/*
 * project.c — 3-Valued Bit-Parallel Fault Simulator
 *
 * Strategy:
 * ---------
 * 1. BIT-PARALLEL GOOD SIMULATION (64 patterns at once using uint64_t)
 *    3-value logic encoded as two bit-vectors per gate:
 *      LOGIC 0: V1=0, V0=1
 *      LOGIC 1: V1=1, V0=0
 *      LOGIC X: V1=0, V0=0
 *
 * 2. PRECOMPUTED FANOUT CONES
 *    Before simulation, for each gate g we build cone[g]: the sorted
 *    (topological order) list of all gates reachable from g via fanout.
 *    Fault propagation then only visits cone[g] instead of scanning every
 *    gate after g_idx, cutting propagation cost dramatically on large circuits.
 *    A flat memory pool (cone_pool) avoids per-gate malloc.
 *
 * 3. GENERATION-COUNTER VISITED TRACKING
 *    Instead of clearing an is_aff[] byte array after each fault (O(cone size)),
 *    we use a uint64_t generation counter (aff_gen[]). A gate is "affected" iff
 *    aff_gen[g] == cur_gen. No clearing loop needed.
 *
 * 4. reaches_po[] EARLY-SKIP
 *    Precomputed boolean: does this gate have any path to a primary output?
 *    Faults at gates that cannot reach any PO are skipped immediately.
 *
 * 5. SELECTIVE FAULT SIMULATION
 *    Only propagate a fault if f_mask (patterns where fault changes gate output)
 *    is non-zero. Detected faults are spliced out of the linked list in-place.
 */

#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "project.h"

/* --------------------------------------------------------------------------
 * 3-Value Bit-Parallel Gate Macros
 * -------------------------------------------------------------------------- */
#define BP_AND(a1,a0,b1,b0,r1,r0) { (r1)=(a1)&(b1); (r0)=(a0)|(b0); }
#define BP_OR(a1,a0,b1,b0,r1,r0)  { (r1)=(a1)|(b1); (r0)=(a0)&(b0); }
#define BP_INV(a1,a0,r1,r0)       { (r1)=(a0);       (r0)=(a1);       }

/* --------------------------------------------------------------------------
 * Static storage
 * -------------------------------------------------------------------------- */

static uint64_t g_v1[MAX_GATES], g_v0[MAX_GATES]; /* good simulation */
static uint64_t f_v1[MAX_GATES], f_v0[MAX_GATES]; /* faulty simulation */
static uint64_t aff_gen[MAX_GATES];               /* generation counter */

/* Fanout cone pool — increase multiplier if pool is exhausted */
#define CONE_POOL_SIZE (MAX_GATES * 48)
static int  cone_pool[CONE_POOL_SIZE];
static int *cone[MAX_GATES];
static int  cone_size[MAX_GATES];

static char reaches_po[MAX_GATES];

/* Scratch buffers used only during build_fanout_cones */
#define FANOUT_POOL_SIZE (MAX_GATES * 6)
static int  fanout_pool[FANOUT_POOL_SIZE];
static int *fanout[MAX_GATES];
static int  fanout_cnt[MAX_GATES];
static char in_cone[MAX_GATES];
static int  bfs_queue[MAX_GATES];

/* --------------------------------------------------------------------------
 * eval_gate — inline 3-valued gate evaluation
 * -------------------------------------------------------------------------- */
static inline void eval_gate(gate_t *gt,
                              uint64_t a1, uint64_t a0,
                              uint64_t b1, uint64_t b0,
                              uint64_t *r1, uint64_t *r0)
{
    uint64_t t1, t0;
    switch (gt->type) {
        case AND:  BP_AND(a1,a0,b1,b0,*r1,*r0); break;
        case OR:   BP_OR (a1,a0,b1,b0,*r1,*r0); break;
        case NAND: BP_AND(a1,a0,b1,b0,t1,t0); BP_INV(t1,t0,*r1,*r0); break;
        case NOR:  BP_OR (a1,a0,b1,b0,t1,t0); BP_INV(t1,t0,*r1,*r0); break;
        case INV:  BP_INV(a1,a0,*r1,*r0); break;
        default:   *r1=a1; *r0=a0; break; /* BUF, PO */
    }
}

/* --------------------------------------------------------------------------
 * build_fanout_cones — called once before simulation begins
 * -------------------------------------------------------------------------- */
static void build_fanout_cones(circuit_t *ckt)
{
    int g, i, fp = 0;

    /* 1. Build forward fanout lists */
    memset(fanout_cnt, 0, sizeof(int) * ckt->ngates);
    for (g = 0; g < ckt->ngates; g++) {
        gate_t *gt = &ckt->gate[g];
        if (gt->type == PI || gt->type == PO_GND || gt->type == PO_VCC) continue;
        fanout_cnt[gt->fanin[0]]++;
        if (gt->type <= NOR) fanout_cnt[gt->fanin[1]]++;
    }
    for (g = 0; g < ckt->ngates; g++) {
        fanout[g] = &fanout_pool[fp];
        fp += fanout_cnt[g];
        fanout_cnt[g] = 0;
    }
    for (g = 0; g < ckt->ngates; g++) {
        gate_t *gt = &ckt->gate[g];
        if (gt->type == PI || gt->type == PO_GND || gt->type == PO_VCC) continue;
        int fi0 = gt->fanin[0];
        fanout[fi0][fanout_cnt[fi0]++] = g;
        if (gt->type <= NOR) {
            int fi1 = gt->fanin[1];
            fanout[fi1][fanout_cnt[fi1]++] = g;
        }
    }

    /* 2. Back-propagate reaches_po (gates are in topo order) */
    memset(reaches_po, 0, ckt->ngates);
    for (i = 0; i < ckt->npo; i++) reaches_po[ckt->po[i]] = 1;
    for (g = ckt->ngates - 1; g >= 0; g--) {
        if (!reaches_po[g]) continue;
        gate_t *gt = &ckt->gate[g];
        if (gt->type == PI || gt->type == PO_GND || gt->type == PO_VCC) continue;
        reaches_po[gt->fanin[0]] = 1;
        if (gt->type <= NOR) reaches_po[gt->fanin[1]] = 1;
    }

    /* 3. Build cone[g] via BFS over fanout, stored in topo order */
    memset(in_cone, 0, ckt->ngates);
    int pool_ptr = 0;

    for (g = 0; g < ckt->ngates; g++) {
        if (!reaches_po[g]) { cone[g] = NULL; cone_size[g] = 0; continue; }

        cone[g] = &cone_pool[pool_ptr];

        int head = 0, tail = 0;
        bfs_queue[tail++] = g;
        in_cone[g] = 1;

        while (head < tail) {
            int cur = bfs_queue[head++];
            for (i = 0; i < fanout_cnt[cur]; i++) {
                int fo = fanout[cur][i];
                if (!in_cone[fo]) { in_cone[fo] = 1; bfs_queue[tail++] = fo; }
            }
        }

        /* Insertion sort into topo order (gate index = topo index) */
        for (i = 1; i < tail; i++) {
            int key = bfs_queue[i], j = i - 1;
            while (j >= 0 && bfs_queue[j] > key) { bfs_queue[j+1] = bfs_queue[j]; j--; }
            bfs_queue[j+1] = key;
        }

        /* Copy to pool, skipping g itself */
        int sz = 0;
        for (i = 0; i < tail; i++) {
            int node = bfs_queue[i];
            in_cone[node] = 0;
            if (node != g) cone_pool[pool_ptr + sz++] = node;
        }
        cone_size[g] = sz;
        pool_ptr += sz;
    }
}

/* --------------------------------------------------------------------------
 * three_val_fault_simulate
 * -------------------------------------------------------------------------- */
fault_list_t *three_val_fault_simulate(ckt, pat, undetected_flist)
    circuit_t    *ckt;
    pattern_t    *pat;
    fault_list_t *undetected_flist;
{
    int p, i, g, w;
    fault_list_t *prev, *curr, *next;
    static uint64_t cur_gen = 0;
    static int cones_built = 0;

    if (!cones_built) {
        build_fanout_cones(ckt);
        memset(aff_gen, 0, sizeof(uint64_t) * ckt->ngates);
        cones_built = 1;
    }

    for (p = 0; p < pat->len; p += 64) {
        int      b_size = (pat->len - p < 64) ? (pat->len - p) : 64;
        uint64_t b_mask = (b_size == 64) ? ~0ULL : ((1ULL << b_size) - 1);

        /* ------------------------------------------------------------------
         * 1. Good simulation
         * ------------------------------------------------------------------ */
        for (i = 0; i < ckt->npi; i++) {
            uint64_t v1 = 0, v0 = 0;
            int pi_g = ckt->pi[i];
            for (w = 0; w < b_size; w++) {
                int val = pat->in[p + w][i];
                if      (val == LOGIC_1) v1 |= (1ULL << w);
                else if (val == LOGIC_0) v0 |= (1ULL << w);
            }
            g_v1[pi_g] = v1; g_v0[pi_g] = v0;
        }

        for (g = 0; g < ckt->ngates; g++) {
            gate_t *gt = &ckt->gate[g];
            if (gt->type == PI)     continue;
            if (gt->type == PO_GND) { g_v1[g] = 0;     g_v0[g] = b_mask; continue; }
            if (gt->type == PO_VCC) { g_v1[g] = b_mask; g_v0[g] = 0;     continue; }
            uint64_t a1 = g_v1[gt->fanin[0]], a0 = g_v0[gt->fanin[0]];
            uint64_t b1 = 0, b0 = 0;
            if (gt->type <= NOR) { b1 = g_v1[gt->fanin[1]]; b0 = g_v0[gt->fanin[1]]; }
            eval_gate(gt, a1, a0, b1, b0, &g_v1[g], &g_v0[g]);
        }

        /* Store fault-free outputs */
        for (w = 0; w < b_size; w++) {
            for (i = 0; i < ckt->npo; i++) {
                int po_g = ckt->po[i];
                if      (g_v1[po_g] & (1ULL << w)) pat->out[p+w][i] = LOGIC_1;
                else if (g_v0[po_g] & (1ULL << w)) pat->out[p+w][i] = LOGIC_0;
                else                                pat->out[p+w][i] = LOGIC_X;
            }
        }

        /* ------------------------------------------------------------------
         * 2. Selective fault simulation
         * ------------------------------------------------------------------ */
        prev = NULL;
        curr = undetected_flist;

        while (curr != NULL) {
            next = curr->next;
            int g_idx = curr->gate_index;

            if (!reaches_po[g_idx]) { prev = curr; curr = next; continue; }

            /* Compute faulty value at fault site */
            uint64_t f_site_v1, f_site_v0;

            if (curr->input_index == -1) {
                f_site_v1 = (curr->type == S_A_1) ? b_mask : 0;
                f_site_v0 = (curr->type == S_A_0) ? b_mask : 0;
            } else {
                gate_t *fg = &ckt->gate[g_idx];
                uint64_t a1, a0, b1 = 0, b0 = 0;
                if (curr->input_index == 0) {
                    a1 = (curr->type == S_A_1) ? b_mask : 0;
                    a0 = (curr->type == S_A_0) ? b_mask : 0;
                } else {
                    a1 = g_v1[fg->fanin[0]]; a0 = g_v0[fg->fanin[0]];
                }
                if (fg->type <= NOR) {
                    if (curr->input_index == 1) {
                        b1 = (curr->type == S_A_1) ? b_mask : 0;
                        b0 = (curr->type == S_A_0) ? b_mask : 0;
                    } else {
                        b1 = g_v1[fg->fanin[1]]; b0 = g_v0[fg->fanin[1]];
                    }
                }
                eval_gate(fg, a1, a0, b1, b0, &f_site_v1, &f_site_v0);
            }

            uint64_t f_mask = ((f_site_v1 ^ g_v1[g_idx]) |
                               (f_site_v0 ^ g_v0[g_idx])) & b_mask;

            int detected = 0;

            if (f_mask) {
                /* Propagate through precomputed fanout cone */
                cur_gen++;
                f_v1[g_idx] = f_site_v1;
                f_v0[g_idx] = f_site_v0;
                aff_gen[g_idx] = cur_gen;

                int *cone_g = cone[g_idx];
                int  cone_n = cone_size[g_idx];

                for (int ci = 0; ci < cone_n; ci++) {
                    int gc = cone_g[ci];
                    gate_t *gt = &ckt->gate[gc];
                    int aff0 = (aff_gen[gt->fanin[0]] == cur_gen);
                    int aff1 = (gt->type <= NOR) && (aff_gen[gt->fanin[1]] == cur_gen);
                    if (!aff0 && !aff1) continue;

                    uint64_t a1 = aff0 ? f_v1[gt->fanin[0]] : g_v1[gt->fanin[0]];
                    uint64_t a0 = aff0 ? f_v0[gt->fanin[0]] : g_v0[gt->fanin[0]];
                    uint64_t b1 = 0, b0 = 0;
                    if (gt->type <= NOR) {
                        b1 = aff1 ? f_v1[gt->fanin[1]] : g_v1[gt->fanin[1]];
                        b0 = aff1 ? f_v0[gt->fanin[1]] : g_v0[gt->fanin[1]];
                    }
                    uint64_t res1, res0;
                    eval_gate(gt, a1, a0, b1, b0, &res1, &res0);

                    if (((res1 ^ g_v1[gc]) | (res0 ^ g_v0[gc])) & b_mask) {
                        f_v1[gc] = res1; f_v0[gc] = res0;
                        aff_gen[gc] = cur_gen;
                    }
                }

                /* Check observability at POs */
                uint64_t detect_mask = 0;
                for (i = 0; i < ckt->npo; i++) {
                    int po_g = ckt->po[i];
                    if (aff_gen[po_g] == cur_gen)
                        detect_mask |= (g_v1[po_g] & f_v0[po_g])
                                     | (g_v0[po_g] & f_v1[po_g]);
                }
                if (detect_mask & b_mask) detected = 1;
            }

            if (detected) {
                if (prev == NULL) undetected_flist = next;
                else              prev->next = next;
                /* Do NOT free curr — support code frees it */
            } else {
                prev = curr;
            }
            curr = next;
        }

        if (undetected_flist == NULL) break;
    }

    return undetected_flist;
}