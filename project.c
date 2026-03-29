#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "project.h"

/* * 3-Value Bit-Parallel Encoding:
 * LOGIC 0: V1=0, V0=1
 * LOGIC 1: V1=1, V0=0
 * LOGIC X: V1=0, V0=0
 */

static uint64_t g_v1[MAX_GATES], g_v0[MAX_GATES]; // Good values
static uint64_t f_v1[MAX_GATES], f_v0[MAX_GATES]; // Faulty values
static int aff_list[MAX_GATES];
static char is_aff[MAX_GATES];

// Bit-Parallel 3-Valued Gate Macros
#define BP_AND(a1, a0, b1, b0, r1, r0) { r1 = (a1 & b1); r0 = (a0 | b0); }
#define BP_OR(a1, a0, b1, b0, r1, r0)  { r1 = (a1 | b1); r0 = (a0 & b0); }
#define BP_INV(a1, a0, r1, r0)         { r1 = a0; r0 = a1; }

fault_list_t *three_val_fault_simulate(ckt, pat, undetected_flist)
    circuit_t *ckt;
    pattern_t *pat;
    fault_list_t *undetected_flist;
{
    int p, i, g, w;
    fault_list_t *prev, *curr, *next;

    for (p = 0; p < pat->len; p += 64) {
        int b_size = (pat->len - p < 64) ? (pat->len - p) : 64;
        uint64_t b_mask = (b_size == 64) ? ~0ULL : (1ULL << b_size) - 1;

        // 1. BIT-PARALLEL GOOD SIMULATION
        for (i = 0; i < ckt->npi; i++) {
            uint64_t v1 = 0, v0 = 0;
            int pi_g = ckt->pi[i];
            for (w = 0; w < b_size; w++) {
                if (pat->in[p + w][i] == LOGIC_1) v1 |= (1ULL << w);
                else if (pat->in[p + w][i] == LOGIC_0) v0 |= (1ULL << w);
            }
            g_v1[pi_g] = v1; g_v0[pi_g] = v0;
        }

        for (g = 0; g < ckt->ngates; g++) {
            gate_t *gt = &ckt->gate[g];
            if (gt->type == PI) continue;
            if (gt->type == PO_GND) { g_v1[g] = 0; g_v0[g] = b_mask; continue; }
            if (gt->type == PO_VCC) { g_v1[g] = b_mask; g_v0[g] = 0; continue; }

            uint64_t a1 = g_v1[gt->fanin[0]], a0 = g_v0[gt->fanin[0]];
            if (gt->type <= NOR) { // 2-input gates AND, OR, NAND, NOR
                uint64_t b1 = g_v1[gt->fanin[1]], b0 = g_v0[gt->fanin[1]];
                if (gt->type == AND) { BP_AND(a1, a0, b1, b0, g_v1[g], g_v0[g]); }
                else if (gt->type == OR) { BP_OR(a1, a0, b1, b0, g_v1[g], g_v0[g]); }
                else if (gt->type == NAND) { uint64_t t1, t0; BP_AND(a1, a0, b1, b0, t1, t0); BP_INV(t1, t0, g_v1[g], g_v0[g]); }
                else { uint64_t t1, t0; BP_OR(a1, a0, b1, b0, t1, t0); BP_INV(t1, t0, g_v1[g], g_v0[g]); }
            } else {
                if (gt->type == INV) { BP_INV(a1, a0, g_v1[g], g_v0[g]); }
                else { g_v1[g] = a1; g_v0[g] = a0; }
            }
        }

        // Store outputs for the test script
        for (w = 0; w < b_size; w++) {
            for (i = 0; i < ckt->npo; i++) {
                int po_g = ckt->po[i];
                if (g_v1[po_g] & (1ULL << w)) pat->out[p+w][i] = LOGIC_1;
                else if (g_v0[po_g] & (1ULL << w)) pat->out[p+w][i] = LOGIC_0;
                else pat->out[p+w][i] = LOGIC_X;
            }
        }

        // 2. BIT-PARALLEL SELECTIVE FAULT SIMULATION
        prev = NULL;
        curr = undetected_flist;
        while (curr != NULL) {
            next = curr->next;
            int g_idx = curr->gate_index;
            uint64_t f_mask = 0; // patterns where fault is activated AND changes gate output
            uint64_t f_site_v1, f_site_v0;

            if (curr->input_index == -1) {
                f_site_v1 = (curr->type == S_A_1) ? b_mask : 0;
                f_site_v0 = (curr->type == S_A_0) ? b_mask : 0;
                f_mask = (f_site_v1 ^ g_v1[g_idx]) | (f_site_v0 ^ g_v0[g_idx]);
            } else {
                gate_t *fg = &ckt->gate[g_idx];
                uint64_t a1 = (curr->input_index == 0) ? ((curr->type == S_A_1) ? b_mask : 0) : g_v1[fg->fanin[0]];
                uint64_t a0 = (curr->input_index == 0) ? ((curr->type == S_A_0) ? b_mask : 0) : g_v0[fg->fanin[0]];
                if (fg->type <= NOR) {
                    uint64_t b1 = (curr->input_index == 1) ? ((curr->type == S_A_1) ? b_mask : 0) : g_v1[fg->fanin[1]];
                    uint64_t b0 = (curr->input_index == 1) ? ((curr->type == S_A_0) ? b_mask : 0) : g_v0[fg->fanin[1]];
                    if (fg->type == AND) { BP_AND(a1, a0, b1, b0, f_site_v1, f_site_v0); }
                    else if (fg->type == OR) { BP_OR(a1, a0, b1, b0, f_site_v1, f_site_v0); }
                    else if (fg->type == NAND) { uint64_t t1, t0; BP_AND(a1, a0, b1, b0, t1, t0); BP_INV(t1, t0, f_site_v1, f_site_v0); }
                    else { uint64_t t1, t0; BP_OR(a1, a0, b1, b0, t1, t0); BP_INV(t1, t0, f_site_v1, f_site_v0); }
                } else {
                    if (fg->type == INV) { BP_INV(a1, a0, f_site_v1, f_site_v0); }
                    else { f_site_v1 = a1; f_site_v0 = a0; }
                }
                f_mask = (f_site_v1 ^ g_v1[g_idx]) | (f_site_v0 ^ g_v0[g_idx]);
            }

            int detected = 0;
            if (f_mask & b_mask) {
                int aff_cnt = 0;
                f_v1[g_idx] = f_site_v1; f_v0[g_idx] = f_site_v0;
                is_aff[g_idx] = 1; aff_list[aff_cnt++] = g_idx;

                for (g = g_idx + 1; g < ckt->ngates; g++) {
                    gate_t *gt = &ckt->gate[g];
                    if (is_aff[gt->fanin[0]] || (gt->type <= NOR && is_aff[gt->fanin[1]])) {
                        uint64_t a1 = is_aff[gt->fanin[0]] ? f_v1[gt->fanin[0]] : g_v1[gt->fanin[0]];
                        uint64_t a0 = is_aff[gt->fanin[0]] ? f_v0[gt->fanin[0]] : g_v0[gt->fanin[0]];
                        uint64_t res1, res0;
                        if (gt->type <= NOR) {
                            uint64_t b1 = is_aff[gt->fanin[1]] ? f_v1[gt->fanin[1]] : g_v1[gt->fanin[1]];
                            uint64_t b0 = is_aff[gt->fanin[1]] ? f_v0[gt->fanin[1]] : g_v0[gt->fanin[1]];
                            if (gt->type == AND) { BP_AND(a1, a0, b1, b0, res1, res0); }
                            else if (gt->type == OR) { BP_OR(a1, a0, b1, b0, res1, res0); }
                            else if (gt->type == NAND) { uint64_t t1, t0; BP_AND(a1, a0, b1, b0, t1, t0); BP_INV(t1, t0, res1, res0); }
                            else { uint64_t t1, t0; BP_OR(a1, a0, b1, b0, t1, t0); BP_INV(t1, t0, res1, res0); }
                        } else {
                            if (gt->type == INV) { BP_INV(a1, a0, res1, res0); }
                            else { res1 = a1; res0 = a0; }
                        }
                        if (((res1 ^ g_v1[g]) | (res0 ^ g_v0[g])) & b_mask) {
                            f_v1[g] = res1; f_v0[g] = res0;
                            is_aff[g] = 1; aff_list[aff_cnt++] = g;
                        }
                    }
                }

                uint64_t detect_mask = 0;
                for (i = 0; i < ckt->npo; i++) {
                    int po_g = ckt->po[i];
                    if (is_aff[po_g]) {
                        // Detected if (Good is 1 AND Faulty is 0) OR (Good is 0 AND Faulty is 1)
                        detect_mask |= (g_v1[po_g] & f_v0[po_g]) | (g_v0[po_g] & f_v1[po_g]);
                    }
                }
                if (detect_mask & b_mask) detected = 1;
                for (i = 0; i < aff_cnt; i++) is_aff[aff_list[i]] = 0;
            }

            if (detected) {
                if (prev == NULL) undetected_flist = next;
                else prev->next = next;
            } else prev = curr;
            curr = next;
        }
        if (undetected_flist == NULL) break;
    }
    return undetected_flist;
}