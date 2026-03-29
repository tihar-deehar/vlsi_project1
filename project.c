#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "project.h"

/* Strategy:
 * 1. Use static arrays to avoid slow malloc/free calls.
 * 2. Use a Macro for gate evaluation to remove function call overhead.
 * 3. Selective Trace: Only re-simulate gates affected by the fault.
 * 4. Activation Check: Skip propagation if the fault doesn't change the gate output.
 * 5. Incremental Reset: Only clear flags for gates that were actually touched.
 */

static int good_vals[MAX_GATES];
static int faulty_vals[MAX_GATES];
static int affected_list[MAX_GATES]; 
static char is_affected[MAX_GATES]; 

// Inline evaluation for maximum speed
#define EVAL_GATE_FAST(type, a, b, res) { \
    if (type == AND) res = (a == LOGIC_0 || b == LOGIC_0) ? LOGIC_0 : (a == LOGIC_1 && b == LOGIC_1) ? LOGIC_1 : LOGIC_X; \
    else if (type == OR) res = (a == LOGIC_1 || b == LOGIC_1) ? LOGIC_1 : (a == LOGIC_0 && b == LOGIC_0) ? LOGIC_0 : LOGIC_X; \
    else if (type == NAND) { \
        int tmp = (a == LOGIC_0 || b == LOGIC_0) ? LOGIC_0 : (a == LOGIC_1 && b == LOGIC_1) ? LOGIC_1 : LOGIC_X; \
        res = (tmp == LOGIC_0) ? LOGIC_1 : (tmp == LOGIC_1) ? LOGIC_0 : LOGIC_X; \
    } else if (type == NOR) { \
        int tmp = (a == LOGIC_1 || b == LOGIC_1) ? LOGIC_1 : (a == LOGIC_0 && b == LOGIC_0) ? LOGIC_0 : LOGIC_X; \
        res = (tmp == LOGIC_0) ? LOGIC_1 : (tmp == LOGIC_1) ? LOGIC_0 : LOGIC_X; \
    } else if (type == INV) res = (a == LOGIC_0) ? LOGIC_1 : (a == LOGIC_1) ? LOGIC_0 : LOGIC_X; \
    else if (type == BUF || type == PO) res = a; \
    else res = LOGIC_X; \
}

fault_list_t *three_val_fault_simulate(ckt, pat, undetected_flist)
    circuit_t *ckt;
    pattern_t *pat;
    fault_list_t *undetected_flist;
{
    int p, i, g, f_val;
    fault_list_t *prev, *curr, *next;

    for (p = 0; p < pat->len; p++) {
        /* 1. FAULT-FREE SIMULATION */
        for (i = 0; i < ckt->npi; i++) good_vals[ckt->pi[i]] = pat->in[p][i];
        
        for (g = 0; g < ckt->ngates; g++) {
            gate_t *gate = &ckt->gate[g];
            if (gate->type == PI) continue;
            if (gate->type == PO_GND) { good_vals[g] = LOGIC_0; continue; }
            if (gate->type == PO_VCC) { good_vals[g] = LOGIC_1; continue; }
            
            int a = good_vals[gate->fanin[0]];
            int b = (gate->type <= NOR) ? good_vals[gate->fanin[1]] : LOGIC_X;
            EVAL_GATE_FAST(gate->type, a, b, good_vals[g]);
        }

        /* Fill pattern outputs */
        for (i = 0; i < ckt->npo; i++) pat->out[p][i] = good_vals[ckt->po[i]];

        /* 2. SELECTIVE FAULT SIMULATION */
        prev = NULL;
        curr = undetected_flist;
        while (curr != NULL) {
            next = curr->next;
            int g_idx = curr->gate_index;
            f_val = (curr->type == S_A_0) ? LOGIC_0 : LOGIC_1;

            int val_at_fault_site = LOGIC_X;
            int activated = 0;

            // Check if fault is activated
            if (curr->input_index == -1) {
                if (good_vals[g_idx] != f_val) {
                    activated = 1;
                    val_at_fault_site = f_val;
                }
            } else {
                gate_t *f_gate = &ckt->gate[g_idx];
                if (good_vals[f_gate->fanin[curr->input_index]] != f_val) {
                    int a = (curr->input_index == 0) ? f_val : good_vals[f_gate->fanin[0]];
                    int b = (f_gate->type <= NOR) ? ((curr->input_index == 1) ? f_val : good_vals[f_gate->fanin[1]]) : LOGIC_X;
                    EVAL_GATE_FAST(f_gate->type, a, b, val_at_fault_site);
                    // Only activate if the gate output actually changes
                    if (val_at_fault_site != good_vals[g_idx]) activated = 1;
                }
            }

            int detected = 0;
            if (activated) {
                int affected_count = 0;
                faulty_vals[g_idx] = val_at_fault_site;
                is_affected[g_idx] = 1;
                affected_list[affected_count++] = g_idx;

                // Propagate only through the fanout cone
                for (g = g_idx + 1; g < ckt->ngates; g++) {
                    gate_t *gate = &ckt->gate[g];
                    int changed = 0;
                    if (is_affected[gate->fanin[0]]) changed = 1;
                    else if (gate->type <= NOR && is_affected[gate->fanin[1]]) changed = 1;

                    if (changed) {
                        int a = is_affected[gate->fanin[0]] ? faulty_vals[gate->fanin[0]] : good_vals[gate->fanin[0]];
                        int b = (gate->type <= NOR) ? (is_affected[gate->fanin[1]] ? faulty_vals[gate->fanin[1]] : good_vals[gate->fanin[1]]) : LOGIC_X;
                        
                        int new_val;
                        EVAL_GATE_FAST(gate->type, a, b, new_val);
                        if (new_val != good_vals[g]) {
                            faulty_vals[g] = new_val;
                            is_affected[g] = 1;
                            affected_list[affected_count++] = g;
                        }
                    }
                }

                // Check POs for detection
                for (i = 0; i < ckt->npo; i++) {
                    int po_g = ckt->po[i];
                    if (is_affected[po_g] && good_vals[po_g] != LOGIC_X && faulty_vals[po_g] != LOGIC_X) {
                        detected = 1;
                        break;
                    }
                }
                // Cleanup affected flags for the next fault
                for (i = 0; i < affected_count; i++) is_affected[affected_list[i]] = 0;
            }

            if (detected) {
                if (prev == NULL) undetected_flist = next;
                else prev->next = next;
            } else {
                prev = curr;
            }
            curr = next;
        }
        if (undetected_flist == NULL) break;
    }
    return undetected_flist;
}
