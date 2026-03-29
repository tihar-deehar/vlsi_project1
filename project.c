#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "project.h"

/* * Strategy:
 * 1. Pre-allocate static evaluation arrays to avoid malloc/free overhead[cite: 48].
 * 2. Optimized Good Sim: Single pass through levelized gates[cite: 22].
 * 3. Selective Fault Sim: Only re-evaluate gates in the fanout cone of the fault.
 * 4. Activation Check: Skip faults that don't change the gate's local output[cite: 20].
 */

static int good_vals[MAX_GATES];
static int faulty_vals[MAX_GATES];
static char affected[MAX_GATES]; 

static inline int eval_3val(gate_type_t type, int a, int b) {
    switch (type) {
        case AND:  return (a == LOGIC_0 || b == LOGIC_0) ? LOGIC_0 : (a == LOGIC_1 && b == LOGIC_1) ? LOGIC_1 : LOGIC_X;
        case OR:   return (a == LOGIC_1 || b == LOGIC_1) ? LOGIC_1 : (a == LOGIC_0 && b == LOGIC_0) ? LOGIC_0 : LOGIC_X;
        case NAND: {
            int res = (a == LOGIC_0 || b == LOGIC_0) ? LOGIC_0 : (a == LOGIC_1 && b == LOGIC_1) ? LOGIC_1 : LOGIC_X;
            return (res == LOGIC_0) ? LOGIC_1 : (res == LOGIC_1) ? LOGIC_0 : LOGIC_X;
        }
        case NOR: {
            int res = (a == LOGIC_1 || b == LOGIC_1) ? LOGIC_1 : (a == LOGIC_0 && b == LOGIC_0) ? LOGIC_0 : LOGIC_X;
            return (res == LOGIC_0) ? LOGIC_1 : (res == LOGIC_1) ? LOGIC_0 : LOGIC_X;
        }
        case INV:  return (a == LOGIC_0) ? LOGIC_1 : (a == LOGIC_1) ? LOGIC_0 : LOGIC_X;
        case BUF:  return a;
        case PO:   return a;
        default:   return LOGIC_X;
    }
}

fault_list_t *three_val_fault_simulate(ckt, pat, undetected_flist)
    circuit_t *ckt;
    pattern_t *pat;
    fault_list_t *undetected_flist;
{
    int p, i, g, f_val;
    fault_list_t *prev, *curr, *next;

    for (p = 0; p < pat->len; p++) {
        /* 1. Good Simulation [cite: 8] */
        for (i = 0; i < ckt->npi; i++) good_vals[ckt->pi[i]] = pat->in[p][i];
        
        for (g = 0; g < ckt->ngates; g++) {
            gate_t *gate = &ckt->gate[g];
            if (gate->type == PI) continue;
            if (gate->type == PO_GND) { good_vals[g] = LOGIC_0; continue; }
            if (gate->type == PO_VCC) { good_vals[g] = LOGIC_1; continue; }
            
            if (gate->type == AND || gate->type == OR || gate->type == NAND || gate->type == NOR)
                good_vals[g] = eval_3val(gate->type, good_vals[gate->fanin[0]], good_vals[gate->fanin[1]]);
            else
                good_vals[g] = eval_3val(gate->type, good_vals[gate->fanin[0]], LOGIC_X);
        }

        /* Store output patterns  */
        for (i = 0; i < ckt->npo; i++) pat->out[p][i] = good_vals[ckt->po[i]];

        /* 2. Fault Simulation [cite: 11, 12] */
        prev = NULL;
        curr = undetected_flist;
        while (curr != NULL) {
            next = curr->next;
            int g_idx = curr->gate_index;
            f_val = (curr->type == S_A_0) ? LOGIC_0 : LOGIC_1;

            int activated = 0;
            int val_at_fault_site = LOGIC_X;

            if (curr->input_index == -1) {
                if (good_vals[g_idx] != f_val) {
                    activated = 1;
                    val_at_fault_site = f_val;
                }
            } else {
                gate_t *f_gate = &ckt->gate[g_idx];
                if (good_vals[f_gate->fanin[curr->input_index]] != f_val) {
                    activated = 1;
                    int a = (curr->input_index == 0) ? f_val : good_vals[f_gate->fanin[0]];
                    int b = (f_gate->type == AND || f_gate->type == OR || f_gate->type == NAND || f_gate->type == NOR) ? 
                            ((curr->input_index == 1) ? f_val : good_vals[f_gate->fanin[1]]) : LOGIC_X;
                    val_at_fault_site = eval_3val(f_gate->type, a, b);
                }
            }

            int detected = 0;
            if (activated && val_at_fault_site != good_vals[g_idx]) {
                faulty_vals[g_idx] = val_at_fault_site;
                affected[g_idx] = 1;

                /* Selective Trace propagation [cite: 22] */
                for (g = g_idx + 1; g < ckt->ngates; g++) {
                    gate_t *gate = &ckt->gate[g];
                    affected[g] = 0; 
                    
                    int fanin_changed = 0;
                    if (affected[gate->fanin[0]]) fanin_changed = 1;
                    else if ((gate->type == AND || gate->type == OR || gate->type == NAND || gate->type == NOR) && affected[gate->fanin[1]]) 
                        fanin_changed = 1;

                    if (fanin_changed) {
                        int a = affected[gate->fanin[0]] ? faulty_vals[gate->fanin[0]] : good_vals[gate->fanin[0]];
                        int b = (gate->type == AND || gate->type == OR || gate->type == NAND || gate->type == NOR) ? 
                                (affected[gate->fanin[1]] ? faulty_vals[gate->fanin[1]] : good_vals[gate->fanin[1]]) : LOGIC_X;
                        
                        int new_val = eval_3val(gate->type, a, b);
                        if (new_val != good_vals[g]) {
                            faulty_vals[g] = new_val;
                            affected[g] = 1;
                        }
                    }
                }

                /* Check Primary Outputs  */
                for (i = 0; i < ckt->npo; i++) {
                    int po_g = ckt->po[i];
                    if (affected[po_g] && good_vals[po_g] != LOGIC_X && faulty_vals[po_g] != LOGIC_X) {
                        detected = 1;
                        break;
                    }
                }
                /* Reset affected flags for next fault simulation pass */
                for (g = g_idx; g < ckt->ngates; g++) affected[g] = 0;
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