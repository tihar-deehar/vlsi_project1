#include <stddef.h>
#include "project.h"

/*************************************************************************

Function:  three_val_transition_fault_simulate

Purpose:  This function performs transition fault simulation on 3-valued
          input patterns.

pat.out[][] is filled with the fault-free output patterns corresponding to
the input patterns in pat.in[][].

Return:  List of faults that remain undetected.

*************************************************************************/
static inline int inv3(int a) {
    if (a == LOGIC_0) return LOGIC_1;
    if (a == LOGIC_1) return LOGIC_0;
    return LOGIC_X;
}

static inline int and3(int a, int b) {
    if (a == LOGIC_0 || b == LOGIC_0) return LOGIC_0;
    if (a == LOGIC_1 && b == LOGIC_1) return LOGIC_1;
    return LOGIC_X;
}

static inline int or3(int a, int b) {
    if (a == LOGIC_1 || b == LOGIC_1) return LOGIC_1;
    if (a == LOGIC_0 && b == LOGIC_0) return LOGIC_0;
    return LOGIC_X;
}

static inline int stuck_to_logic(stuck_val_t type) {
    return (type == S_A_0) ? LOGIC_0 : LOGIC_1;
}

static inline int eval_gate(gate_type_t type, int a, int b) {
    switch (type) {
        case AND:  return and3(a, b);
        case NAND: return inv3(and3(a, b));
        case OR:   return or3(a, b);
        case NOR:  return inv3(or3(a, b));
        case INV:  return inv3(a);
        case BUF:  return a;
        default:   return UNDEFINED;
    }
}

static void simulate_good(circuit_t *ckt, int *input_pat, int *values) {
    int i, g, a, b;
    gate_t *gate;

    for (i = 0; i < ckt->ngates; i++) {
        values[i] = UNDEFINED;
    }

    for (i = 0; i < ckt->npi; i++) {
        values[ckt->pi[i]] = input_pat[i];
    }

    for (g = 0; g < ckt->ngates; g++) {
        gate = &ckt->gate[g];

        switch (gate->type) {
            case PI:
                break;

            case PO_GND:
                values[g] = LOGIC_0;
                break;

            case PO_VCC:
                values[g] = LOGIC_1;
                break;

            case INV:
            case BUF:
            case PO:
                a = values[gate->fanin[0]];
                if (gate->type == PO) values[g] = a;
                else values[g] = eval_gate(gate->type, a, LOGIC_X);
                break;

            case AND:
            case OR:
            case NAND:
            case NOR:
                a = values[gate->fanin[0]];
                b = values[gate->fanin[1]];
                values[g] = eval_gate(gate->type, a, b);
                break;

            default:
                break;
        }
    }
}

static void simulate_faulty(circuit_t *ckt, int *input_pat, int *values, fault_list_t *fault) {
    int i, g, a, b, fault_val;
    gate_t *gate;

    fault_val = stuck_to_logic(fault->type);

    for (i = 0; i < ckt->ngates; i++) {
        values[i] = UNDEFINED;
    }

    for (i = 0; i < ckt->npi; i++) {
        values[ckt->pi[i]] = input_pat[i];
    }

    for (g = 0; g < ckt->ngates; g++) {
        gate = &ckt->gate[g];

        switch (gate->type) {
            case PI:
              if (g == fault->gate_index && fault->input_index == -1) {
                values[g] = fault_val;
              }
              break;

            case PO_GND:
                values[g] = LOGIC_0;
                break;

            case PO_VCC:
                values[g] = LOGIC_1;
                break;

            case INV:
            case BUF:
            case PO:
                a = values[gate->fanin[0]];

                if (g == fault->gate_index && fault->input_index == 0) {
                    a = fault_val;
                }

                if (gate->type == PO) values[g] = a;
                else values[g] = eval_gate(gate->type, a, LOGIC_X);

                if (g == fault->gate_index && fault->input_index == -1) {
                    values[g] = fault_val;
                }
                break;

            case AND:
            case OR:
            case NAND:
            case NOR:
                a = values[gate->fanin[0]];
                b = values[gate->fanin[1]];

                if (g == fault->gate_index) {
                    if (fault->input_index == 0) a = fault_val;
                    if (fault->input_index == 1) b = fault_val;
                }

                values[g] = eval_gate(gate->type, a, b);

                if (g == fault->gate_index && fault->input_index == -1) {
                    values[g] = fault_val;
                }
                break;

            default:
                break;
        }
    }
}

fault_list_t *three_val_fault_simulate(ckt,pat,undetected_flist)
     circuit_t *ckt;
     pattern_t *pat;
     fault_list_t *undetected_flist;
{
    int good_values[MAX_GATES];
    int bad_values[MAX_GATES];
    int p, j, detected;
    fault_list_t *prev, *curr, *next;

    for (p = 0; p < pat->len; p++) {
        simulate_good(ckt, pat->in[p], good_values);

        for (j = 0; j < ckt->npo; j++) {
            pat->out[p][j] = good_values[ckt->po[j]];
        }
    }

    prev = NULL;
    curr = undetected_flist;

    while (curr != NULL) {
        detected = FALSE;

        for (p = 0; p < pat->len && !detected; p++) {
            simulate_faulty(ckt, pat->in[p], bad_values, curr);

            for (j = 0; j < ckt->npo; j++) {
                int good = pat->out[p][j];
                int bad  = bad_values[ckt->po[j]];

                if (good != LOGIC_X && bad != LOGIC_X && good != bad) {
                    detected = TRUE;
                    break;
                }
            }
        }

        next = curr->next;

        if (detected) {
            if (prev == NULL) undetected_flist = next;
            else prev->next = next;
        } else {
            prev = curr;
        }

        curr = next;
    }

    return(undetected_flist);
}
