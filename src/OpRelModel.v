(* This file was automatically extracted by prepare_release script. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETable.
Require MTable.
Require Import Bool.

Notation is_i32_cell := op_rel_is_i32.
Notation is_sign_cell := op_rel_is_sign.

Notation lhs_u16_cells_le0 := op_rel_lhs_u16_le0.
Notation lhs_u16_cells_le1:= op_rel_lhs_u16_le1.
Notation lhs_u16_cells_le2 := op_rel_lhs_u16_le2.
Notation lhs_u16_cells_le3 := op_rel_lhs_u16_le3.
Notation lhs_u64_cell := op_rel_lhs_u64.
Notation lhs_flag_bit_cell := op_rel_lhs_flag_bit.
Notation lhs_flag_rem_cell := op_rel_lhs_flag_rem.
Notation lhs_flag_rem_diff_cell := op_rel_lhs_flag_rem_diff.

Notation rhs_u16_cells_le0 := op_rel_rhs_u16_le0.
Notation rhs_u16_cells_le1 := op_rel_rhs_u16_le1.
Notation rhs_u16_cells_le2 := op_rel_rhs_u16_le2.
Notation rhs_u16_cells_le3 := op_rel_rhs_u16_le3.
Notation rhs_u64_cell := op_rel_rhs_u64.
Notation rhs_flag_bit_cell := op_rel_rhs_flag_bit.
Notation rhs_flag_rem_cell := op_rel_rhs_flag_rem.
Notation rhs_flag_rem_diff_cell := op_rel_rhs_flag_rem_diff.

Notation diff_u16_cells_le0 := op_rel_diff_u16_le0.
Notation diff_u16_cells_le1 := op_rel_diff_u16_le1.
Notation diff_u16_cells_le2 := op_rel_diff_u16_le2.
Notation diff_u16_cells_le3 := op_rel_diff_u16_le3.
Notation diff_u64_cell := op_rel_diff_u64.

Notation diff_inv_cell := op_rel_diff_inv.
Notation res_is_eq_cell := op_rel_res_is_eq.
Notation res_is_lt_cell := op_rel_res_is_lt.
Notation res_is_gt_cell := op_rel_res_is_gt.

Notation op_is_eq_cell := op_rel_op_is_eq.
Notation op_is_ne_cell := op_rel_op_is_ne.
Notation op_is_lt_cell := op_rel_op_is_lt.
Notation op_is_gt_cell :=op_rel_op_is_gt.
Notation op_is_le_cell := op_rel_op_is_le.
Notation op_is_ge_cell := op_rel_op_is_ge.

Notation l_pos_r_pos_cell := op_rel_l_pos_r_pos. 
Notation l_pos_r_neg_cell := op_rel_l_pos_r_neg.
Notation l_neg_r_pos_cell := op_rel_l_neg_r_pos.
Notation l_neg_r_neg_cell := op_rel_l_neg_r_neg.

Notation memory_table_lookup_stack_read_rhs := op_rel_memory_table_lookup_stack_read_rhs.
Notation memory_table_lookup_stack_read_lhs := op_rel_memory_table_lookup_stack_read_lhs.
Notation memory_table_lookup_stack_write := op_rel_memory_table_lookup_stack_write.

(* isbit, is16, iscommon, is64 from etable *)
Axiom is_i32_bit: isbit is_i32_cell.
Axiom is_sign_bit: isbit is_sign_cell.

Axiom lhs_u16_cells_le0_u16: is16 lhs_u16_cells_le0.
Axiom lhs_u16_cells_le1_u16: is16 lhs_u16_cells_le1.
Axiom lhs_u16_cells_le2_u16: is16 lhs_u16_cells_le2.
Axiom lhs_u16_cells_le3_u16: is16 lhs_u16_cells_le3.

 (* u64 cells with flag bit dyn sign *)
Axiom lhs_u64: is64_from16
    lhs_u64_cell
    lhs_u16_cells_le0
    lhs_u16_cells_le1
    lhs_u16_cells_le2
    lhs_u16_cells_le3.

Axiom lhs_u64_flag_bit_dyn_sign:
    gate etable
    (fun get =>
        (get (ops_cell Rel) 0) * 
            ((get is_sign_cell 0) 
                * (get lhs_flag_bit_cell 0) * (Z.shiftl 1 15)
                + (get lhs_flag_rem_cell 0)
                - (get lhs_u16_cells_le3 0 +
                (get is_i32_cell 0) * (get lhs_u16_cells_le1 0 - get lhs_u16_cells_le3 0)))
        :: (get (ops_cell Rel) 0) * 
                ((get is_sign_cell 0) 
                * (get lhs_flag_rem_cell 0 + get lhs_flag_rem_diff_cell 0 - ((Z.shiftl 1 15) -1)))
        :: (get (ops_cell Rel) 0) * 
            ((get is_sign_cell 0 - 1) * (get lhs_flag_bit_cell 0))
        ::nil). 

Axiom lhs_flag_bit: isbit lhs_flag_bit_cell.
Axiom lhs_flag_rem_common: iscommon lhs_flag_rem_cell.
Axiom lhs_flag_rem_diff_common: iscommon lhs_flag_rem_diff_cell.

Axiom rhs_u16_cells_le0_u16: is16 rhs_u16_cells_le0.
Axiom rhs_u16_cells_le1_u16: is16 rhs_u16_cells_le1.
Axiom rhs_u16_cells_le2_u16: is16 rhs_u16_cells_le2.
Axiom rhs_u16_cells_le3_u16: is16 rhs_u16_cells_le3.

(* u64 cells with flag bit dyn sign *)
Axiom rhs_u64: is64_from16
    rhs_u64_cell
    rhs_u16_cells_le0 
    rhs_u16_cells_le1
    rhs_u16_cells_le2
    rhs_u16_cells_le3.

Axiom rhs_u64_flag_bit_dyn_sign:
    gate etable
    (fun get =>
    (get (ops_cell Rel) 0) * 
        ((get is_sign_cell 0) 
            * (get rhs_flag_bit_cell 0) * (Z.shiftl 1 15)
            + (get rhs_flag_rem_cell 0)
            - (get rhs_u16_cells_le3 0 +
               (get is_i32_cell 0) * (get rhs_u16_cells_le1 0 - get rhs_u16_cells_le3 0)))
        :: (get (ops_cell Rel) 0) * 
            ((get is_sign_cell 0) 
                * (get rhs_flag_rem_cell 0 + get rhs_flag_rem_diff_cell 0 - ((Z.shiftl 1 15) -1)))
        ::(get (ops_cell Rel) 0) * 
            ((get is_sign_cell 0 - 1) * (get rhs_flag_bit_cell 0))
        ::nil). 

Axiom rhs_flag_bit: isbit rhs_flag_bit_cell.
Axiom rhs_flag_rem_common: iscommon rhs_flag_rem_cell.
Axiom rhs_flag_rem_diff_common: iscommon rhs_flag_rem_diff_cell.

Axiom diff_u16_cells_le0_u16: is16 diff_u16_cells_le0.
Axiom diff_u16_cells_le1_u16: is16 diff_u16_cells_le1.
Axiom diff_u16_cells_le2_u16: is16 diff_u16_cells_le2.
Axiom diff_u16_cells_le3_u16: is16 diff_u16_cells_le3.

 (* u64 cells *)
 Axiom diff_u64: is64_from16
    diff_u64_cell
    diff_u16_cells_le0
    diff_u16_cells_le1 
    diff_u16_cells_le2 
    diff_u16_cells_le3.

Axiom diff_is_u64: is64 diff_u64_cell.

Axiom res_is_eq_bit: isbit res_is_eq_cell.
Axiom res_is_lt_bit: isbit res_is_lt_cell.
Axiom res_is_gt_bit: isbit res_is_gt_cell.

Axiom op_is_eq_bit: isbit op_is_eq_cell. 
Axiom op_is_ne_bit: isbit op_is_ne_cell.
Axiom op_is_lt_bit: isbit op_is_lt_cell.  
Axiom op_is_gt_bit: isbit op_is_gt_cell.  
Axiom op_is_le_bit: isbit op_is_le_cell. 
Axiom op_is_ge_bit: isbit op_is_ge_cell.

(* stack_read_rhs *)
Axiom stack_read_rhs :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read_rhs
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => get is_i32_cell)
    (fun get => get rhs_u64_cell)
    (fun get => get (ops_cell Rel)).
 
(* stack_read_lhs *)
Axiom stack_read_lhs :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read_lhs
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    (fun get => get is_i32_cell)
    (fun get => get lhs_u64_cell)
    (fun get => get (ops_cell Rel)).

(* stack_write *)
Axiom stack_write :
  alloc_memory_table_lookup_write_cell_with_value
    memory_table_lookup_stack_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    (fun get => get is_i32_cell)
    (fun get => get (ops_cell Rel)).
Notation res := (memory_table_lookup_stack_write AMTLWC_value_cell).

(* rel: selector *)
Axiom rel_selector :
    gate etable
    (fun get =>
        (get (ops_cell Rel) 0) * 
             ((get op_is_eq_cell 0)
            + (get op_is_ne_cell 0)
            + (get op_is_lt_cell 0)
            + (get op_is_gt_cell 0)
            + (get op_is_le_cell 0)
            + (get op_is_ge_cell 0)
            - 1)
        :: nil).

(* rel: compare diff *)
Axiom rel_compare_diff :
    gate etable
    (fun get => 
    (get (ops_cell Rel) 0) * 
        ((get lhs_u64_cell 0) 
            + (get res_is_lt_cell 0)
                * (get diff_u64_cell 0)
            - (get res_is_gt_cell 0)
                * (get diff_u64_cell 0)
            - (get rhs_u64_cell 0))
    ::(get (ops_cell Rel) 0) * 
        ((get res_is_gt_cell 0)
            + (get res_is_lt_cell 0)
            + (get res_is_eq_cell 0)
            - 1)
    ::(get (ops_cell Rel) 0) * 
        ((get diff_u64_cell 0)
            * (get res_is_eq_cell 0))
    ::(get (ops_cell Rel) 0) * 
        ((get diff_u64_cell 0)
            * (get diff_inv_cell 0)
        + (get res_is_eq_cell 0)
        - 1)
    :: nil).

(* rel: compare op res *)
Axiom rel_compare_op_res :
    gate etable
    (fun get => 
    (get (ops_cell Rel) 0) * 
        ((get l_pos_r_pos_cell 0) 
            - (1 - get lhs_flag_bit_cell 0)
                * (1 - get rhs_flag_bit_cell 0))
    ::(get (ops_cell Rel) 0) * 
        ((get l_pos_r_neg_cell 0)
            - (1 - get lhs_flag_bit_cell 0)
                * (get rhs_flag_bit_cell 0))
    ::(get (ops_cell Rel) 0) * 
        ((get l_neg_r_pos_cell 0)
            - (get lhs_flag_bit_cell 0 )
                * (1 - get rhs_flag_bit_cell 0))
    ::(get (ops_cell Rel) 0) * 
        ((get l_neg_r_neg_cell 0)
            - (get lhs_flag_bit_cell 0)
                * (get rhs_flag_bit_cell 0))
    ::(get (ops_cell Rel) 0) * 
        ((get op_is_eq_cell 0)
            * (get res 0 - get res_is_eq_cell 0))
    ::(get (ops_cell Rel) 0) * 
        ((get op_is_ne_cell 0)
            * (get res 0 - 1 + get res_is_eq_cell 0))
    ::(get (ops_cell Rel) 0) * 
        ((get op_is_lt_cell 0)
            * (get res 0 
                - get l_neg_r_pos_cell 0 
                - get l_pos_r_pos_cell 0 * get res_is_lt_cell 0 
                - get l_neg_r_neg_cell 0 * get res_is_lt_cell 0))
    ::(get (ops_cell Rel) 0) * 
        ((get op_is_le_cell 0)
            * (get res 0 
                - get l_neg_r_pos_cell 0 
                - get l_pos_r_pos_cell 0 * get res_is_lt_cell 0 
                - get l_neg_r_neg_cell 0 * get res_is_lt_cell 0 
                - get res_is_eq_cell 0))
    ::(get (ops_cell Rel) 0) * 
        ((get op_is_gt_cell 0)
            * (get res 0
                - get l_pos_r_neg_cell 0 
                - get l_pos_r_pos_cell 0 * get res_is_gt_cell 0
                - get l_neg_r_neg_cell 0 * get res_is_gt_cell 0))

    ::(get (ops_cell Rel) 0) * 
        ((get op_is_ge_cell 0)
            * (get res 0
                - get l_pos_r_neg_cell 0
                - get l_pos_r_pos_cell 0 * get res_is_gt_cell 0
                - get l_neg_r_neg_cell 0 * get res_is_gt_cell 0
                - get res_is_eq_cell 0))
    ::nil).

