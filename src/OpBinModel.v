(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Wasm.numerics.

Require Import Shared.
Require Import ETable.
Require MTable.
Require MTableModel.

(* Translation of the constrains in op_bin.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_bin.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::Bin], which is written (ops_cell Bin) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation is_i32 := op_bin_is_i32.
Notation lhs_u64_cell := op_bin_lhs_u64_cell.
Notation lhs_u16_cells_le_0 := op_bin_lhs_u16_cells_le_0.
Notation lhs_u16_cells_le_1 := op_bin_lhs_u16_cells_le_1.
Notation lhs_u16_cells_le_2 := op_bin_lhs_u16_cells_le_2.
Notation lhs_u16_cells_le_3 := op_bin_lhs_u16_cells_le_3.
Notation lhs_flag_bit_cell := op_bin_lhs_flag_bit_cell.
Notation lhs_flag_u16_rem_cell := op_bin_lhs_flag_u16_rem_cell.
Notation lhs_flag_u16_rem_diff_cell := op_bin_lhs_flag_u16_rem_diff_cell.
Notation rhs_u64_cell := op_bin_rhs_u64_cell.
Notation rhs_u16_cells_le_0 := op_bin_rhs_u16_cells_le_0.
Notation rhs_u16_cells_le_1 := op_bin_rhs_u16_cells_le_1.
Notation rhs_u16_cells_le_2 := op_bin_rhs_u16_cells_le_2.
Notation rhs_u16_cells_le_3 := op_bin_rhs_u16_cells_le_3.
Notation rhs_flag_bit_cell := op_bin_rhs_flag_bit_cell.
Notation rhs_flag_u16_rem_cell := op_bin_rhs_flag_u16_rem_cell.
Notation rhs_flag_u16_rem_diff_cell := op_bin_rhs_flag_u16_rem_diff_cell.
Notation d_u64_cell := op_bin_d_u64_cell.
Notation d_u16_cells_le_0 := op_bin_d_u16_cells_le_0.
Notation d_u16_cells_le_1 := op_bin_d_u16_cells_le_1.
Notation d_u16_cells_le_2 := op_bin_d_u16_cells_le_2.
Notation d_u16_cells_le_3 := op_bin_d_u16_cells_le_3.
Notation d_flag_helper_diff := op_bin_d_flag_helper_diff.
Notation aux1 := op_bin_aux1.
Notation aux2 := op_bin_aux2.
Notation overflow := op_bin_overflow.
Notation is_add := op_bin_is_add.
Notation is_sub := op_bin_is_sub.
Notation is_mul := op_bin_is_mul.
Notation is_div_u := op_bin_is_div_u.
Notation is_div_s := op_bin_is_div_s.
Notation is_rem_u := op_bin_is_rem_u.
Notation is_rem_s := op_bin_is_rem_s.
Notation is_div_s_or_rem_s := op_bin_is_div_s_or_rem_s.
Notation d_leading_u16 := op_bin_d_leading_u16.
Notation normalized_lhs := op_bin_normalized_lhs.
Notation normalized_rhs := op_bin_normalized_rhs.
Notation res_flag := op_bin_res_flag.
Notation size_modulus := op_bin_size_modulus.
Notation degree_helper1 := op_bin_degree_helper1.
Notation degree_helper2 := op_bin_degree_helper2.
Notation memory_table_lookup_stack_read_rhs := op_bin_memory_table_lookup_stack_read_rhs.
Notation memory_table_lookup_stack_read_lhs := op_bin_memory_table_lookup_stack_read_lhs.
Notation memory_table_lookup_stack_write := op_bin_memory_table_lookup_stack_write.

Axiom stack_read_rhs :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read_rhs
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => get is_i32)
    (fun get => get rhs_u64_cell)
    (fun get => get (ops_cell Bin)).

Axiom stack_read_lhs :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read_lhs
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    (fun get => get is_i32)
    (fun get => get lhs_u64_cell)
    (fun get => get (ops_cell Bin)).

Axiom stack_write :
  alloc_memory_table_lookup_write_cell_with_value
    memory_table_lookup_stack_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    (fun get => get is_i32)
    (fun get => get (ops_cell Bin)).
Notation res := (memory_table_lookup_stack_write AMTLWC_value_cell).

Axiom is_i32_bit : isbit is_i32.
Axiom lhs_flag_bit_cell_bit : isbit lhs_flag_bit_cell.
Axiom rhs_flag_bit_cell_bit : isbit rhs_flag_bit_cell.
Axiom overflow_bit : isbit overflow.
Axiom is_add_bit : isbit is_add.
Axiom is_sub_bit : isbit is_sub.
Axiom is_mul_bit : isbit is_mul.
Axiom is_div_u_bit : isbit is_div_u.
Axiom is_div_s_bit : isbit is_div_s.
Axiom is_rem_u_bit : isbit is_rem_u.
Axiom is_rem_s_bit : isbit is_rem_s.
Axiom is_div_s_or_rem_s_bit : isbit is_div_s_or_rem_s.

Axiom lhs_flag_u16_rem_cell_common : iscommon lhs_flag_u16_rem_cell.
Axiom lhs_flag_u16_rem_diff_cell_common : iscommon lhs_flag_u16_rem_diff_cell.
Axiom rhs_flag_u16_rem_cell_common : iscommon rhs_flag_u16_rem_cell.
Axiom rhs_flag_u16_rem_diff_cell_common : iscommon rhs_flag_u16_rem_diff_cell.
Axiom d_flag_helper_diff_common : iscommon d_flag_helper_diff.

Axiom lhs_u16_cells_U16 : 
    is16 lhs_u16_cells_le_0 /\
    is16 lhs_u16_cells_le_1 /\
    is16 lhs_u16_cells_le_2 /\
    is16 lhs_u16_cells_le_3.

Axiom rhs_u16_cells_U16 :
    is16 rhs_u16_cells_le_0 /\
    is16 rhs_u16_cells_le_1 /\
    is16 rhs_u16_cells_le_2 /\
    is16 rhs_u16_cells_le_3.

Axiom d_u16_cells_U16 :
    is16 d_u16_cells_le_0 /\
    is16 d_u16_cells_le_1 /\
    is16 d_u16_cells_le_2 /\
    is16 d_u16_cells_le_3.

Axiom lhs_U64 : is64_from16
    lhs_u64_cell
    lhs_u16_cells_le_0
    lhs_u16_cells_le_1
    lhs_u16_cells_le_2
    lhs_u16_cells_le_3.

Axiom rhs_U64 : is64_from16
    rhs_u64_cell
    rhs_u16_cells_le_0
    rhs_u16_cells_le_1
    rhs_u16_cells_le_2
    rhs_u16_cells_le_3.

Axiom d_U64 : is64_from16
    d_u64_cell
    d_u16_cells_le_0
    d_u16_cells_le_1
    d_u16_cells_le_2
    d_u16_cells_le_3.

Axiom aux1_U64 : is64 aux1.
Axiom aux2_U64 : is64 aux2.

Axiom lhs_flag_bit_dyn :
  pgate etable 
    (fun get =>
    let flag_u16 := (get lhs_u16_cells_le_3 0)
    + (get is_i32 0)
    * (get lhs_u16_cells_le_1 0 - get lhs_u16_cells_le_3 0) in

    (get lhs_flag_bit_cell 0) * (Z.shiftl 1 15)
  + (get lhs_flag_u16_rem_cell 0) - flag_u16
  ::(get lhs_flag_u16_rem_cell 0) + (get lhs_flag_u16_rem_diff_cell 0)
  - ((Z.shiftl 1 15) - 1)
  ::nil).

Axiom rhs_flag_bit_dyn :
  pgate etable 
    (fun get =>
    let flag_u16 := (get rhs_u16_cells_le_3 0)
    + (get is_i32 0)
    * (get rhs_u16_cells_le_1 0 - get rhs_u16_cells_le_3 0) in

    (get rhs_flag_bit_cell 0) * (Z.shiftl 1 15)
  + (get rhs_flag_u16_rem_cell 0) - flag_u16
  ::(get rhs_flag_u16_rem_cell 0) + (get rhs_flag_u16_rem_diff_cell 0)
  - ((Z.shiftl 1 15) - 1)
  ::nil).

Axiom bin_selector :
  pgate etable
    (fun get =>
    (get (ops_cell Bin) 0)
  * ((get is_add 0) + (get is_sub 0) + (get is_mul 0) 
  + (get is_div_u 0) + (get is_rem_u 0) 
  + (get is_div_s 0) + (get is_rem_s 0) - 1)
  ::nil).

Axiom bin_size_modulus :
  pgate etable
    (fun get =>
    (get (ops_cell Bin) 0)
  * (get size_modulus 0 - (Z.shiftl 1 64)
  + (get is_i32 0) * (Z.shiftl 0xFFFFFFFF 32))
  ::nil).

Axiom bin_add :
  pgate etable
    (fun get =>
    (get (ops_cell Bin) 0) * (get is_add 0)
  * (get lhs_u64_cell 0 + get rhs_u64_cell 0 - get res 0
  - get overflow 0 * get size_modulus 0)
  ::nil).

Axiom bin_sub :
  pgate etable
    (fun get =>
    (get (ops_cell Bin) 0) * (get is_sub 0)
  * (get rhs_u64_cell 0 + get res 0 - get lhs_u64_cell 0 
  - get overflow 0 * get size_modulus 0)
  ::nil).

Axiom bin_mul_constraints :
  pgate etable
    (fun get =>
    (get (ops_cell Bin) 0) * (get is_mul 0)
  * (get lhs_u64_cell 0 * get rhs_u64_cell 0
  - get aux1 0 * get size_modulus 0
  - get res 0)
  ::nil).

Axiom bin_div_u_rem_u_constraints :
  pgate etable
    (fun get =>
    (get (ops_cell Bin) 0) * (get is_rem_u 0 + get is_div_u 0)
  * (get lhs_u64_cell 0 - get rhs_u64_cell 0 * get d_u64_cell 0 
  - get aux1 0)
  ::(get (ops_cell Bin) 0) * (get is_rem_u 0 + get is_div_u 0)
  * (get aux1 0 + get aux2 0 + 1
  - get rhs_u64_cell 0)
  ::(get (ops_cell Bin) 0) * (get is_div_u 0)
  * (get res 0 - get d_u64_cell 0)
  ::(get (ops_cell Bin) 0) * (get is_rem_u 0)
  * (get res 0 - get aux1 0)
  ::nil).

Axiom bin_res_flag :
  pgate etable
    (fun get =>
    (get (ops_cell Bin) 0)
  * (get res_flag 0 
  - (get lhs_flag_bit_cell 0 + get rhs_flag_bit_cell 0
  - 2 * get lhs_flag_bit_cell 0 * get rhs_flag_bit_cell 0))
  ::nil).

Axiom bin_div_s_rem_s_constraints_common :
  pgate etable
    (fun get =>
    (get (ops_cell Bin) 0)
  * (get is_div_s_or_rem_s 0 - (get is_div_s 0 + get is_rem_s 0))
  ::(get (ops_cell Bin) 0) * (get normalized_lhs 0 
  - (get lhs_u64_cell 0 * (1 - get lhs_flag_bit_cell 0) 
  + (get size_modulus 0 - get lhs_u64_cell 0) * get lhs_flag_bit_cell 0))
  ::(get (ops_cell Bin) 0) * (get normalized_rhs 0 
  - (get rhs_u64_cell 0 * (1 - get rhs_flag_bit_cell 0) 
  + (get size_modulus 0 - get rhs_u64_cell 0) * get rhs_flag_bit_cell 0))
  ::(get (ops_cell Bin) 0) * (get is_div_s_or_rem_s 0)
  * (get d_leading_u16 0 - (get d_u16_cells_le_3 0
  + (get is_i32 0) * (get d_u16_cells_le_1 0 - get d_u16_cells_le_3 0)))
  ::(get (ops_cell Bin) 0) * (get is_div_s_or_rem_s 0)
  * (get d_leading_u16 0 + get d_flag_helper_diff 0 - 0x7fff)
  * (1 - get res_flag 0)
  ::(get (ops_cell Bin) 0) * (get is_div_s_or_rem_s 0)
  * (get normalized_lhs 0 - get normalized_rhs 0 * get d_u64_cell 0
  - get aux1 0)
  ::(get (ops_cell Bin) 0) * (get is_div_s_or_rem_s 0)
  * (get aux1 0 + get aux2 0 + 1 - get normalized_rhs 0)
  ::nil).

Axiom bin_div_s_constraints_res :
  pgate etable
    (fun get =>
    (get (ops_cell Bin) 0) * (get is_div_s 0)
  * (get res 0 - get d_u64_cell 0)
  * (1 - get res_flag 0)
  ::(get (ops_cell Bin) 0) * (get is_div_s 0)
  * (get degree_helper1 0 
  - (get d_u64_cell 0 + get res 0) * get res_flag 0)
  ::(get (ops_cell Bin) 0) * (get is_div_s 0)
  * (get res 0 + get d_u64_cell 0 - get size_modulus 0)
  * (get degree_helper1 0)
  ::nil).

Axiom bin_rem_s_constraints_res :
  pgate etable
    (fun get =>
    (get (ops_cell Bin) 0) * (get is_rem_s 0)
  * (get res 0 - get aux1 0)
  * (1 - get lhs_flag_bit_cell 0)
  ::(get (ops_cell Bin) 0) * (get is_rem_s 0)
  * (get degree_helper2 0 
  - (get aux1 0 + get res 0) * get lhs_flag_bit_cell 0)
  ::(get (ops_cell Bin) 0) * (get is_rem_s 0)
  * (get res 0 + get aux1 0 - get size_modulus 0)
  * (get degree_helper2 0)
  ::nil).
