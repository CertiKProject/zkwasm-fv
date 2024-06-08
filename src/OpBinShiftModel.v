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

(* Translation of the constrains in op_bin_shift.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_bin_shift.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::BinShift], which is written (ops_cell BinShift) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation is_i32 := op_bin_shift_is_i32.
Notation lhs_u64_cell := op_bin_shift_lhs_u64_cell.
Notation lhs_u16_cells_le_0 := op_bin_shift_lhs_u16_cells_le_0.
Notation lhs_u16_cells_le_1 := op_bin_shift_lhs_u16_cells_le_1.
Notation lhs_u16_cells_le_2 := op_bin_shift_lhs_u16_cells_le_2.
Notation lhs_u16_cells_le_3 := op_bin_shift_lhs_u16_cells_le_3.
Notation lhs_flag_bit_cell := op_bin_shift_lhs_flag_bit_cell.
Notation lhs_flag_u16_rem_cell := op_bin_shift_lhs_flag_u16_rem_cell.
Notation lhs_flag_u16_rem_diff_cell := op_bin_shift_lhs_flag_u16_rem_diff_cell.
Notation rhs_u64_cell := op_bin_shift_rhs_u64_cell.
Notation rhs_u16_cells_le_0 := op_bin_shift_rhs_u16_cells_le_0.
Notation rhs_u16_cells_le_1 := op_bin_shift_rhs_u16_cells_le_1.
Notation rhs_u16_cells_le_2 := op_bin_shift_rhs_u16_cells_le_2.
Notation rhs_u16_cells_le_3 := op_bin_shift_rhs_u16_cells_le_3.
Notation round := op_bin_shift_round.
Notation rem := op_bin_shift_rem.
Notation diff := op_bin_shift_diff.
Notation pad := op_bin_shift_pad.
Notation rhs_modulus := op_bin_shift_rhs_modulus.
Notation size_modulus := op_bin_shift_size_modulus.
Notation rhs_round := op_bin_shift_rhs_round.
Notation rhs_rem := op_bin_shift_rhs_rem.
Notation rhs_rem_diff := op_bin_shift_rhs_rem_diff.
Notation is_shl := op_bin_shift_is_shl.
Notation is_shr_u := op_bin_shift_is_shr_u.
Notation is_shr_s := op_bin_shift_is_shr_s.
Notation is_rotl := op_bin_shift_is_rotl.
Notation is_rotr := op_bin_shift_is_rotr.
Notation is_l := op_bin_shift_is_l.
Notation is_r := op_bin_shift_is_r.
Notation degree_helper := op_bin_shift_degree_helper.
Notation lookup_pow_modulus := pow_table_lookup_modulus_cell.
Notation lookup_pow_power := pow_table_lookup_power_cell.
Notation memory_table_lookup_stack_read_rhs := op_bin_shift_memory_table_lookup_stack_read_rhs.
Notation memory_table_lookup_stack_read_lhs := op_bin_shift_memory_table_lookup_stack_read_lhs.
Notation memory_table_lookup_stack_write := op_bin_shift_memory_table_lookup_stack_write.

Axiom stack_read_rhs :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read_rhs
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => get is_i32)
    (fun get => get rhs_u64_cell)
    (fun get => get (ops_cell BinShift)).

Axiom stack_read_lhs :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read_lhs
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    (fun get => get is_i32)
    (fun get => get lhs_u64_cell)
    (fun get => get (ops_cell BinShift)).

Axiom stack_write :
  alloc_memory_table_lookup_write_cell_with_value
    memory_table_lookup_stack_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    (fun get => get is_i32)
    (fun get => get (ops_cell BinShift)).
Notation res := (memory_table_lookup_stack_write AMTLWC_value_cell).

Axiom is_i32_bit : isbit is_i32.
Axiom lhs_flag_bit_cell_bit : isbit lhs_flag_bit_cell.
Axiom is_shl_bit : isbit is_shl.
Axiom is_shr_u_bit : isbit is_shr_u.
Axiom is_shr_s_bit : isbit is_shr_s.
Axiom is_rotl_bit : isbit is_rotl.
Axiom is_rotr_bit : isbit is_rotr.
Axiom is_l_bit : isbit is_l.
Axiom is_r_bit : isbit is_r.

Axiom lhs_flag_u16_rem_cell_common : iscommon lhs_flag_u16_rem_cell.
Axiom lhs_flag_u16_rem_diff_cell_common : iscommon lhs_flag_u16_rem_diff_cell.
Axiom rhs_round_common : iscommon rhs_round.
Axiom rhs_rem_common : iscommon rhs_rem.
Axiom rhs_rem_diff_common : iscommon rhs_rem_diff.

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

Axiom round_U64 : is64 round.
Axiom rem_U64 : is64 rem.
Axiom diff_U64 : is64 diff.

Axiom lhs_flag_bit_dyn :
  gate etable 
    (fun get =>
    let flag_u16 := (get lhs_u16_cells_le_3 0)
    + (get is_i32 0)
    * (get lhs_u16_cells_le_1 0 - get lhs_u16_cells_le_3 0) in

    (get lhs_flag_bit_cell 0) * (Z.shiftl 1 15)
  + (get lhs_flag_u16_rem_cell 0) - flag_u16
  ::(get lhs_flag_u16_rem_cell 0) + (get lhs_flag_u16_rem_diff_cell 0)
  - ((Z.shiftl 1 15) - 1)
  ::nil).

Axiom bin_shift_op_select :
  gate etable
    (fun get =>
    (get (ops_cell BinShift) 0)
  * ((get is_shr_u 0) + (get is_shr_s 0) + (get is_rotr 0) - (get is_r 0))
  ::(get (ops_cell BinShift) 0)
  * ((get is_shl 0) + (get is_rotl 0) - (get is_l 0))
  ::(get (ops_cell BinShift) 0)
  * ((get is_l 0) + (get is_r 0) - 1)
  ::nil).

Axiom bin_shift_modulus :
  gate etable
    (fun get =>
    (get (ops_cell BinShift) 0) 
  * (get rhs_modulus 0 - 64 + get is_i32 0 * 32)
  ::(get (ops_cell BinShift) 0)
  * (get size_modulus 0 - (Z.shiftl 1 64) 
  + get is_i32 0 * (Z.shiftl 0xFFFFFFFF 32))
  ::nil).

Axiom bin_shift_rhs_rem :
  gate etable
    (fun get =>
    (get (ops_cell BinShift) 0) 
  * ((get rhs_round 0) * (get rhs_modulus 0)
  + (get rhs_rem 0) - (get rhs_u16_cells_le_0 0))
  ::(get (ops_cell BinShift) 0)
  * (get rhs_rem 0 + get rhs_rem_diff 0 + 1
  - get rhs_modulus 0)
  ::nil).

Axiom bin_shift_modulus_pow_lookup :
  gate etable
    (fun get =>
    (get (ops_cell BinShift) 0) 
  * (get lookup_pow_power 0 - (get rhs_rem 0 + 128))
  ::nil).

Axiom bin_shift_is_r :
  gate etable
    (fun get =>
    (get (ops_cell BinShift) 0) * (get is_r 0)
  * (get rem 0 
  + get round 0 * get lookup_pow_modulus 0 
  - get lhs_u64_cell 0)
  ::(get (ops_cell BinShift) 0) * (get is_r 0)
  * (get rem 0 + get diff 0 + 1 
  - get lookup_pow_modulus 0)
  ::nil).

Axiom bin_shift_shr_u :
  gate etable
    (fun get =>
    (get (ops_cell BinShift) 0) * (get is_shr_u 0)
  * (get res 0 - get round 0)
  ::nil).

Axiom bin_shift_shr_s :
  gate etable
    (fun get =>
    (get (ops_cell BinShift) 0)
  * (get degree_helper 0 
  - (get lookup_pow_modulus 0 - 1) * (get size_modulus 0))
  ::(get (ops_cell BinShift) 0) * (get is_shr_s 0)
  * (get pad 0 * get lookup_pow_modulus 0
  - get lhs_flag_bit_cell 0 * get degree_helper 0)
  ::(get (ops_cell BinShift) 0) * (get is_shr_s 0)
  * (get res 0 - get round 0 - get pad 0)
  ::nil).

Axiom bin_shift_is_rotr :
  gate etable
    (fun get =>
    (get (ops_cell BinShift) 0) * (get is_rotr 0)
  * (get res 0 * get lookup_pow_modulus 0
  - get round 0 * get lookup_pow_modulus 0
  - get rem 0 * get size_modulus 0)
  ::nil).

Axiom bin_shift_is_l :
  gate etable
    (fun get =>
    (get (ops_cell BinShift) 0) * (get is_l 0)
  * (get lhs_u64_cell 0 * get lookup_pow_modulus 0
  - get round 0 * get size_modulus 0 - get rem 0)
  ::(get (ops_cell BinShift) 0) * (get is_l 0)
  * (get rem 0 + get diff 0 + 1 - get size_modulus 0)
  ::nil).

Axiom bin_shift_shl :
  gate etable
    (fun get =>
    (get (ops_cell BinShift) 0) * (get is_shl 0)
  * (get res 0 - get rem 0)
  ::nil).

Axiom bin_shift_rotl :
  gate etable
    (fun get =>
    (get (ops_cell BinShift) 0) * (get is_rotl 0)
  * (get res 0 - get rem 0 - get round 0)
  ::nil).
