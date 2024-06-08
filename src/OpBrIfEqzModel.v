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

(* Translation of the constrains in op_br_if_eqz.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_br_if_eqz.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::BrIfEqz], which is written (ops_cell BrIfEqz) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation cond_inv_cell := op_br_if_eqz_cond_inv_cell.
Notation cond_is_zero_cell := op_br_if_eqz_cond_is_zero_cell.
Notation cond_is_not_zero_cell := op_br_if_eqz_cond_is_not_zero_cell.
Notation keep_cell := op_br_if_eqz_keep_cell.
Notation is_i32_cell := op_br_if_eqz_is_i32_cell.
Notation drop_cell := op_br_if_eqz_drop_cell.
Notation dst_pc_cell := op_br_if_eqz_dst_pc_cell.
Notation memory_table_lookup_stack_read_cond := op_br_if_eqz_memory_table_lookup_stack_read_cond.
Notation memory_table_lookup_stack_read_return_value := op_br_if_eqz_memory_table_lookup_stack_read_return_value.
Notation memory_table_lookup_stack_write_return_value := op_br_if_eqz_memory_table_lookup_stack_write_return_value.

Axiom stack_read_cond :
  alloc_memory_table_lookup_read_cell_with_value
    memory_table_lookup_stack_read_cond
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => 1)
    (fun get => get (ops_cell BrIfEqz)).
Notation cond_cell := (memory_table_lookup_stack_read_cond AMTLRC_value_cell).

Axiom stack_read_return_value :
  alloc_memory_table_lookup_read_cell_with_value
    memory_table_lookup_stack_read_return_value
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    (fun get => get is_i32_cell)
    (fun get => get (ops_cell BrIfEqz) * (get keep_cell) * (get cond_is_zero_cell)).
Notation value_cell := (memory_table_lookup_stack_read_return_value AMTLRC_value_cell).

Axiom stack_write_return_value :
  alloc_memory_table_lookup_write_cell
    memory_table_lookup_stack_write_return_value
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + get drop_cell + 2)
    (fun get => get is_i32_cell)
    (fun get => get value_cell)
    (fun get => get (ops_cell BrIfEqz) * (get keep_cell) * (get cond_is_zero_cell)).

Axiom cond_is_zero_cell_bit : isbit cond_is_zero_cell.
Axiom cond_is_not_zero_cell_bit : isbit cond_is_not_zero_cell.
Axiom keep_cell_bit : isbit keep_cell.
Axiom is_i32_cell_bit : isbit is_i32_cell.

Axiom drop_cell_common : iscommon drop_cell.
Axiom dst_pc_cell_common : iscommon dst_pc_cell.

Axiom op_br_if_eqz_cond_bit :
  gate etable
    (fun get =>
    (get (ops_cell BrIfEqz) 0)
  * (get cond_is_zero_cell 0) * (get cond_cell 0)
  ::(get (ops_cell BrIfEqz) 0)
  * ((get cond_is_zero_cell 0) + (get cond_cell 0) * (get cond_inv_cell 0)
  - 1)
  ::(get (ops_cell BrIfEqz) 0)
  * ((get cond_is_zero_cell 0) + (get cond_is_not_zero_cell 0) - 1)
  ::nil).
