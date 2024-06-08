(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Wasm.numerics.

Require Import Shared.
Require Import ImageTableModel.
Require Import ETable.
Require MTable.
Require MTableModel.

(* Translation of the constrains in op_br_table.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_br_table.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::BrTable], which is written (ops_cell BrTable) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation keep := op_br_table_keep.
Notation keep_is_i32 := op_br_table_keep_is_i32.
Notation keep_value := op_br_table_keep_value.
Notation drop := op_br_table_drop.
Notation dst_iid := op_br_table_dst_iid.
Notation expected_index := op_br_table_expected_index.
Notation effective_index := op_br_table_effective_index.
Notation targets_len := op_br_table_targets_len.
Notation is_out_of_bound := op_br_table_is_out_of_bound.
Notation is_not_out_of_bound := op_br_table_is_not_out_of_bound.
Notation diff := op_br_table_diff.
Notation memory_table_lookup_stack_read_index := op_br_table_memory_table_lookup_stack_read_index.
Notation memory_table_lookup_stack_read_return_value := op_br_table_memory_table_lookup_stack_read_return_value.
Notation memory_table_lookup_stack_write_return_value := op_br_table_memory_table_lookup_stack_write_return_value.
Notation br_table_lookup := brtable_lookup_cell.

Axiom stack_read_index :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read_index
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => 1)
    (fun get => get expected_index)
    (fun get => get (ops_cell BrTable)).

Axiom stack_read_return_value :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read_return_value
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    (fun get => get keep_is_i32)
    (fun get => get keep_value)
    (fun get => get (ops_cell BrTable) * (get keep)).

Axiom stack_write_return_value :
  alloc_memory_table_lookup_write_cell
    memory_table_lookup_stack_write_return_value
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + get drop + 2)
    (fun get => get keep_is_i32)
    (fun get => get keep_value)
    (fun get => get (ops_cell BrTable) * (get keep)).

Axiom keep_bit : isbit keep.
Axiom keep_is_i32_bit : isbit keep_is_i32.
Axiom is_out_of_bound_bit : isbit is_out_of_bound.
Axiom is_not_out_of_bound_bit : isbit is_not_out_of_bound.

Axiom drop_common : iscommon drop.
Axiom dst_iid_common : iscommon dst_iid.
Axiom effective_index_common : iscommon effective_index.
Axiom targets_len_common : iscommon targets_len.

Axiom keep_value_U64 : is64 keep_value.
Axiom expected_index_U64 : is64 expected_index.
Axiom diff_U64 : is64 diff.

Axiom op_br_table_oob :
  gate etable
    (fun get =>
    (get (ops_cell BrTable) 0)
  * ((get is_not_out_of_bound 0) + (get is_out_of_bound 0) - 1)
  ::(get (ops_cell BrTable) 0) * (get is_out_of_bound 0)
  * ((get targets_len 0) + (get diff 0) - (get expected_index 0))
  ::(get (ops_cell BrTable) 0) * (get is_not_out_of_bound 0)
  * ((get expected_index 0) + (get diff 0) + 1 - (get targets_len 0))
  ::nil).

Axiom op_br_table_effective_index_gate :
  gate etable
    (fun get =>
    (get (ops_cell BrTable) 0) * (get is_out_of_bound 0)
  * ((get targets_len 0) - 1 - (get effective_index 0))
  ::(get (ops_cell BrTable) 0) * (get is_not_out_of_bound 0)
  * ((get expected_index 0) - (get effective_index 0))
  ::nil).

Axiom op_br_table_br_table_lookup :
  gate etable
    (fun get =>
    (get (ops_cell BrTable) 0)
  * ((get br_table_lookup 0) - encode_br_table_entry 
      (get fid_cell 0) 
      (get iid_cell 0) 
      (get effective_index 0) 
      (get drop 0) 
      (get keep 0) 
      (get dst_iid 0))
  ::nil).
