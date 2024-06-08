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

(* Translation of the constrains in op_local_set.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_local_get.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::LocalSet], which is written (ops_cell LocalSet) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation is_i32_cell := op_local_set_is_i32_cell.
Notation offset_cell := op_local_set_offset_cell.
Notation value_cell := op_local_set_value_cell.
Notation memory_table_lookup_stack_read := op_local_set_memory_table_lookup_stack_read.
Notation memory_table_lookup_stack_write := op_local_set_memory_table_lookup_stack_write.
 
Axiom stack_read :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => get is_i32_cell)
    (fun get => get value_cell)
    (fun get => get (ops_cell LocalSet)).

Axiom stack_write :
  alloc_memory_table_lookup_write_cell
    memory_table_lookup_stack_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1 + get offset_cell)
    (fun get => get is_i32_cell)
    (fun get => get value_cell)
    (fun get => get (ops_cell LocalSet)).

Axiom is_i32_bit : isbit is_i32_cell.
Axiom offset_common : iscommon offset_cell.
Axiom value_U64 : is64 value_cell.
