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

(* Translation of the constrains in op_memory_size.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_memory_size.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::MemorySize], which is written (ops_cell MemorySize) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation allocated_memory_pages := mpages_cell.
Notation memory_table_lookup_stack_write := op_memory_size_memory_table_lookup_stack_write.

Axiom stack_write :
  alloc_memory_table_lookup_write_cell
    memory_table_lookup_stack_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell)
    (fun get => 1)
    (fun get => get allocated_memory_pages)
    (fun get => get (ops_cell MemorySize)).
