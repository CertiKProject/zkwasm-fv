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

(* Translation of the constrains in op_memory_grow.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_memory_grow.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::MemoryGrow], which is written (ops_cell MemoryGrow) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation grow_size := op_memory_grow_grow_size.
Notation result := op_memory_grow_result.
Notation current_maximal_diff := op_memory_grow_current_maximal_diff.
Notation success := op_memory_grow_success.
Notation current_memory_size := mpages_cell.
Notation maximal_memory_pages := maximal_memory_pages_cell.
Notation memory_table_lookup_stack_read := op_memory_grow_memory_table_lookup_stack_read.
Notation memory_table_lookup_stack_write := op_memory_grow_memory_table_lookup_stack_write.
 
Axiom stack_read :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => 1)
    (fun get => get grow_size)
    (fun get => get (ops_cell MemoryGrow)).

Axiom stack_write :
  alloc_memory_table_lookup_write_cell
    memory_table_lookup_stack_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => 1)
    (fun get => get result)
    (fun get => get (ops_cell MemoryGrow)).

Axiom success_bit : isbit success.
Axiom current_maximal_diff_common : iscommon current_maximal_diff.
Axiom grow_size_U64 : is64 grow_size.
Axiom result_U64 : is64 result.

Axiom memory_grow_return_value :
  gate etable
    (fun get =>
    (get (ops_cell MemoryGrow) 0) 
  * ((get result 0) - (0xFFFFFFFF + 
    (get success 0) * ((get current_memory_size 0) - 0xFFFFFFFF)))
  ::nil).

Axiom memory_grow_updated_memory_size :
  gate etable
    (fun get =>
    (get (ops_cell MemoryGrow) 0) * (get success 0)
  * ((get current_memory_size 0) + (get grow_size 0) 
  + (get current_maximal_diff 0) - (get maximal_memory_pages 0))
  ::nil).
