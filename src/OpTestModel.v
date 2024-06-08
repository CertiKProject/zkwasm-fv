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

(* Translation of the constrains in op_test.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_test.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::Test], which is written (ops_cell Test) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation is_i32_cell := op_test_is_i32_cell.
Notation res_cell := op_test_res_cell.
Notation value_cell := op_test_value_cell.
Notation value_inv_cell := op_test_value_inv_cell.
Notation memory_table_lookup_stack_read := op_test_memory_table_lookup_stack_read.
Notation memory_table_lookup_stack_write := op_test_memory_table_lookup_stack_write.

Axiom stack_read :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => get is_i32_cell)
    (fun get => get value_cell)
    (fun get => get (ops_cell Test)).

Axiom stack_write :
  alloc_memory_table_lookup_write_cell
    memory_table_lookup_stack_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => 1)
    (fun get => get res_cell)
    (fun get => get (ops_cell Test)).

Axiom is_i32_cell_bit : isbit is_i32_cell.
Axiom res_cell_bit : isbit res_cell.
Axiom value_cell_U64 : is64 value_cell.

Axiom op_test_res_not_value :
  gate etable
    (fun get =>
    (get (ops_cell Test) 0)
  * ((get res_cell 0) * (get value_cell 0))
  ::(get (ops_cell Test) 0)
  * ((get value_cell 0) * (get value_inv_cell 0) - 1 + (get res_cell 0))
  ::nil).
