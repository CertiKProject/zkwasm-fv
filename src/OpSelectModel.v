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

(* Translation of the constrains in op_select.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_select.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::Select], which is written (ops_cell Select) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation cond := op_select_cond.
Notation cond_inv := op_select_cond_inv.
Notation val1 := op_select_val1.
Notation val2 := op_select_val2.
Notation res := op_select_res.
Notation is_i32 := op_select_is_i32.
Notation memory_table_lookup_stack_read_cond := op_select_memory_table_lookup_stack_read_cond.
Notation memory_table_lookup_stack_read_val2 := op_select_memory_table_lookup_stack_read_val2.
Notation memory_table_lookup_stack_read_val1 := op_select_memory_table_lookup_stack_read_val1.
Notation memory_table_lookup_stack_write := op_select_memory_table_lookup_stack_write.

Axiom stack_read_cond :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read_cond
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => 1)
    (fun get => get cond)
    (fun get => get (ops_cell Select)).

Axiom stack_read_val2 :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read_val2
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    (fun get => get is_i32)
    (fun get => get val2)
    (fun get => get (ops_cell Select)).

Axiom stack_read_val1 :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read_val1
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 3)
    (fun get => get is_i32)
    (fun get => get val1)
    (fun get => get (ops_cell Select)).

Axiom stack_write :
  alloc_memory_table_lookup_write_cell
    memory_table_lookup_stack_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 3)
    (fun get => get is_i32)
    (fun get => get res)
    (fun get => get (ops_cell Select)).

Axiom is_i32_bit : isbit is_i32.
Axiom cond_U64 : is64 cond.
Axiom val1_U64 : is64 val1.
Axiom val2_U64 : is64 val2.
Axiom res_U64 : is64 res.

Axiom select_cond_is_zero :
  gate etable
    (fun get =>
    (get (ops_cell Select) 0)
  * (1 - (get cond 0) * (get cond_inv 0))
  * ((get res 0) - (get val2 0))
  ::nil).

Axiom select_cond_is_not_zero :
  gate etable
    (fun get =>
    (get (ops_cell Select) 0) * (get cond 0) 
  * ((get res 0) - (get val1 0))
  ::nil).
