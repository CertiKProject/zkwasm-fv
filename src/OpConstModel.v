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

(* Translation of the constrains in op_const.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_const.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::Const], which is written (ops_cell Const) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation is_i32 := op_const_is_i32.
Notation value := op_const_value.
Notation memory_table_lookup_stack_write := op_const_memory_table_lookup_stack_write.

Axiom stack_write :
  alloc_memory_table_lookup_write_cell
    memory_table_lookup_stack_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell)
    (fun get => get is_i32)
    (fun get => get value)
    (fun get => get (ops_cell Const)).

Axiom is_i32_bit : isbit is_i32.
Axiom value_U64 : is64 value.
