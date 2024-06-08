(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETable.
Require MTable.

Require Import OpUnaryModel.

(* Proofs about op_unary.rs. *)

Require Import Wasm.numerics.
Require Import IntegerFunctions.
Require Import BitTableModel.
Require BitTable.
Require Import Lia.
Require Import MTable.
Require Import Relation RelationHelper.

Theorem opcode_mops_correct_unary : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Unary i.
Admitted. (* Proof omitted for release, present in original source. *)

(* Clz proofs *)

(* Ctz proofs *)

(* Popcnt proofs *)

(* Stack related proofs *)

Theorem UnaryOp_Clz_correct : forall i st x1 xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Unary) i = 1 ->
  etable_values is_clz i = 1 ->
  state_rel i st ->
  wasm_stack st = Wasm_int.Z_of_uint i64m x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_clz i64m x1) - (etable_values is_i32 i) * 32:: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem UnaryOp_Ctz_64_correct : forall i st x1 xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Unary) i = 1 ->
  etable_values is_ctz i = 1 ->
  etable_values is_i32 i = 0 ->
  state_rel i st ->
  wasm_stack st = Wasm_int.Z_of_uint i64m x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_ctz i64m x1):: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem UnaryOp_Ctz_32_correct : forall i st x1 xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Unary) i = 1 ->
  etable_values is_ctz i = 1 ->
  etable_values is_i32 i = 1 ->
  state_rel i st ->
  wasm_stack st = Wasm_int.Z_of_uint i32m x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) (Wasm_int.Z_of_uint i32m (Wasm_int.int_ctz i32m x1):: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem UnaryOp_Popcnt_correct : forall i st x1 xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Unary) i = 1 ->
  etable_values op_unary_is_popcnt i = 1 ->
  state_rel i st ->
  wasm_stack st = Wasm_int.Z_of_uint i64m x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_popcnt i64m x1):: xs)).
Admitted. (* Proof omitted for release, present in original source. *)
