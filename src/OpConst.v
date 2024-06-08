(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpConstModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_const : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Const i.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem ConstOp_correct : forall i st x1 xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Const) i = 1 ->
  state_rel i st ->
  wasm_stack st = xs ->
  etable_values value i = x1 ->
  state_rel (i+1) (update_stack (incr_iid st) (x1:: xs)).
Admitted. (* Proof omitted for release, present in original source. *)
