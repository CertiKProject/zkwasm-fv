(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_drop : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Drop i.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem DropOp_correct : forall i st x1 xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Drop) i = 1 ->
  state_rel i st ->
  wasm_stack st = x1::xs ->
  state_rel (i+1) (update_stack (incr_iid st) xs).
Admitted. (* Proof omitted for release, present in original source. *)
