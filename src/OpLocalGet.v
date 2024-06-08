(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpLocalGetModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_local_get : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct LocalGet i.
Admitted. (* Proof omitted for release, present in original source. *)

Require Import FunctionalExtensionality.

Theorem LocalGetOp_correct : forall i st y xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell LocalGet) i = 1 ->
  state_rel i st ->
  wasm_stack st = xs ->
  (etable_values offset_cell i) > 1 ->
  nth_error xs (Z.to_nat (etable_values offset_cell i - 1)) = Some y ->
  state_rel (i+1) (update_stack (incr_iid st) (y :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)
