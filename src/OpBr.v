(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpBrModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_br : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Br i.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem Br_no_keep_correct : forall i st xd xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Br) i = 1 ->
  state_rel i st ->
  wasm_stack st = xd ++ xs ->
  length xd = Z.to_nat (etable_values drop_cell i) ->
  etable_values keep_cell i = 0 ->
  state_rel (i+1) (update_stack (move_to_iid st (etable_values dst_pc_cell i)) xs).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem Br_keep_correct : forall i st xv xd xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Br) i = 1 ->
  state_rel i st ->
  wasm_stack st = xv :: xd ++ xs ->
  length xd = Z.to_nat (etable_values drop_cell i) ->
  etable_values keep_cell i = 1 ->
  state_rel (i+1) (update_stack (move_to_iid st (etable_values dst_pc_cell i)) (xv :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)
