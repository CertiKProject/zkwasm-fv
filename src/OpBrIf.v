(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpBrIfModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_br_if : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct BrIf i.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem BrIf_no_branch_correct : forall i st xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell BrIf) i = 1 ->
  state_rel i st ->
  wasm_stack st = 0 :: xs ->
  state_rel (i+1) (update_stack (incr_iid st) xs).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem BrIf_branch_no_keep_correct : forall i st xcond xd xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell BrIf) i = 1 ->
  state_rel i st ->
  wasm_stack st = xcond :: xd ++ xs ->
  xcond <> 0 ->
  length xd = Z.to_nat (etable_values drop_cell i) ->
  etable_values keep_cell i = 0 ->
  state_rel (i+1) (update_stack (move_to_iid st (etable_values dst_pc_cell i)) xs).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem BrIf_branch_and_keep_correct : forall i st xcond xv xd xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell BrIf) i = 1 ->
  state_rel i st ->
  wasm_stack st = xcond :: xv :: xd ++ xs ->
  xcond <> 0 ->
  length xd = Z.to_nat (etable_values drop_cell i) ->
  etable_values keep_cell i = 1 ->
  state_rel (i+1) (update_stack (move_to_iid st (etable_values dst_pc_cell i)) (xv :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)
