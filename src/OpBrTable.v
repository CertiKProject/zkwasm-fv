(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import ImageTableModel.
Require Import OpBrTableModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_br_table : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct BrTable i.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem BrTable_branch_no_keep_correct : forall i st xid xd xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell BrTable) i = 1 ->
  state_rel i st ->
  wasm_stack st = xid :: xd ++ xs ->
  length xd = Z.to_nat (etable_values drop i) ->
  etable_values keep i = 0 ->
  state_rel (i+1) (update_stack (move_to_iid st (etable_values dst_iid i)) xs).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem BrTable_branch_and_keep_correct : forall i st xid xv xd xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell BrTable) i = 1 ->
  state_rel i st ->
  wasm_stack st = xid :: xv :: xd ++ xs ->
  length xd = Z.to_nat (etable_values drop i) ->
  etable_values keep i = 1 ->
  state_rel (i+1) (update_stack (move_to_iid st (etable_values dst_iid i)) (xv :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)
