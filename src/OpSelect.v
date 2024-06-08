(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import FunctionalExtensionality.
Require Import Shared.
Require Import OpSelectModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_select : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Select i.
Admitted. (* Proof omitted for release, present in original source. *)

Definition select cond val2 val1 : Z :=
    match cond with
    | 0 => val2
    | _ => val1
    end.

Theorem SelectOp_correct : forall i st xcond x2 x1 xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Select) i = 1 ->
  state_rel i st ->
  wasm_stack st = xcond:: x2 :: x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) ((select xcond x2 x1):: xs)).
Admitted. (* Proof omitted for release, present in original source. *)
