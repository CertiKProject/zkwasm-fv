(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETable.
Require MTable.
Require Import Relation RelationHelper.

Require Import OpGlobalSetModel.

(* Proofs about op_global_set.rs. *)

Require Import Wasm.numerics.
Require Import Lia.
Require Import MTable.

Theorem opcode_mops_correct_global_set : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct GlobalSet i.
Admitted. (* Proof omitted for release, present in original source. *)

Opaque set_glob.

Theorem GlobalSet_correct : forall i st idx glbs x v xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell GlobalSet) i = 1 ->
  etable_values idx_cell i = Z.of_nat idx ->
  state_rel i st ->
  value_rel x v ->
  wasm_stack st = (x::xs) ->
  wasm_globals st = glbs ->
  exists glbs',
  (set_glob glbs idx v) = Some glbs'
  /\ state_rel (i+1) (update_globals (update_stack (incr_iid st) xs) glbs').
Admitted. (* Proof omitted for release, present in original source. *)
