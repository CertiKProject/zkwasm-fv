(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETable.
Require MTable.
Require Import Relation RelationHelper.

Require Import OpGlobalGetModel.

(* Proofs about op_global_get.rs. *)

Require Import Wasm.numerics.
Require Import Lia.
Require Import MTable.

Theorem opcode_mops_correct_global_get : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct GlobalGet i.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem GlobalGet_correct : forall i st idx xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell GlobalGet) i = 1 ->
  etable_values idx_cell i = Z.of_nat idx ->
  state_rel i st ->
  wasm_stack st = xs ->
  exists x v,
    glob_val (wasm_globals st) idx = Some v
  /\ value_rel x v    
  /\ state_rel (i+1) (update_stack (incr_iid st) (x :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)
