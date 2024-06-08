(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import Relation RelationHelper.
Require Import JTableModel JTable.
Require Import ETable.

Require Import OpCallIndirectModel.

(* Proofs about op_call_indirect.rs. *)

Require Import Wasm.numerics.
Require Import Lia.
Require Import MTable.

Theorem opcode_mops_correct_callindirect : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct CallIndirect i.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma call_mops : forall i,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    etable_values (ops_cell CallIndirect) i = 1 ->
    mops_at_correct i ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem CallIndirect_correct : forall i st x xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell CallIndirect) i = 1 ->
  state_rel i st ->
  wasm_stack st = (x::xs) ->
  state_rel (i+1) (update_callstack (move_to_label (update_stack st xs) (etable_values func_index i, 0))
                                    ((etable_values fid_cell i, etable_values iid_cell i + 1) :: (wasm_callstack st))).
Admitted. (* Proof omitted for release, present in original source. *)
