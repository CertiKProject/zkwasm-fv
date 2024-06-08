(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import FunctionalExtensionality.
Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import JTableModel JTable.
Require Import ETable.
Require Import Relation RelationHelper.

Require Import OpReturnModel.

(* Proofs about op_return.rs. *)

Require Import Wasm.numerics.
Require Import Lia.
Require Import MTable.

Theorem opcode_mops_correct_return : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Return i.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma stack_rel_drop : forall xs ys stk_map sp,
    stack_rel stk_map sp (xs++ys) ->
    stack_rel stk_map (sp + Z.of_nat (length xs)) ys.
Admitted. (* Proof omitted for release, present in original source. *)

(* Two cases, for keep=1 and keep=0 *)

Theorem Return_correct_nokeep : forall i st xs ys,
  0 <= i ->
  i + 1 < ETableModel.etable_numRow ->
  etable_values frame_id_cell i > 0 ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Return) i = 1 ->
  etable_values keep i = 0 ->
  state_rel i st ->
  wasm_stack st = xs++ys ->
  etable_values drop i = Z.of_nat (length xs)  ->
  exists lbl cs',
    (wasm_callstack st) = lbl::cs'
    /\ state_rel (i+1) (update_callstack (update_stack (move_to_label st lbl) ys) cs').
Admitted. (* Proof omitted for release, present in original source. *)

Theorem Return_correct_keep : forall i st x xs ys,
  0 <= i ->
  i + 1 < ETableModel.etable_numRow ->
  etable_values frame_id_cell i > 0 ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Return) i = 1 ->
  etable_values keep i = 1 ->
  state_rel i st ->
  wasm_stack st = x::xs++ys ->
  etable_values drop i = Z.of_nat (length xs)  ->
  exists lbl cs',
    (wasm_callstack st) = lbl::cs'
    /\ state_rel (i+1) (update_callstack (update_stack (move_to_label st lbl) (x::ys)) cs').
Admitted. (* Proof omitted for release, present in original source. *)
