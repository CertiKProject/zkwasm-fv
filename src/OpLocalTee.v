(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpLocalTeeModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_local_tee : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct LocalTee i.
Admitted. (* Proof omitted for release, present in original source. *)

(* Note: the offset value inn the etable, (etable_values offset_cell i), ultimately
   comes from the trace generated by Wasmi. The way Wasmi specifies the offset
   for LocalTee and LocalSet differ by 1, and zkWasm then follows that convention,
   which is why the Tee spec has -2 where the Set spec has -1. *)
Theorem LocalTeeOp_correct : forall i st y ys x xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell LocalTee) i = 1 ->
  state_rel i st ->
  wasm_stack st = y :: ys ++ x :: xs ->
  (etable_values offset_cell i) > 1 ->
  length ys =  (Z.to_nat (etable_values offset_cell i) -2 )%nat ->
  state_rel (i+1) (update_stack (incr_iid st) (y :: ys ++ y :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)
