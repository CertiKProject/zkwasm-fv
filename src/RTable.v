(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

(* Proofs about the optable in rtable.rs *)

Require Import List.
Require Import ZArith.
Require Import Lia.

Require Import Shared.
Require Import IntegerFunctions.
Require Import RTableModel.

Ltac destr_conj :=
  repeat match goal with
      [ H: _ /\ _  |- _ ] => destruct H
      end.

Theorem in_op_table_and : forall x y res,
  in_op_table BitOp_And x y res ->
       0 <= x < 256 
    /\ 0 <= y < 256 
    /\ res = Z.land x y.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem in_op_table_or : forall x y res,
in_op_table BitOp_Or x y res ->
     0 <= x < 256 
  /\ 0 <= y < 256 
  /\ res = Z.lor x y.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem in_op_table_xor : forall x y res,
in_op_table BitOp_Xor x y res ->
     0 <= x < 256 
  /\ 0 <= y < 256 
  /\ res = Z.lxor x y.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem in_op_table_popcnt : forall x y res,
in_op_table Popcnt_index x y res ->
     0 <= x < 256 
  /\ y = 0
  /\ res = popcnt x.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem in_op_table_power : forall x y res,
    in_op_table Power_index x y res ->
    (y <> 0 \/ res <> 0) ->
    128 <= y < 256 /\ res = 2 ^ (y - 128).
Admitted. (* Proof omitted for release, present in original source. *)
