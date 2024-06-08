(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.
Require Import Wasm.operations.

From mathcomp.ssreflect Require Import seq ssrfun.
From mathcomp.ssreflect Require ssrnat.

From compcert.lib Require Import Integers.
From compcert.common Require Import Memdata.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpLoadModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.
Require Import OpLoadHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_load : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Load i.
Admitted. (* Proof omitted for release, present in original source. *)

(* Todo: Maybe write a better definition of this in terms of `is_sign`
   and the number of bytes of the number (which we get from
   `is_eight_bytes` etc), instead of mixing in `load_picked_flag`. *)
Definition sign_extend i val :=
  val + (etable_values is_sign i) * (etable_values load_picked_flag i) * sign_extension i.

Require Import FunctionalExtensionality.

Theorem load_correct : forall i st base xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Load) i = 1 ->
  state_rel i st ->
  wasm_stack st =  (base :: xs) ->
  exists bs,
    load (wasm_memory st)
         (Z.to_N base)
         (Z.to_N (etable_values opcode_load_offset i))
         (Z.to_nat (etable_values len i)) = Some bs
    /\ state_rel (i+1) (update_stack (incr_iid st) ((sign_extend i (Memdata.decode_int bs)::xs))).
Admitted. (* Proof omitted for release, present in original source. *)
