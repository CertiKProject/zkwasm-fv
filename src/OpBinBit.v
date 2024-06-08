(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETable.
Require Import Relation RelationHelper.
Require MTable.

Require Import OpBinBitModel.

(* Proofs about op_bin_bit.rs. *)

Require Import Wasm.numerics.
Require Import BitTableModel.
Require BitTable.
Require Import Lia.
Require Import MTable.

Theorem opcode_mops_correct_bin_bit : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct BinBit i.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem BitOp_And_correct : forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinBit) i = 1 ->
    etable_values op_class i = RTableModel.BitOp_And ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1:: Wasm_int.Z_of_uint i64m x2::xs) ->
    state_rel (i+1) ((update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_and i64m x2 x1) :: xs))).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem BitOp_Or_correct : forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinBit) i = 1 ->
    etable_values op_class i = RTableModel.BitOp_Or ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1:: Wasm_int.Z_of_uint i64m x2::xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_or i64m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem BitOp_Xor_correct : forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinBit) i = 1 ->
    etable_values op_class i = RTableModel.BitOp_Xor ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1:: Wasm_int.Z_of_uint i64m x2::xs) ->
    state_rel (i+1)
      (update_stack (incr_iid st)
         (Wasm_int.Z_of_uint i64m (Wasm_int.int_xor i64m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

