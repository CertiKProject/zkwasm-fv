(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpMemorySizeModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_memory_size : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct MemorySize i.
Admitted. (* Proof omitted for release, present in original source. *)

Require Import Wasm.operations.

Theorem MemorySizeOp_correct : forall i st xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell MemorySize) i = 1 ->
  state_rel i st ->
  wasm_stack st = xs ->
  state_rel (i+1) (update_stack (incr_iid st) (Z.of_N (mem_size (wasm_memory st)) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)
