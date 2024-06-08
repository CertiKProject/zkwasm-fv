(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.
Require Import Wasm.operations.
Require Wasm.memory_list.

Require Import ZArith.
Require Import List.
Require Import FunctionalExtensionality.
Require Import Lia.

Require Import Shared.
Require Import OpMemoryGrowModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_memory_grow : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct MemoryGrow i.
Admitted. (* Proof omitted for release, present in original source. *)


(* The zkWasm constraints are less deterministic than WasmCert, it may refuse to grow
   a memory even if it is within the limit, and then let a later grow operation 
   succeed. (This probably is allowed by the English-language Wasm specification, even if 
   it would not be done by Wasmi.) So we have two cases, one when the operation succeeds
   and one it doesn't.
   Becuase we cover both possible values of (success i) this handles all possible traces. 
 *)
Theorem MemoryGrowOp_correct_nosuccess : forall i st x1 xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell MemoryGrow) i = 1 ->
  etable_values success i = 0   ->
  state_rel i st ->
  wasm_stack st = x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) (0xFFFFFFFF :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem MemoryGrowOp_correct_success : forall i st x1 xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell MemoryGrow) i = 1 ->
  etable_values success i = 1   ->
  state_rel i st ->
  wasm_stack st = x1:: xs ->
  exists mem',
    mem_grow (wasm_memory st) (Z.to_N x1) = Some mem' /\
    state_rel (i+1) (update_memory (update_stack (incr_iid st) (Z.of_N (mem_size (wasm_memory st)) :: xs)) mem').
Admitted. (* Proof omitted for release, present in original source. *)
