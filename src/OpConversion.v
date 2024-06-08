(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import ImageTableModel.
Require Import OpConversionModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_conversion : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Conversion i.
Admitted. (* Proof omitted for release, present in original source. *)

(* Only unsigned extension is I64ExtendI32 *)

(* wasm_extend_s in WasmCert-Coq only extends I32 to I64 instead of all types, like I8 to I32, and no notion of padding *)
Definition sign_extend i x := 
    (etable_values sign_op i) * (etable_values flag_bit i) * (etable_values padding i) 
    + x mod (etable_values modulus i).

Theorem ConversionOp_Wrap_correct : forall i st x1 xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Conversion) i = 1 ->
  etable_values is_i32_wrap_i64 i = 1 ->
  state_rel i st ->
  wasm_stack st = Wasm_int.Z_of_uint i64m x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) (Wasm_int.Z_of_uint i32m (wasm_wrap x1):: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem ConversionOp_Unsigned_Extend_correct : forall i st x1 xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Conversion) i = 1 ->
  etable_values sign_op i = 0 ->
  etable_values value_is_i32 i = 1 ->
  state_rel i st ->
  wasm_stack st = Wasm_int.Z_of_uint i32m x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (wasm_extend_u x1):: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem ConversionOp_Signed_Extend_correct : forall i st x1 xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Conversion) i = 1 ->
  etable_values sign_op i = 1 ->
  state_rel i st ->
  wasm_stack st = Wasm_int.Z_of_sint i32m x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) (sign_extend i (Wasm_int.Z_of_sint i32m x1):: xs)).
Admitted. (* Proof omitted for release, present in original source. *)
