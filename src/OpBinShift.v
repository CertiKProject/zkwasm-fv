(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpBinShiftModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_bin_shift : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct BinShift i.
Admitted. (* Proof omitted for release, present in original source. *)

Definition shr_u l r modulus := 
    Z.shiftr l (r mod modulus).

Definition shr_s l r modulus := 
  match Z.shiftr l (modulus - 1) with
  | 1 => Z.shiftr l (r mod modulus) 
          + Z.shiftl (2^(r mod modulus) - 1) (modulus - r mod modulus)
  | _ => Z.shiftr l (r mod modulus)
  end.

Definition rotr l r modulus :=
    Z.shiftr l (r mod modulus) +
    Z.shiftl (l mod 2^(r mod modulus)) (modulus - (r mod modulus)).

Definition shl l r modulus :=
    (Z.shiftl l (r mod modulus)) mod 2^modulus.

Definition rotl l r modulus := 
    (Z.shiftl l (r mod modulus)) mod 2^modulus 
    + Z.shiftr l (modulus - (r mod modulus)).

Theorem BinShift_Shr_U_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_shr_u i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) (shr_u xl xr (64 - etable_values is_i32 i * 32) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem BinShift_Shr_S_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_shr_s i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) (shr_s xl xr (64 - etable_values is_i32 i * 32) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem BinShift_Rotr_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_rotr i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) (rotr xl xr (64 - etable_values is_i32 i * 32) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem BinShift_Shl_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_shl i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) (shl xl xr (64 - etable_values is_i32 i * 32) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem BinShift_Rotl_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_rotl i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) (rotl xl xr (64 - etable_values is_i32 i * 32) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)
