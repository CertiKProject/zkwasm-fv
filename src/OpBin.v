(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpBinModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.
Require Import MTableModel.

Open Scope Z_scope.

Theorem opcode_mops_correct_bin : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Bin i.
Admitted. (* Proof omitted for release, present in original source. *)

Definition abs x modulus :=
    match Z.shiftr x (modulus - 1) =? 1 with
    | true => 2^modulus - x
    | false => x
    end.

Definition div_s l r modulus :=
  match Z.lxor (Z.shiftr l (modulus - 1)) (Z.shiftr r (modulus - 1)) =? 1 with
  (* when abs l / abs r = 0, result should be 0 *)
  | true => (2^modulus - (abs l modulus) / (abs r modulus)) mod 2^modulus
  | false => (abs l modulus) / (abs r modulus)
  end.

Definition rem_s l r modulus := 
    match Z.shiftr l (modulus - 1) =? 0 with
    | true => (abs l modulus) mod (abs r modulus)
    (* if abs l mod abs r = 0, result is 0 *)
    | false => (2^modulus - ((abs l modulus) mod (abs r modulus))) mod 2^modulus
    end.

Theorem Bin_Add_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_add i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) ((xl + xr) mod 2^(64 - etable_values is_i32 i * 32):: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem Bin_Sub_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_sub i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) ((xl - xr) mod 2^(64 - etable_values is_i32 i * 32):: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem Bin_Mul_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_mul i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) ((xl * xr) mod 2^(64 - etable_values is_i32 i * 32):: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem Bin_Div_U_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_u i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) ((xl / xr):: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem Bin_Rem_U_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_rem_u i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) ((xl mod xr):: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem Bin_Div_S_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_s i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) (div_s xl xr (64 - etable_values is_i32 i * 32):: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem Bin_Rem_S_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_rem_s i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) (rem_s xl xr (64 - etable_values is_i32 i * 32):: xs)).
Admitted. (* Proof omitted for release, present in original source. *)
