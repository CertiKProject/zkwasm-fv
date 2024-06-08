(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import IntegerFunctions.
Require Import RTableModel.
Require Import RTable.
Require Import BitTableModel.

Open Scope Z_scope.
    
Import BitTableModel.
Export BitTableModel.

Section blockwise.
  Variable i : Z.
  Hypothesis i_range : 0 <= i.
  
  Hypothesis is_block_1 : bit_table_values block_sel (i+1) = 1.

  (* We can first specify all the values for block_sel, u32_sel, lookup_sel explicitly. *)

  Definition OP := bit_table_values op i.
  
  Section blockwise_bitop.
    Hypothesis op_isnt_popcnt : OP <> Popcnt_index.

  End blockwise_bitop.

  Section blockwise_bitop_and.
    Hypothesis op_is_And : OP = BitOp_And.
    
  End blockwise_bitop_and.

  Section blockwise_bitop_xor.
    Hypothesis op_is_Xor : OP = BitOp_Xor.
    
  End blockwise_bitop_xor.

  Section blockwise_bitop_or.
    Hypothesis op_is_Or : OP = BitOp_Or.
    
  End blockwise_bitop_or.
  
  Section blockwise_popcnt.

    Hypothesis op_is_popcnt : OP = Popcnt_index.

  End blockwise_popcnt.
End blockwise.

Require Import Wasm.numerics.

(** The bit_table is correct for the And operation. *)
Theorem in_bit_table_and : 
 forall (i : Z) w_l w_r,
       0 <= i ->
       value bit_table block_sel (i + 1) = 1 ->
       value bit_table op i = BitOp_And ->
       value bit_table val_l i   = Wasm_int.Z_of_uint i64m w_l ->
       value bit_table val_r i   = Wasm_int.Z_of_uint i64m w_r ->
       value bit_table val_res i = Wasm_int.Z_of_uint i64m (Wasm_int.int_and i64m w_l w_r).
Admitted. (* Proof omitted for release, present in original source. *)

(** The bit_table is correct for the Xor operation. *)
Theorem in_bit_table_xor : 
 forall (i : Z) w_l w_r,
       0 <= i ->
       value bit_table block_sel (i + 1) = 1 ->
       value bit_table op i = BitOp_Xor ->
       value bit_table val_l i   = Wasm_int.Z_of_uint i64m w_l ->
       value bit_table val_r i   = Wasm_int.Z_of_uint i64m w_r ->
       value bit_table val_res i = Wasm_int.Z_of_uint i64m (Wasm_int.int_xor i64m w_l w_r).
Admitted. (* Proof omitted for release, present in original source. *)

(** The bit_table is correct for the Or operation. *)
Theorem in_bit_table_or : 
 forall (i : Z) w_l w_r,
       0 <= i ->
       value bit_table block_sel (i + 1) = 1 ->
       value bit_table op i = BitOp_Or ->
       value bit_table val_l i   = Wasm_int.Z_of_uint i64m w_l ->
       value bit_table val_r i   = Wasm_int.Z_of_uint i64m w_r ->
       value bit_table val_res i = Wasm_int.Z_of_uint i64m (Wasm_int.int_or i64m w_l w_r).
Admitted. (* Proof omitted for release, present in original source. *)
  
(** The bit_table is correct for the Popcnt operation. *)
Theorem in_bit_table_popcnt : 
    forall (i : Z) w_l,
        0 <= i ->
        value bit_table block_sel (i + 1) = 1 ->
        value bit_table op i = Popcnt_index ->
        value bit_table val_l i   = Wasm_int.Z_of_uint i64m w_l ->
        value bit_table val_r i = 0 ->
        value bit_table val_res i = Wasm_int.Z_of_uint i64m (Wasm_int.int_popcnt i64m w_l).
Admitted. (* Proof omitted for release, present in original source. *)
