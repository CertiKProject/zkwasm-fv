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

Open Scope Z_scope.

Lemma load_one_number_of_bytes : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    (etable_values is_one_byte i = 1 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 0)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 1 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 0)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 1 /\ etable_values is_eight_bytes i = 0)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 1).
Admitted. (* Proof omitted for release, present in original source. *)


Definition effective_address i := etable_values load_base i + etable_values opcode_load_offset i.

Lemma effective_address_division_theorem : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    Z.div_eucl (effective_address i) WASM_BLOCK_BYTE_SIZE =
    (etable_values load_block_index i, etable_values load_inner_pos i).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma cross_block_rem_range : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    0 <= etable_values cross_block_rem i < WASM_BLOCK_BYTE_SIZE.
Admitted. (* Proof omitted for release, present in original source. *)

Definition end_inner_byte i := 
    etable_values load_inner_pos i + etable_values len i - 1.

Lemma end_inner_byte_range : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    0 <= end_inner_byte i < (etable_values is_cross_block i + 1) * WASM_BLOCK_BYTE_SIZE.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma end_byte : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    Z.div_eucl (effective_address i + etable_values len i - 1) WASM_BLOCK_BYTE_SIZE = 
    (etable_values load_block_index i + etable_values is_cross_block i, etable_values cross_block_rem i).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma no_cross_block_no_heap2 : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_cross_block i = 0 ->
    etable_values load_value_in_heap2 i = 0.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma len_modulus_range : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values len_modulus i = 2^8
 \/ etable_values len_modulus i = 2^16
 \/ etable_values len_modulus i = 2^32
 \/ etable_values len_modulus i = 2^64.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma len_modulus_and_len : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values len_modulus i = 2^(etable_values len i * 8).
Admitted. (* Proof omitted for release, present in original source. *)
  
Lemma load_tailing_range : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    0 <= etable_values load_tailing_u64_cell i < etable_values lookup_pow_modulus i.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma load_picked_upper_bits_four_bytes_case : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_four_bytes i = 1 ->
    etable_values load_picked_u16_cells_le_2 i = 0 /\
    etable_values load_picked_u16_cells_le_3 i = 0.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma load_picked_length_four_bytes_case : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_four_bytes i = 1 ->
    0 <= etable_values load_picked_u64_cell i < 2^32.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma load_picked_length_two_bytes_case : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_two_bytes i = 1 ->
    0 <= etable_values load_picked_u64_cell i < 2^16.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma load_picked_length_one_byte_case : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_one_byte i = 1 ->
    0 <= etable_values load_picked_u64_cell i < 2^8.
Admitted. (* Proof omitted for release, present in original source. *)

(* Loaded value has the correct number of bytes *)
Lemma load_size : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    0 <= etable_values load_picked_u64_cell i < etable_values len_modulus i.
Admitted. (* Proof omitted for release, present in original source. *)


Definition value_leading_u8 i :=
    etable_values is_one_byte i * etable_values load_picked_leading_u16_u8_low i
  + (1 - etable_values is_one_byte i) * etable_values load_picked_leading_u16_u8_high i.

Definition sign_extension i :=
  (* If loaded value is I64 but not 8 bytes, need at least 4 byte extension*)
    (1 - etable_values is_eight_bytes i) * (1 - etable_values is_i32 i) * 0xFFFFFFFF00000000
  (* If one byte, need 3 byte or 7 byte extension *)  
  + etable_values is_one_byte i * 0xFFFFFF00
  (* If two bytes, need 2 or 6 byte extension *)
  + etable_values is_two_bytes i * 0xFFFF0000.
  (* If four bytes, need 4 or 0 byte extension. No extension for 8 bytes *)

(* Result is either loaded value or sign-extended laoded value *)
Theorem loaded_result_is_correct : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values res i =
    etable_values load_picked_u64_cell i + 
    (* only sign extend if op is signed and loaded value is negative *)
    (etable_values is_sign i) * (etable_values load_picked_flag i) * sign_extension i.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma memory_pages_not_exceeded : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values load_block_index i + etable_values is_cross_block i <
    etable_values mpages_cell i * WASM_BLOCKS_PER_PAGE.
Admitted. (* Proof omitted for release, present in original source. *)


Lemma load_load_picked : forall i mem,
  0 <= i ->
  etable_values (ops_cell Load) i = 1 ->  
  heap_rel (heap_map (etable_values eid_cell i)) (etable_values mpages_cell i) (etable_values maximal_memory_pages_cell i) mem ->
  exists bs,
    load mem
      (Z.to_N (etable_values load_base i))
      (Z.to_N (etable_values opcode_load_offset i))
      (Z.to_nat (etable_values len i))  = Some bs /\
  etable_values load_picked_u64_cell i = Memdata.decode_int bs.
Admitted. (* Proof omitted for release, present in original source. *)
