(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.
Require Import Wasm.operations.
Require Import Wasm.type_preservation.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpStoreModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_store : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Store i.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma load_one_number_of_bytes : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    (etable_values is_one_byte i = 1 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 0)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 1 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 0)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 1 /\ etable_values is_eight_bytes i = 0)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 1).
Admitted. (* Proof omitted for release, present in original source. *)

Definition effective_address i := etable_values store_base i + etable_values opcode_store_offset i.

Lemma effective_address_division_theorem : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    Z.div_eucl (effective_address i) WASM_BLOCK_BYTE_SIZE =
    (etable_values load_block_index i, etable_values load_block_inner_pos i).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma cross_block_rem_range : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    0 <= etable_values cross_block_rem i < WASM_BLOCK_BYTE_SIZE.
Admitted. (* Proof omitted for release, present in original source. *)

Definition end_inner_byte i := 
    etable_values load_block_inner_pos i + etable_values len i - 1.

Lemma end_inner_byte_range : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    0 <= end_inner_byte i < (etable_values is_cross_block i + 1) * WASM_BLOCK_BYTE_SIZE.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma end_byte : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    Z.div_eucl (effective_address i + etable_values len i - 1) WASM_BLOCK_BYTE_SIZE = 
    (etable_values load_block_index i + etable_values is_cross_block i, etable_values cross_block_rem i).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma no_cross_block_no_heap2 : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values is_cross_block i = 0 ->
    etable_values load_value_in_heap2 i = 0.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma len_modulus_range : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values len_modulus i = 2^8
 \/ etable_values len_modulus i = 2^16
 \/ etable_values len_modulus i = 2^32
 \/ etable_values len_modulus i = 2^64.
Admitted. (* Proof omitted for release, present in original source. *)



Lemma load_tailing_range : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    0 <= etable_values load_tailing i < etable_values lookup_pow_modulus i.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma len_modulus_and_len : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values len_modulus i = 2^(etable_values len i * 8).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma load_picked_upper_bits_four_bytes_case : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values is_four_bytes i = 1 ->
    etable_values load_picked_u16_cells_le_2 i = 0 /\
    etable_values load_picked_u16_cells_le_3 i = 0.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma load_picked_length_four_bytes_case : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values is_four_bytes i = 1 ->
    0 <= etable_values load_picked_u64_cell i < 2^32.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma load_picked_length_two_bytes_case : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values is_two_bytes i = 1 ->
    0 <= etable_values load_picked_u64_cell i < 2^16.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma load_picked_length_one_byte_case : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values is_one_byte i = 1 ->
    0 <= etable_values load_picked_u64_cell i < 2^8.
Admitted. (* Proof omitted for release, present in original source. *)

(* Loaded value has the correct number of bytes *)
Lemma load_size : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    0 <= etable_values load_picked_u64_cell i < etable_values len_modulus i.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma memory_pages_not_exceeded : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values load_block_index i + etable_values is_cross_block i <
    etable_values mpages_cell i * WASM_BLOCKS_PER_PAGE.
Admitted. (* Proof omitted for release, present in original source. *)

Require Import CommonMemory.

Require Import IntegerFunctions.

Require OpLoadHelper.

Require Import FunctionalExtensionality.

Theorem Store_correct : forall i st mem v base xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Store) i = 1 ->
  state_rel i st ->
  wasm_stack st = (v::base::xs) ->
  wasm_memory st = mem ->
  exists new_mem,
    store (wasm_memory st) (Z.to_N base)
    (Z.to_N (etable_values opcode_store_offset i))
    (Memdata.encode_int (Z.to_nat (etable_values len i)) v)
    (Z.to_nat (etable_values len i)) = Some (new_mem) /\
      state_rel (i+1) (update_memory (update_stack (incr_iid st) xs) new_mem).
Admitted. (* Proof omitted for release, present in original source. *)
