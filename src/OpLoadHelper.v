(* Copyright (C) CertiK 2024-2026 *)

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
Proof.
  intros i Hrange.
  pose(Hlength := op_load_length i Hrange).
  simpl in Hlength.
  destruct Hlength as [? _].
  replace (i+0) with i in * by lia.
  pose(Honebit := is_one_byte_bit i).
  pose(Htwobit := is_two_bytes_bit i).
  pose(Hfourbit := is_four_bytes_bit i).
  pose(Heightbit := is_eight_bytes_bit i).
  lia.
Qed.

Definition bytes_loaded i := 
    etable_values is_one_byte i * 1
  + etable_values is_two_bytes i * 2
  + etable_values is_four_bytes i * 4
  + etable_values is_eight_bytes i * 8.

Lemma bytes_loaded_range : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    bytes_loaded i = 1
 \/ bytes_loaded i = 2
 \/ bytes_loaded i = 4
 \/ bytes_loaded i = 8.
Proof.
  intros i Hrange.
  pose(H := load_one_number_of_bytes i Hrange).
  unfold bytes_loaded.
  lia.
Qed.

Lemma length_is_correct : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values len i = bytes_loaded i.
Proof.
  intros i Hrange.
  pose(Hlen := op_load_len_gate i Hrange).
  simpl in Hlen.
  destruct Hlen as [? _].
  replace (i+0) with i in * by lia.
  unfold bytes_loaded.
  pose(load_one_number_of_bytes i Hrange).
  lia.
Qed.

Lemma load_one_number_of_bytes_len : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    (etable_values is_one_byte i = 1 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 0 /\ etable_values len i = 1)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 1 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 0 /\ etable_values len i = 2)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 1 /\ etable_values is_eight_bytes i = 0 /\ etable_values len i = 4)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 1 /\ etable_values len i = 8).
Proof.
  intros i Hrange Hops.
  rewrite length_is_correct by auto.
  unfold bytes_loaded.
  destruct (load_one_number_of_bytes i Hrange Hops) as
    [ [? [? [? ?]]] | [[? [? [? ?]]] | [[? [? [? ?]]] | [? [? [? ?]]]]]];
    rewrite H, H0, H1, H2;
    lia.
Qed.

Lemma load_tailing_diff_range : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    0 <= etable_values load_tailing_diff_u64_cell i < 2^64.
Proof.
  intros i.
  pose(Hloadtailingdiffu64 := load_tailing_diff_U64 i).
  simpl in Hloadtailingdiffu64.
  pose(Hloadtailingdiffu16cells := load_tailing_diff_U16_cells).
  destruct Hloadtailingdiffu16cells as [? [? [? ?]]].
  destruct(H i).
  destruct(H0 i).
  destruct(H1 i).
  destruct(H2 i).
  simpl in *.
  lia.
Qed.

Lemma load_tailing_length : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values load_tailing_u64_cell i < etable_values lookup_pow_modulus i.
Proof.
  intros i Hrange.
  pose(Hpickvalue := op_load_pick_value i Hrange).
  simpl in Hpickvalue.
  destruct Hpickvalue as [_ [_ [? _]]].
  replace (i+0) with i in * by lia.
  pose(Hloadtailingdiff := load_tailing_diff_range i).
  lia.
Qed.

Lemma load_inner_pos_bound : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    0 <= etable_values load_inner_pos i < WASM_BLOCK_BYTE_SIZE.
Proof.
  intros i Hrange.
  pose(H := op_load_load_block_index_gate i Hrange).
  simpl in H.
  destruct H as [_ [? _]].
  replace (i+0) with i in * by lia.
  pose(Hdiffrange := load_inner_pos_diff_U8 i).
  pose(Hinnerrange := load_inner_pos_U8 i).
  unfold WASM_BLOCK_BYTE_SIZE.
  lia.
Qed.

Definition effective_address i := etable_values load_base i + etable_values opcode_load_offset i.

Lemma effective_address_value : forall i,
    0 <= i -> 
    etable_values (ops_cell Load) i = 1 ->
    effective_address i = 
    etable_values load_block_index i * WASM_BLOCK_BYTE_SIZE + etable_values load_inner_pos i.
Proof.
  intros i Hrange.
  pose(H := op_load_load_block_index_gate i Hrange).
  simpl in H.
  destruct H as [? [_ _]].
  replace (i+0) with i in * by lia.
  unfold effective_address.
  lia.
Qed.

Lemma effective_address_division_theorem : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    Z.div_eucl (effective_address i) WASM_BLOCK_BYTE_SIZE =
    (etable_values load_block_index i, etable_values load_inner_pos i).
Proof.
  intros i Hrange Hops.
  rewrite(Zaux.Zdiv_eucl_unique _ _).
  assert(Hquot : etable_values load_block_index i = effective_address i / WASM_BLOCK_BYTE_SIZE).
  rewrite(effective_address_value i Hrange Hops).
  rewrite(Z.div_add_l _ _ _).
  rewrite(Z.div_small _ _).
  lia.
  apply(load_inner_pos_bound i Hrange Hops).
  unfold WASM_BLOCK_BYTE_SIZE.
  congruence.
  rewrite Hquot.
  assert(Hrem : etable_values load_inner_pos i = effective_address i mod WASM_BLOCK_BYTE_SIZE).
  rewrite(effective_address_value i Hrange Hops).
  replace(etable_values load_block_index i * WASM_BLOCK_BYTE_SIZE + etable_values load_inner_pos i)
  with (etable_values load_inner_pos i + etable_values load_block_index i * WASM_BLOCK_BYTE_SIZE).
  rewrite(Z_mod_plus _ _ _).
  rewrite(Z.mod_small _ _).
  reflexivity.
  apply(load_inner_pos_bound i Hrange Hops).
  unfold WASM_BLOCK_BYTE_SIZE.
  reflexivity.
  lia.
  rewrite Hrem.
  reflexivity.
Qed.

Lemma cross_block_rem_range : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    0 <= etable_values cross_block_rem i < WASM_BLOCK_BYTE_SIZE.
Proof.
  intros i Hrange.
  pose(H := op_load_cross_bloc i Hrange).
  simpl in H.
  destruct H as [_ [? _]].
  replace (i+0) with i in * by lia.
  pose(cross_block_rem_diff_common i).
  unfold WASM_BLOCK_BYTE_SIZE.
  pose(cross_block_rem_common i).
  lia.
Qed.

Definition end_inner_byte i := 
    etable_values load_inner_pos i + etable_values len i - 1.

Lemma end_inner_byte_range : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    0 <= end_inner_byte i < (etable_values is_cross_block i + 1) * WASM_BLOCK_BYTE_SIZE.
Proof.
  intros i Hrange.
  pose(H := op_load_cross_bloc i Hrange).
  simpl in H.
  destruct H as [? [_ _]].
  replace (i+0) with i in * by lia.
  pose(Hbit := is_cross_block_bit i).
  unfold end_inner_byte.
  pose(Hremrange := cross_block_rem_range i Hrange).
  destruct Hbit as [? | ?]; [lia | lia].
Qed.

Lemma end_byte : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    Z.div_eucl (effective_address i + etable_values len i - 1) WASM_BLOCK_BYTE_SIZE = 
    (etable_values load_block_index i + etable_values is_cross_block i, etable_values cross_block_rem i).
Proof.
  intros i Hrange Hops.
  rewrite(Zaux.Zdiv_eucl_unique _ _).
  rewrite(effective_address_value i Hrange Hops).
  pose(H := op_load_cross_bloc i Hrange).
  simpl in H.
  replace (i+0) with i in H by lia.
  destruct H as [H _].
  pose(Hremrange := cross_block_rem_range i Hrange Hops).
  unfold WASM_BLOCK_BYTE_SIZE in *.
  replace(etable_values load_block_index i * 8 + etable_values load_inner_pos i + etable_values len i - 1)
  with (etable_values load_block_index i * 8 + (etable_values load_inner_pos i + etable_values len i - 1)) by lia.
  rewrite(Z.div_add_l _ _ _) by congruence.
  replace(etable_values load_block_index i * 8 + (etable_values load_inner_pos i + etable_values len i - 1))
  with ((etable_values load_inner_pos i + etable_values len i - 1) + etable_values load_block_index i * 8) by lia.
  rewrite(Z_mod_plus _ _ _) by lia.
  replace(etable_values load_inner_pos i + etable_values len i - 1)
  with (etable_values is_cross_block i * 8 + etable_values cross_block_rem i) by lia.
  rewrite(Z.div_add_l _ _ _) by congruence.
  rewrite(Z.div_small _ _).
  replace(etable_values is_cross_block i * 8 + etable_values cross_block_rem i)
  with (etable_values cross_block_rem i + etable_values is_cross_block i * 8) by lia.
  rewrite(Z_mod_plus _ _ _) by lia.
  rewrite(Z.mod_small _ _).
  replace(etable_values is_cross_block i + 0) with (etable_values is_cross_block i) by lia.
  reflexivity.
  assumption.
  assumption.
Qed.

Lemma no_cross_block_no_heap2 : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_cross_block i = 0 ->
    etable_values load_value_in_heap2 i = 0.
Proof.
  intros i Hrange.
  pose(H := op_load_cross_bloc i Hrange).
  simpl in H.
  destruct H as [_ [_ [? _]]].
  replace (i+0) with i in * by lia.
  lia.
Qed.

Lemma len_modulus_range : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values len_modulus i = 2^8
 \/ etable_values len_modulus i = 2^16
 \/ etable_values len_modulus i = 2^32
 \/ etable_values len_modulus i = 2^64.
Proof.
  intros i Hrange.
  pose(H := op_load_pick_value i Hrange).
  simpl in *.
  destruct H as [? _].
  replace (i+0) with i in * by lia.
  pose(Hbytes := load_one_number_of_bytes i).
  lia.
Qed.

Lemma len_modulus_and_len : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values len_modulus i = 2^(etable_values len i * 8).
Proof.
  intros i Hrange Hops.
  pose(Hmodulus := op_load_pick_value i Hrange).
  pose(Hlen := op_load_len_gate i Hrange).
  simpl in *.
  replace(i+0) with i in * by lia.
  destruct Hmodulus as [Hmodulus _].
  pose(Hbytes := load_one_number_of_bytes i Hrange Hops).
  destruct Hbytes as [Hone | [Htwo | [Hfour | Height]]].
  - assert(etable_values len i = 1). lia.
    rewrite H. lia.
  - assert(etable_values len i = 2). lia.
    rewrite H. lia.
  - assert(etable_values len i = 4). lia.
    rewrite H. lia.
  - assert(etable_values len i = 8). lia.
    rewrite H. lia.
Qed.
  
Lemma load_tailing_range : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    0 <= etable_values load_tailing_u64_cell i < etable_values lookup_pow_modulus i.
Proof.
  intros i Hrange.
  pose(H := op_load_pick_value i Hrange).
  simpl in H.
  destruct H as [_ [_ [? _]]].
  replace (i+0) with i in * by lia.
  pose(Hdiffrange := load_tailing_diff_range i Hrange).
  pose(Htailu64 := load_tailing_U64 i).
  pose(Htailu16 := load_tailing_U16_cells).
  destruct Htailu16 as [? [? [? ?]]].
  destruct (H0 i).
  destruct (H1 i).
  destruct (H2 i).
  destruct (H3 i).
  simpl in *.
  lia.
Qed.

Lemma load_picked_upper_bits_four_bytes_case : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_four_bytes i = 1 ->
    etable_values load_picked_u16_cells_le_2 i = 0 /\
    etable_values load_picked_u16_cells_le_3 i = 0.
Proof.
  intros i Hrange Hfour.
  pose(H := op_load_pick_value_size_check i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  destruct H as [? _].
  rewrite Hfour in H.
  pose(Hu16 := load_picked_U16_cells).
  destruct Hu16 as [_ [_ [? ?]]].
  destruct (H0 i) as [? _].
  destruct (H1 i) as [? _].
  lia.
Qed.

Lemma load_picked_length_four_bytes_case : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_four_bytes i = 1 ->
    0 <= etable_values load_picked_u64_cell i < 2^32.
Proof.
  intros i Hrange Hops Hfour.
  pose(H := op_load_pick_value_size_check i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  destruct H as [? _].
  rewrite Hfour in H.
  pose(Hu64 := load_picked_U64 i).
  pose(Hupper := load_picked_upper_bits_four_bytes_case i Hrange Hops Hfour).
  destruct Hupper.
  rewrite H0, H1 in Hu64.
  simpl in Hu64.
  pose(Hu16 := load_picked_U16_cells).
  destruct Hu16 as [? [? _]].
  destruct (H2 i).
  destruct (H3 i).
  simpl in H5, H7.
  lia.
Qed.

Lemma load_picked_leading_is_upper_two_bytes : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    (etable_values is_one_byte i = 1
 \/ etable_values is_two_bytes i = 1 ->
    etable_values load_picked_leading_u16 i = etable_values load_picked_u16_cells_le_0 i)
 /\ (etable_values is_four_bytes i = 1 ->
    etable_values load_picked_leading_u16 i = etable_values load_picked_u16_cells_le_1 i)
 /\ (etable_values is_eight_bytes i = 1 ->
    etable_values load_picked_leading_u16 i = etable_values load_picked_u16_cells_le_3 i).
Proof.
  intros i Hrange. 
  pose(H := op_load_pick_u16_decompose1 i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  destruct H as [? _].
  pose(load_one_number_of_bytes i Hrange).
  split.
  lia.
  split.
  lia.
  lia.
Qed.

Lemma load_picked_leading_is_two_bytes : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    0 <= etable_values load_picked_leading_u16 i < 2^16.
Proof.
  intros i Hrange Hops.
  pose(H := load_picked_leading_is_upper_two_bytes i Hrange Hops).
  destruct H as [H2 [H4 H8]].
  pose(Hbytes := load_one_number_of_bytes i Hrange Hops).
  pose(Hu16 := load_picked_U16_cells).
  destruct Hbytes.
  - destruct H as [? _].
    assert (etable_values load_picked_leading_u16 i = etable_values load_picked_u16_cells_le_0 i).
    apply H2. left. apply H.
    destruct Hu16 as [? _].
    destruct (H1 i).
    simpl in H5.
    lia.
  destruct H. 
  - destruct H as [_ [? _]].
    assert (etable_values load_picked_leading_u16 i = etable_values load_picked_u16_cells_le_0 i).
    apply H2. right. apply H.
    destruct Hu16 as [? _].
    destruct (H1 i).
    simpl in H5.
    lia.
  destruct H.
  - destruct H as [_ [_ [? _]]].
    apply H4 in H.
    destruct Hu16 as [_ [? _]].
    destruct (H0 i).
    simpl in H3.
    lia.
  destruct H as [_ [_ [_ ?]]].
  apply H8 in H.
  destruct Hu16 as [_ [_ [_ ?]]].
  destruct (H0 i).
  simpl in H3.
  lia.
Qed.

Lemma load_picked_upper_bits_two_bytes_case : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_two_bytes i = 1 ->
    etable_values load_picked_u16_cells_le_1 i = 0 /\
    etable_values load_picked_u16_cells_le_2 i = 0 /\
    etable_values load_picked_u16_cells_le_3 i = 0.
Proof.
  intros i Hrange Hops Htwo.
  pose(Hupper := load_picked_leading_is_upper_two_bytes i Hrange Hops).
  destruct Hupper as [? _].
  assert(etable_values load_picked_leading_u16 i = etable_values load_picked_u16_cells_le_0 i).
  apply H. right. apply Htwo.
  pose(Hsize := op_load_pick_value_size_check i Hrange).
  simpl in Hsize.
  destruct Hsize as [_ [? _]].
  replace (i+0) with i in * by lia.
  rewrite Htwo in H1.
  assert(etable_values load_picked_u64_cell i = etable_values load_picked_u16_cells_le_0 i).
  lia.
  pose(Hu64 := load_picked_U64 i).
  pose(Hu16 := load_picked_U16_cells).
  destruct Hu16 as [? [? [? ?]]].
  destruct (H3 i). destruct (H4 i). destruct (H5 i). destruct (H6 i).
  simpl in *.
  lia.
Qed.

Lemma load_picked_length_two_bytes_case : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_two_bytes i = 1 ->
    0 <= etable_values load_picked_u64_cell i < 2^16.
Proof. 
  intros i Hrange Hops Htwo.
  pose(H := load_picked_upper_bits_two_bytes_case i Hrange Hops Htwo).
  simpl in H.
  replace (i+0) with i in * by lia.
  pose(Hu64 := load_picked_U64 i).
  simpl in Hu64.
  pose(Hu16 := load_picked_U16_cells).
  destruct Hu16 as [? _].
  destruct (H0 i).
  simpl in H2.
  lia.
Qed.

Lemma load_picked_leading_u16_decomposition : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values load_picked_leading_u16 i =
    etable_values load_picked_leading_u16_u8_high i * 2^8 +
    etable_values load_picked_leading_u16_u8_low i.
Proof.
  intros i Hrange Hops.
  pose(H := op_load_pick_u16_decompose2 i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Lemma decompose_load_picked_leading_u16_high : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    Z.shiftr (etable_values load_picked_leading_u16 i) 8 =
    etable_values load_picked_leading_u16_u8_high i.
Proof.
  intros i Hrange Hops.
  pose(H := op_load_pick_u16_decompose2 i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  destruct H as [? _].
  pose(HlowU8 := load_picked_leading_u16_u8_low_U8 i).
  rewrite(load_picked_leading_u16_decomposition i Hrange Hops).
  rewrite(Z.shiftr_div_pow2 _ _) by lia.
  rewrite(Z.div_add_l _ _ _) by lia.
  rewrite(Z.div_small _ _) by apply HlowU8.
  lia.
Qed.

Lemma load_picked_leading_u16_u8_low_range : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    0 <= etable_values load_picked_leading_u16_u8_low i < 2^8.
Proof.
  intros i Hrange Hops.
  pose(H := load_picked_leading_u16_u8_low_U8 i).
  assumption.
Qed.

Lemma load_picked_length_one_byte_case : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_one_byte i = 1 ->
    0 <= etable_values load_picked_u64_cell i < 2^8.
Proof.
  intros i Hrange Hops Hone.
  pose(H := op_load_pick_value_size_check i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [_ [H _]]].
  pose(Hlow := load_picked_leading_u16_u8_low_range i Hrange Hops).
  lia.
Qed.

(* Loaded value has the correct number of bytes *)
Lemma load_size : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    0 <= etable_values load_picked_u64_cell i < etable_values len_modulus i.
Proof.
  intros i Hrange Hops.
  pose(Hlen := op_load_pick_value i Hrange).
  simpl in Hlen.
  replace(i+0) with i in * by lia.
  destruct Hlen as [Hlen _].
  pose(Hbytes := load_one_number_of_bytes i Hrange Hops).
  destruct Hbytes as [Hone | Hbytes].
  - replace(etable_values len_modulus i) with (2^8) by lia.
    destruct Hone as [Hone _].
    apply(load_picked_length_one_byte_case i Hrange Hops Hone).
  destruct Hbytes as [Htwo | Hbytes].
  - replace(etable_values len_modulus i) with (2^16) by lia.
    destruct Htwo as [_ [Htwo _]].
    apply(load_picked_length_two_bytes_case i Hrange Hops Htwo).
  destruct Hbytes as [Hfour | Height].
  - replace(etable_values len_modulus i) with (2^32) by lia.
    destruct Hfour as [_ [_ [Hfour _]]].
    apply(load_picked_length_four_bytes_case i Hrange Hops Hfour).
  - pose(Hu64 := load_picked_U64 i).
    pose(Hu16 := load_picked_U16_cells).
    destruct Hu16 as [H0 [H1 [H2 H3]]].
    specialize (H0 i).
    specialize (H1 i).
    specialize (H2 i).
    specialize (H3 i).
    lia.
Qed.

Definition heap_value i := 
    etable_values load_value_in_heap1 i 
  + etable_values load_value_in_heap2 i * 2^64.

Lemma heap_value_decomposition : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    heap_value i =
    etable_values load_leading_u64_cell i * etable_values lookup_pow_modulus i * etable_values len_modulus i
    + etable_values load_picked_u64_cell i * etable_values lookup_pow_modulus i
    + etable_values load_tailing_u64_cell i.
Proof.
  intros i Hrange Hops.
  pose(H := op_load_pick_value i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  unfold heap_value.
  lia.
Qed.

Lemma lookup_pow_values : forall i,
    0 <= i ->
    etable_values lookup_pow_power i <> 0 ->
    128 <= etable_values lookup_pow_power i < 256 /\
    etable_values lookup_pow_modulus i = 2^(etable_values lookup_pow_power i - 128).
Proof.
  intros i Hrange Hnonzero.
  assert (Hin:=ETableModel.c8d i Hrange).
  apply RTable.in_op_table_power in Hin; auto.
Qed.

Lemma load_picked_starts_at_load_inner_pos : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    Z.shiftr (heap_value i) (etable_values load_inner_pos i * 8) =
    etable_values load_leading_u64_cell i * etable_values len_modulus i
    + etable_values load_picked_u64_cell i.
intros i Hrange Hops.
  rewrite(heap_value_decomposition i Hrange Hops).
  pose(Hinner := load_inner_pos_bound i Hrange Hops).
  rewrite(Z.shiftr_div_pow2 _ _) by lia.
  pose(Hpow := op_load_pos_modulus i Hrange).
  simpl in Hpow.
  replace(i+0) with i in * by lia.
  assert (Hpower_lookup_nonzero : etable_values lookup_pow_power i <> 0).
  {
    assert (inner_is_8 := load_inner_pos_U8 i).
    lia.
  }
  replace(etable_values load_inner_pos i * 8) with (etable_values lookup_pow_power i - 128) by lia.
  pose(Hlookup := lookup_pow_values i Hrange Hpower_lookup_nonzero).
  replace(2^(etable_values lookup_pow_power i - 128)) with (etable_values lookup_pow_modulus i) by lia.
  pose(Htail := load_tailing_range i Hrange Hops).
  replace(etable_values load_leading_u64_cell i * etable_values lookup_pow_modulus i * etable_values len_modulus i +
  etable_values load_picked_u64_cell i * etable_values lookup_pow_modulus i +
  etable_values load_tailing_u64_cell i) with
  ((etable_values load_leading_u64_cell i * etable_values len_modulus i +
  etable_values load_picked_u64_cell i) * etable_values lookup_pow_modulus i +
  etable_values load_tailing_u64_cell i) by lia.
  rewrite(Z.div_add_l _ _ _) by lia.
  rewrite(Z.div_small _ _) by apply Htail.
  lia.
Qed.

Lemma load_picked_ends_at_is_cross_block_plus_cross_block_rem_plus_one : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    Z.shiftr (heap_value i) ((etable_values is_cross_block i * WASM_BLOCK_BYTE_SIZE + etable_values cross_block_rem i + 1) * 8) =
    etable_values load_leading_u64_cell i.
Proof.
  intros i Hrange Hops.
  pose(Hcross := op_load_cross_bloc i Hrange).
  simpl in Hcross.
  replace(i+0) with i in * by lia.
  destruct Hcross as [Hcross _].
  replace((etable_values is_cross_block i * WASM_BLOCK_BYTE_SIZE + etable_values cross_block_rem i + 1) * 8)
  with ((etable_values load_inner_pos i * 8) + etable_values len i * 8) by lia.
  pose(Hbytes := bytes_loaded_range i Hrange Hops).
  pose(Hlen := length_is_correct i Hrange Hops).
  rewrite <- (Z.shiftr_shiftr _ _ _) by lia.
  rewrite (load_picked_starts_at_load_inner_pos i Hrange Hops).
  rewrite(Z.shiftr_div_pow2 _ _) by lia.
  rewrite (len_modulus_and_len i Hrange Hops).
  rewrite(Z.div_add_l _ _ _) by lia.
  rewrite <- (len_modulus_and_len i Hrange Hops).
  rewrite(Z.div_small _ _) by apply (load_size i Hrange Hops).
  lia.
Qed.

Lemma load_picked_from_heap_value : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values load_picked_u64_cell i = 
    (Z.shiftr (heap_value i) (etable_values load_inner_pos i * 8)) mod (etable_values len_modulus i).
Proof.
  intros i Hrange Hops.
  rewrite(load_picked_starts_at_load_inner_pos i Hrange Hops).
  pose(load_size i Hrange Hops).
  rewrite Z.add_comm.
  rewrite Z_mod_plus by lia.
  rewrite Z.mod_small; auto.
Qed.

Lemma load_picked_leading_u8_rem_range : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    0 <= etable_values load_picked_leading_u8_rem i < 128.
Proof.
  intros i Hrange Hops.
  pose(H := op_load_flag i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [H _]].
  pose(Hdiff := load_picked_leading_u8_rem_diff_common i).
  pose(Hrem := load_picked_leading_u8_rem_common i).
  lia.
Qed.

Definition value_leading_u8 i :=
    etable_values is_one_byte i * etable_values load_picked_leading_u16_u8_low i
  + (1 - etable_values is_one_byte i) * etable_values load_picked_leading_u16_u8_high i.

Lemma value_leading_u8_decomposition : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    value_leading_u8 i = etable_values load_picked_flag i * 128 
    + etable_values load_picked_leading_u8_rem i.
Proof.
  intros i Hrange Hops.
  unfold value_leading_u8.
  pose(H := op_load_flag i Hrange).
  simpl in *.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Lemma value_leading_u8_range : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    0 <= value_leading_u8 i < 2^8.
Proof.
  intros i Hrange Hops.
  rewrite(value_leading_u8_decomposition i Hrange Hops).
  pose(Hrem := load_picked_leading_u8_rem_range i Hrange Hops).
  pose(Hflag := load_picked_flag_bit i).
  lia.
Qed.

Lemma load_picked_flag_is_leading_bit : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    Z.shiftr (value_leading_u8 i) 7 = etable_values load_picked_flag i.
Proof.
  intros i Hrange Hops.
  rewrite(value_leading_u8_decomposition i Hrange Hops).
  rewrite(Z.shiftr_div_pow2 _ _) by lia.
  rewrite(Z.div_add_l _ _ _) by lia.
  pose(Hrem := load_picked_leading_u8_rem_range i Hrange Hops).
  rewrite(Z.div_small _ _) by lia.
  lia.
Qed.

Lemma degree_helper_value : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values degree_helper i = 
    etable_values load_picked_flag i * etable_values is_sign i.
Proof.
  intros i Hrange Hops.
  pose(H := op_load_extension i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Definition sign_extension i :=
  (* If loaded value is I64 but not 8 bytes, need at least 4 byte extension*)
    (1 - etable_values is_eight_bytes i) * (1 - etable_values is_i32 i) * 0xFFFFFFFF00000000
  (* If one byte, need 3 byte or 7 byte extension *)  
  + etable_values is_one_byte i * 0xFFFFFF00
  (* If two bytes, need 2 or 6 byte extension *)
  + etable_values is_two_bytes i * 0xFFFF0000.
  (* If four bytes, need 4 or 0 byte extension. No extension for 8 bytes *)

Lemma leading_bit_8 : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_one_byte i = 1 ->
    (etable_values load_picked_flag i) = (Z.shiftr (etable_values load_picked_u64_cell i) 7).
Proof.
  intros i Hrange Hops Hone.
  pose(H := op_load_pick_value_size_check i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [_ [H _]]].
  rewrite Hops, Hone in H.
  replace (etable_values load_picked_u64_cell i) with (etable_values load_picked_leading_u16_u8_low i) by lia.
  clear H.
  rewrite  <- load_picked_flag_is_leading_bit by auto.
  unfold value_leading_u8.
  rewrite Hone.
  replace ((1 * etable_values load_picked_leading_u16_u8_low i +
              (1 - 1) * etable_values load_picked_leading_u16_u8_high i))
            with (etable_values load_picked_leading_u16_u8_low i) by lia.
  reflexivity.
Qed.
  
Lemma leading_bit_16 : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_two_bytes i = 1 ->
    (etable_values load_picked_flag i) = (Z.shiftr (etable_values load_picked_u64_cell i) 15).
Proof.
  intros i Hrange Hops Htwo.
  pose(H := load_picked_upper_bits_two_bytes_case i Hrange Hops Htwo).
  destruct H as [Hcell1 [Hcell2 Hcell3]].  
  pose(Hu64 := load_picked_U64 i).
  simpl in Hu64.
  rewrite Hcell1, Hcell2, Hcell3 in Hu64.
  replace (etable_values load_picked_u64_cell i) with (etable_values load_picked_u16_cells_le_0 i) by lia.
  clear Hcell1 Hcell2 Hcell3 Hu64.
  rewrite  <- load_picked_flag_is_leading_bit by auto.
  unfold value_leading_u8.
  assert (Hone : etable_values is_one_byte i = 0).
  {
    destruct (load_one_number_of_bytes  i Hrange Hops) as [[? [? [? ?]]] | [[? [? [? ?]]] | [[? [? [? ?]]] | [? [? [? ?]]]]]];
    congruence.
  }    
  rewrite Hone.
  replace ((0 * etable_values load_picked_leading_u16_u8_low i +
              (1 - 0) * etable_values load_picked_leading_u16_u8_high i))
    with (etable_values load_picked_leading_u16_u8_high i) by lia.
  rewrite <- decompose_load_picked_leading_u16_high by auto.
  rewrite Z.shiftr_shiftr by lia.
  change (8+7) with 15.

  destruct (load_picked_leading_is_upper_two_bytes i Hrange Hops) as [H [_ _]].
  rewrite H by auto.
  reflexivity.
Qed.

Lemma shiftr_31_plus: forall x y,
    0 <= x < 2 ^ 16 ->
    0 <= y < 2 ^ 16 ->
    Z.shiftr (x + y * Z.pow_pos 2 16) 31 = Z.shiftr y 15.
Proof.
  intros x y Hxrange Hyrange.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (Z.pow_pos 2 16) with (2 ^ 16).
  change (2 ^ 31) with (2^16 * 2^15).
  rewrite <- Zdiv_Zdiv by lia.
  rewrite Z_div_plus_full by lia.
  replace (x / 2 ^ 16) with 0.
  2: {
    rewrite Zdiv_small; lia.
  }
  replace (0+y) with y by lia.
  reflexivity.
Qed.

Lemma leading_bit_32 : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_four_bytes i = 1 ->
    (etable_values load_picked_flag i) = (Z.shiftr (etable_values load_picked_u64_cell i) 31).
Proof.
  intros i Hrange Hops Hfour.
  pose(H := load_picked_upper_bits_four_bytes_case i Hrange Hops Hfour).
  destruct H as [Hcell2 Hcell3].
  pose(Hu64 := load_picked_U64 i).
  simpl in Hu64.
  rewrite Hcell2, Hcell3 in Hu64.
  replace (etable_values load_picked_u64_cell i) with
    (etable_values load_picked_u16_cells_le_0 i
     + etable_values load_picked_u16_cells_le_1 i * Z.pow_pos 2 16) by lia.
  clear Hcell2 Hcell3 Hu64.
  replace (Z.shiftr
    (etable_values load_picked_u16_cells_le_0 i +
       etable_values load_picked_u16_cells_le_1 i * Z.pow_pos 2 16) 31)
    with (Z.shiftr (etable_values load_picked_u16_cells_le_1 i) 15).
  2: {
    destruct load_picked_U16_cells as [is16_0 [is16_1 _]].
    specialize (is16_0 i).
    specialize (is16_1 i).
    rewrite shiftr_31_plus by auto.
    reflexivity.
  }  
  rewrite  <- load_picked_flag_is_leading_bit by auto.
  unfold value_leading_u8.
  assert (Hone : etable_values is_one_byte i = 0).
  {
    destruct (load_one_number_of_bytes  i Hrange Hops) as [[? [? [? ?]]] | [[? [? [? ?]]] | [[? [? [? ?]]] | [? [? [? ?]]]]]];
    congruence.
  }    
  rewrite Hone.
  replace ((0 * etable_values load_picked_leading_u16_u8_low i +
              (1 - 0) * etable_values load_picked_leading_u16_u8_high i))
    with (etable_values load_picked_leading_u16_u8_high i) by lia.
  rewrite <- decompose_load_picked_leading_u16_high by auto.
  rewrite Z.shiftr_shiftr by lia.
  change (8+7) with 15.

  destruct (load_picked_leading_is_upper_two_bytes i Hrange Hops) as [_ [H _]].
  rewrite H by auto.
  reflexivity.
Qed.

Lemma sign_extension_correct: forall i (signed : bool) (src: ConvOpSrc) (res: ConvOpRes),
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values is_sign i = (Z_of_bool signed) ->
    etable_values len i = len_of_LoadSize src ->
    etable_values is_i32 i = (match res with RES64 => 0 | RES32 => 1 end) ->
    etable_values load_picked_u64_cell i + 
    (etable_values is_sign i) * (etable_values load_picked_flag i) * sign_extension i
    = sign_extend signed src res (etable_values load_picked_u64_cell i).
Proof.
  intros i signed src res Hrange Hops Hsign Hlen Hi32.
  destruct signed.
  - simpl in Hsign. rewrite Hsign.
    unfold sign_extend.
    destruct res.
    + destruct src.
      * simpl in Hlen.
        destruct (load_one_number_of_bytes_len  i Hrange Hops) as
          [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [Hone [Htwo [Hfour [Height Hlen']]]]]]]; try congruence.
        rewrite <- (leading_bit_8 i Hrange Hops Hone).
        unfold sign_extension.
        rewrite Hone, Htwo, Height, Hi32.
        destruct (load_picked_flag_bit i) as [Hpicked | Hpicked].
        ** rewrite Hpicked. simpl. lia.
        ** rewrite Hpicked. change (Z.odd 1) with true. lia.
      * simpl in Hlen.
        destruct (load_one_number_of_bytes_len  i Hrange Hops) as
          [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [Hone [Htwo [Hfour [Height Hlen']]]]]]]; try congruence.
        rewrite <- (leading_bit_16 i Hrange Hops Htwo).
        unfold sign_extension.
        rewrite Hone, Htwo, Height, Hi32.
        destruct (load_picked_flag_bit i) as [Hpicked | Hpicked].
        ** rewrite Hpicked. simpl. lia.
        ** rewrite Hpicked. change (Z.odd 1) with true. lia.
      * simpl in Hlen.
        destruct (load_one_number_of_bytes_len  i Hrange Hops) as
          [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [Hone [Htwo [Hfour [Height Hlen']]]]]]]; try congruence.
        unfold sign_extension.
        rewrite Hone, Htwo, Height, Hi32.
        destruct (load_picked_flag_bit i) as [Hpicked | Hpicked].
        ** rewrite Hpicked. simpl. lia.
        ** rewrite Hpicked. change (Z.odd 1) with true. lia.
      * simpl in Hlen.
        destruct (load_one_number_of_bytes_len  i Hrange Hops) as
          [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [Hone [Htwo [Hfour [Height Hlen']]]]]]]; try congruence.
        unfold sign_extension.
        rewrite Hone, Htwo, Height, Hi32.
        destruct (load_picked_flag_bit i) as [Hpicked | Hpicked].
        ** rewrite Hpicked. simpl. lia.
        ** rewrite Hpicked. change (Z.odd 1) with true. lia.
    + destruct src.
      * simpl in Hlen.
        destruct (load_one_number_of_bytes_len  i Hrange Hops) as
          [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [Hone [Htwo [Hfour [Height Hlen']]]]]]]; try congruence.
        rewrite <- (leading_bit_8 i Hrange Hops Hone).
        unfold sign_extension.
        rewrite Hone, Htwo, Height, Hi32.
        destruct (load_picked_flag_bit i) as [Hpicked | Hpicked].
        ** rewrite Hpicked. simpl. lia.
        ** rewrite Hpicked. change (Z.odd 1) with true. lia.
      * simpl in Hlen.
        destruct (load_one_number_of_bytes_len  i Hrange Hops) as
          [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [Hone [Htwo [Hfour [Height Hlen']]]]]]]; try congruence.
        rewrite <- (leading_bit_16 i Hrange Hops Htwo).
        unfold sign_extension.
        rewrite Hone, Htwo, Height, Hi32.
        destruct (load_picked_flag_bit i) as [Hpicked | Hpicked].
        ** rewrite Hpicked. simpl. lia.
        ** rewrite Hpicked. change (Z.odd 1) with true. lia.
      * simpl in Hlen.
        destruct (load_one_number_of_bytes_len  i Hrange Hops) as
          [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [Hone [Htwo [Hfour [Height Hlen']]]]]]]; try congruence.
        rewrite <- (leading_bit_32 i Hrange Hops Hfour).
        unfold sign_extension.
        unfold sign_extension.
        rewrite Hone, Htwo, Height, Hi32.
        destruct (load_picked_flag_bit i) as [Hpicked | Hpicked].
        ** rewrite Hpicked. simpl. lia.
        ** rewrite Hpicked. change (Z.odd 1) with true. lia.
      * simpl in Hlen.
        destruct (load_one_number_of_bytes_len  i Hrange Hops) as
          [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [[Hone [Htwo [Hfour [Height Hlen']]]] | [Hone [Htwo [Hfour [Height Hlen']]]]]]]; try congruence.
        unfold sign_extension.
        rewrite Hone, Htwo, Height, Hi32.
        destruct (load_picked_flag_bit i) as [Hpicked | Hpicked].
        ** rewrite Hpicked. simpl. lia.
        ** rewrite Hpicked. change (Z.odd 1) with true. lia.
  - simpl in Hsign. rewrite Hsign.
    unfold sign_extend.
    lia.
Qed.

(* Result is either loaded value or sign-extended laoded value *)
Theorem loaded_result_is_correct : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values res i =
    etable_values load_picked_u64_cell i + 
    (* only sign extend if op is signed and loaded value is negative *)
    (etable_values is_sign i) * (etable_values load_picked_flag i) * sign_extension i.
Proof.
  intros i Hrange Hops.
  pose(H := op_load_extension i Hrange).
  unfold sign_extension.
  simpl in *.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Lemma memory_pages_not_exceeded : forall i,
    0 <= i ->
    etable_values (ops_cell Load) i = 1 ->
    etable_values load_block_index i + etable_values is_cross_block i <
    etable_values mpages_cell i * WASM_BLOCKS_PER_PAGE.
Proof.
  intros i Hrange Hops.
  pose(H := op_load_allocated_address i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  pose(Hadd := address_within_allocated_pages_helper_common i).
  lia.
Qed.

Lemma read_heap1 : forall i mem,
  0 <= i ->
  etable_values (ops_cell Load) i = 1 ->
  heap_rel (heap_map (etable_values eid_cell i)) (etable_values mpages_cell i) (etable_values maximal_memory_pages_cell i) mem ->
  exists bs,
    read_bytes mem (8 * Z.to_N (etable_values load_block_index i)) 8 =
    Some bs /\ Memdata.decode_int bs = etable_values load_value_in_heap1 i.
Proof.
  intros i mem Hrange Hops Hheap_rel .
  apply (heap_rel_lookup _ _ _ _ Hheap_rel).
  {
    pose(memory_pages_not_exceeded i Hrange Hops).
    destruct Hheap_rel as [heap_real_lookup heap_size heap_valid].    
    assert(Hne : etable_values load_block_index i + 1 <= 
      etable_values current_memory_page_size i * WASM_BLOCKS_PER_PAGE).
    - pose(is_cross_block_bit i); lia.
      rewrite heap_size in Hne.
      unfold WASM_BLOCKS_PER_PAGE in Hne.
      unfold mem_size in Hne.
      unfold ml_valid in heap_valid.
      unfold page_size in *.
      simpl in heap_valid, Hne.
    assert (65536 | Z.of_N (mem_length mem)).
    - apply Znumtheory.Zmod_divide; try lia.
      unfold mem_length.
      apply (f_equal Z.of_N) in heap_valid.
      rewrite N2Z.inj_mod in heap_valid.
      simpl in heap_valid; auto.
    rewrite N2Z.inj_div in Hne.
    apply (Zmult_le_compat_r _ _ 8) in Hne; try lia.
    replace (Z.of_N (mem_length mem) / Z.of_N 65536 * 8192 * 8) with
      (65536 * (Z.of_N (mem_length mem) / 65536)) in Hne by lia.
    rewrite <- Znumtheory.Zdivide_Zdiv_eq_2 in Hne; auto; try lia.
    rewrite (Z.mul_comm 65536 _) in Hne.
    rewrite Z_div_mult in Hne; try lia.
    pose(load_block_index_common i).
    apply Z2N.inj_le in Hne; lia.
  }
  {
    eapply mtable_read with (is_i32 := 0).
    pose(Hread := alloc_memory_table_lookup_read_cell_with_value_correct
      _ _ _ _ _ _ heap_read1 i Hrange).
    simpl in Hread.
    pose(load_block_index_common i).
    rewrite Z2N.id; try lia.
    apply Hread; auto.
    apply (eid_common i).
    pose(load_block_index_common i).
    assert(0 <= etable_values load_block_index i < 2 * common + 10). lia.
    simpl in H.
    lia.
  }
Qed.

Lemma read_heap2 : forall i mem,
  0 <= i ->
  etable_values (ops_cell Load) i = 1 ->
  heap_rel (heap_map (etable_values eid_cell i)) (etable_values mpages_cell i) (etable_values maximal_memory_pages_cell i) mem ->
  etable_values is_cross_block i = 1 ->
  exists bs,
    read_bytes mem (8 * Z.to_N (etable_values load_block_index i + 1)) 8 =
    Some bs /\ Memdata.decode_int bs = etable_values load_value_in_heap2 i.
Proof.
  intros i mem Hrange Hops Hheap_rel Hcross.
  apply (heap_rel_lookup _ _ _ _ Hheap_rel).
  {
    pose(memory_pages_not_exceeded i Hrange Hops).
    destruct Hheap_rel as [heap_real_lookup heap_size heap_valid].
    assert(Hne : (etable_values load_block_index i + 1) + 1 <= 
      etable_values current_memory_page_size i * WASM_BLOCKS_PER_PAGE).
    - lia.
    rewrite heap_size in Hne.
    unfold WASM_BLOCKS_PER_PAGE in Hne.
    unfold mem_size in Hne.
    unfold ml_valid in heap_valid.
    unfold page_size in *.
    simpl in heap_valid, Hne.
    assert (65536 | Z.of_N (mem_length mem)).
    - apply Znumtheory.Zmod_divide; try lia.
      unfold mem_length.
      apply (f_equal Z.of_N) in heap_valid.
      rewrite N2Z.inj_mod in heap_valid.
      simpl in heap_valid; auto.
    rewrite N2Z.inj_div in Hne.
    apply (Zmult_le_compat_r _ _ 8) in Hne; try lia.
    replace (Z.of_N (mem_length mem) / Z.of_N 65536 * 8192 * 8) with
      (65536 * (Z.of_N (mem_length mem) / 65536)) in Hne by lia.
    rewrite <- Znumtheory.Zdivide_Zdiv_eq_2 in Hne; auto; try lia.
    rewrite (Z.mul_comm 65536 _) in Hne.
    rewrite Z_div_mult in Hne; try lia.
    pose(load_block_index_common i).
    apply Z2N.inj_le in Hne; lia.
  }
  {
    eapply mtable_read with (is_i32 := 0).
    pose(Hread := alloc_memory_table_lookup_read_cell_with_value_correct
      _ _ _ _ _ _ heap_read2 i Hrange).
    simpl in Hread.
    pose(load_block_index_common i).
    rewrite Z2N.id; try lia.
    apply Hread; auto; try lia.
    apply (eid_common i).
    pose(load_block_index_common i).
    assert(0 <= etable_values load_block_index i + 1 < 2 * common + 10). lia.
    simpl in H.
    lia.
  }
Qed.

Lemma those_not_nil:
  forall A (l: list (option A)) (a : option A),
    those (a :: l) <> Some nil.
Proof.
  intros A l a.
  rewrite <- those_those0.
  simpl.
  destruct a.
  - destruct (those0 l); simpl; discriminate 1.
  - discriminate 1.
Qed.

Lemma those_nil:
  forall A,
    those (@nil (option A)) = Some (@nil A).
Proof.
  intros. rewrite <- those_those0. simpl.
  reflexivity.
Qed.

Lemma those_cons:
  forall A (a: option A) (a': A) (l: list (option A)) (l': list A),
    a = Some a' ->
    those l = Some l' ->
    those (a :: l) = Some (a' :: l').
Proof.
  intros A a a' l l' Ha Hl.
  rewrite <- those_those0 in *. subst.
  simpl. rewrite Hl. simpl. reflexivity.
Qed.

Lemma those_cons_desctruct:
  forall A (a: option A) (a': A) (l: list (option A)) (l': list A),
    those (a :: l) = Some (a' :: l') ->
    a = Some a' /\ those l = Some l'.
Proof.
  intros A a a' l l'.
  rewrite <- those_those0. simpl.
  destruct a as [b|] eqn: Ha.
  - unfold option_map. destruct (those0 l) eqn: Hthose_l.
    + inversion 1. subst.
      rewrite <- those_those0. rewrite Hthose_l.
      split; reflexivity.
    + discriminate 1.
    + discriminate 1.
Qed.

Lemma those_Some:
  forall A (l: list (option A)) (l': list A),
    those l = Some l' ->
    Forall (fun x => x <> None) l.
Proof.
  intros A.
  induction l as [|a t].
  - intros. apply Forall_nil_iff. exact I.
  - intros l' H. apply Forall_cons_iff.
    split.
    * generalize H. rewrite <- those_those0. simpl.
      destruct a eqn: Ha; [discriminate 2 | discriminate 1].
    * destruct l' as [|a' t'].
      pose proof (those_not_nil _ t a) as Hnnil.
      exfalso. apply Hnnil. exact H.
      apply (IHt t').
      eapply those_cons_desctruct in H.
      destruct H as [Ha Ht]. exact Ht.
Qed.

Lemma those_Some_forall:
  forall A (l: list (option A)) (l': list A),
    those l = Some l' ->
    Forall2 (fun x y => x = Some y) l l'.
Proof.
  intros A.
  induction l as [|a t Hind].
  - intros l' H.
    rewrite those_nil in H.
    inversion H.
    apply Forall2_nil.
  - destruct l'.
    + pose proof (those_not_nil _ t a).
      intros Hthose. rewrite Hthose in H.
      exfalso. apply H. reflexivity.
  - intros Hat.
    eapply those_cons_desctruct in Hat.
    destruct Hat as [Ha Ht].
    apply Forall2_cons_iff.
    split; [eassumption|].
    apply Hind. eassumption.
Qed.

Lemma those_forall_Some:
  forall A (l: list (option A)) (l': list A),
    Forall2 (fun x y => x = Some y) l l' ->
    those l = Some l'.
Proof.
  intros A.
  induction l as [|a t Hind].
  - destruct l'; intros.
    + apply those_nil.
    + inversion H.
  - destruct l'; intros.
    + inversion H.
    + apply those_cons.
      apply Forall2_cons_iff in H.
      destruct H as [Ha Hf].
      * eassumption.
      * apply Hind.
        apply Forall2_cons_iff in H.
        destruct H as [Ha Hf].
        eassumption.
Qed.


Lemma those_app:
  forall A (l1 l2 : list (option A)) (l1' l2' : list A),
    those l1 = Some l1' ->
    those l2 = Some l2' ->
    those (l1 ++ l2) = Some (l1' ++ l2').
Proof.
  intros until l2'. intros H1 H2.
  apply those_Some_forall in H1, H2.
  apply those_forall_Some.
  apply Forall2_app; eassumption.
Qed.

Lemma those_app_inv:
  forall A (l1 l2: list (option A)) (l' : list A),
    those (l1 ++ l2) = Some l' ->
    exists l1' l2',
      those l1 = Some l1' /\ those l2 = Some l2' /\ l' = l1' ++ l2'.
Proof.
  intros until l'. intros H.
  eapply those_Some_forall in H.
  apply Forall2_app_inv_l in H.
  destruct H as (l1' & l2' & H1 & H2 & Heq).
  exists l1'. exists l2'.
  apply those_forall_Some in H1, H2.
  split; [eassumption|].
  split; [eassumption|].
  assumption.
Qed.

Definition read_bytes_aux (m : memory) (start_idx : N) (len : nat) : list (option byte) :=
  (List.map
     (fun off =>
        let idx := BinNatDef.N.add start_idx (N.of_nat off) in
        memory_list.mem_lookup idx m.(mem_data))
     (seq.iota 0 len)).

Lemma iota_S:
  forall a b, iota (S a) b = [seq ssrnat.addn 1 i | i <- iota a b].
Proof.
  intros.
  rewrite <- iotaDl.
  replace (ssrnat.addn 1 a) with (S a); [reflexivity|].
  ssrnat.nat_congr.
  reflexivity.
Qed.

Lemma iota_add_refl:
  forall a b, iota a b = [seq (a + i)%nat | i <- iota 0 b].
Proof.
  intros.
  rewrite <- iotaDl.
  ssrnat.nat_norm.
  reflexivity.
Qed.


Lemma mem_lookup_index_eq:
  forall mem len1 len2 start_idx,
    List.map
      (fun off => memory_list.mem_lookup
                 (start_idx + N.of_nat off)%N
                 (mem_data mem))
      (iota len1 len2)
    =
    List.map
      (fun off => memory_list.mem_lookup
                 (start_idx + N.of_nat len1 + N.of_nat off)%N
                 (mem_data mem))
      (iota 0 len2).
Proof.
  intros mem. induction len1.
  - intros.
    replace (start_idx + N.of_nat 0)%N with start_idx by lia.
    reflexivity.
  - intros.
    pose proof (IHlen1 len2 (start_idx + N.of_nat 1)%N) as Hind.
    replace (start_idx + N.of_nat (S len1))%N with
      (start_idx + N.of_nat 1 + N.of_nat len1)%N by lia.
    rewrite <- Hind.
    rewrite iota_S. rewrite <- map_comp.
    f_equal. intros Hn Ho Hfun Hmk.
    rewrite Hfun. reflexivity.
    eapply FunctionalExtensionality.functional_extensionality.
    intros x.
    unfold comp. ssrnat.nat_norm.
    f_equal. lia.
Qed.


Lemma iota_app: forall len1 len2,
    iota 0 (len1 + len2) = iota 0 len1 ++ iota len1 len2.
Proof.
  intros. apply iotaD.
Qed.

Lemma read_bytes_app_inv : forall mem start_idx len1 len2 bs,
    read_bytes mem start_idx (len1 + len2) = Some bs ->
    exists bs1 bs2,
      read_bytes mem start_idx len1 = Some bs1 /\
        read_bytes mem (start_idx + N.of_nat len1) len2 = Some bs2 /\
        bs = bs1 ++ bs2.
Proof.
  intros until bs. unfold read_bytes.
  rewrite iota_app. rewrite map_app.
  intros H.
  apply those_Some_forall in H.
  apply Forall2_app_inv_l in H.
  destruct H as (l1' & l2' & H1 & H2 & Heq).
  exists l1'. exists l2'.
  split; [| split].
  - apply those_forall_Some. eauto.
  - apply those_forall_Some.
    rewrite mem_lookup_index_eq in H2.
    eauto.
  - assumption.
Qed.

Lemma read_bytes_app: forall mem start_idx len1 len2 bs1 bs2,
    read_bytes mem start_idx len1 = Some bs1 ->
    read_bytes mem (start_idx + N.of_nat len1) len2 = Some bs2 ->
    read_bytes mem start_idx (len1 + len2) = Some (bs1 ++ bs2).
Proof.
  intros until bs2. unfold read_bytes. intros H1 H2.
  rewrite iota_app. rewrite map_app.
  apply those_forall_Some.
  apply Forall2_app.
  - apply those_Some_forall in H1.
    eassumption.
  - apply those_Some_forall in H2.
    rewrite iota_add_refl.
    rewrite <- map_comp.
    unfold comp.
    replace ([seq memory_list.mem_lookup
                (start_idx + N.of_nat (len1 + x))%N (mem_data mem)
             | x <- iota 0 len2]) with
      (List.map
            (fun off : nat =>
               memory_list.mem_lookup
                 (start_idx + N.of_nat len1 + N.of_nat off)%N (mem_data mem))
            (iota 0 len2)).
  - generalize H2.
    eapply Forall2_impl.
    eauto.
  - f_equal.
    + intros _ _ H _. rewrite H. reflexivity.
    + apply FunctionalExtensionality.functional_extensionality.
      intros x.
      f_equal.
      lia.
Qed.

Lemma those_length: forall A (l: list (option A)) (l': list A),
    those l = Some l' ->
    length l = length l'.
Proof.
  intros until l'. intros H.
  apply those_Some_forall in H.
  apply Forall2_length in H.
  eassumption.
Qed.

Lemma read_bytes_length: forall mem start_idx len bs,
    read_bytes mem start_idx len = Some bs ->
    length bs = len.
Proof.
  intros until bs. intros H.
  unfold read_bytes in H.
  apply those_length in H.
  rewrite <- H.
  rewrite map_length.
  rewrite size_iota.
  reflexivity.
Qed.


Lemma little_endian_eq: forall bs,
    rev_if_be (bs) = bs.
Proof.
  intros.
  unfold rev_if_be.
  Transparent Archi.big_endian.
  simpl.
  reflexivity.
Qed.

Lemma decode_int_cons: forall b bs,
    Memdata.decode_int (b :: bs) =
      Memdata.decode_int bs * 2^8 + Byte.unsigned b.
Proof.
  intros.
  unfold decode_int. do 2 rewrite little_endian_eq.
  simpl.
  lia.
Qed.

Lemma length_nil_eq: forall A,
    length (@nil A) = 0%nat.
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma cons_length: forall A (a: A) (t : list A),
    length (a :: t) = S (length t).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma decode_int_nil:
  Memdata.decode_int nil = 0.
Proof.
  unfold decode_int. simpl.
  reflexivity.
Qed.

Lemma decode_int_app: forall bs1 bs2,
    Memdata.decode_int(bs1 ++ bs2) =
      Memdata.decode_int bs2 * 2^(Z.of_nat (length bs1) * 8) + Memdata.decode_int bs1.
Proof.
  induction bs1.
  - intros. rewrite length_nil_eq.
    replace (2 ^ (Z.of_nat 0 * 8)) with 1 by lia.
    simpl.
    rewrite decode_int_nil.
    lia.
  - intros.
    rewrite cat_cons.
    rewrite decode_int_cons. rewrite cons_length.
    replace (Z.of_nat (S (length bs1))) with
      (Z.of_nat (length bs1) + 1)%Z by lia.
    rewrite IHbs1.
    rewrite decode_int_cons.
    rewrite Z.mul_add_distr_r.
    replace ((Z.of_nat (length bs1) + 1) * 8) with
      (Z.of_nat (length bs1) * 8 + 8) by lia.
    rewrite Z.pow_add_r; lia.
Qed.

Lemma read_bytes_separate : forall mem start_idx len1 len2 bs,
  read_bytes mem start_idx (len1 + len2) = Some bs ->
  exists bs1 bs2,
    read_bytes mem start_idx len1 = Some bs1 /\
    read_bytes mem (start_idx + N.of_nat len1) len2 = Some bs2 /\
      bs = bs1 ++ bs2.
Proof.
  apply read_bytes_app_inv.
Qed.


Lemma read_bytes_combine : forall mem len1 len2 start_idx bs1 bs2,
    read_bytes mem start_idx len1 = Some bs1 ->
    read_bytes mem (start_idx + N.of_nat len1) len2 = Some bs2 ->
    read_bytes mem start_idx (len1 + len2) = Some (bs1 ++ bs2) /\
      Memdata.decode_int (bs1 ++ bs2) =
        Memdata.decode_int bs2 * 2^(Z.of_nat len1 * 8) + Memdata.decode_int bs1.
Proof.
  intros until bs2. intros H1 H2.
  split.
  - eapply read_bytes_app; eassumption.
  - pose proof (read_bytes_length _ _ _ _ H1) as Hlen.
    rewrite <- Hlen.
    eapply decode_int_app.
Qed.

Lemma read_bytes_drop_l: forall mem start_idx len bs x,
  (N.to_nat x <= len)%nat ->
  read_bytes mem start_idx len = Some bs ->
  exists bx,
    read_bytes mem (start_idx + x) (len - N.to_nat x) = Some bx.
Proof.
  intros until x. intros Hle Hbs.
  replace (len) with (N.to_nat x + (len - N.to_nat x))%nat in Hbs by lia.
  pose proof (read_bytes_app_inv _ _ _ _ _ Hbs) as Hinv.
  generalize Hinv. intros (bs1 & bs2 & Hbs1 & Hbs2 & Hbs_app).
  exists bs2.
  rewrite Nnat.N2Nat.id in Hbs2.
  eassumption.
Qed.

Lemma length_ge_0: forall A (l: list A),
    (0 <= length l)%nat.
Proof.
  intros. lia.
Qed.

Lemma byte_unsigned_range: forall b,
    (0 <= Byte.unsigned b < 2^8)%Z.
Proof.
  intros.
  pose proof (Byte.unsigned_range_2 b).
  unfold Byte.max_unsigned in H. simpl in H.
  lia.
Qed.

Lemma decode_int_range: forall bs,
    (0 <= Memdata.decode_int bs < 2^(Z.of_nat (length bs) * 8))%Z.
Proof.
  induction bs.
  - simpl. unfold decode_int. rewrite little_endian_eq. simpl. lia.
  - rewrite decode_int_cons.
    rewrite cons_length.
    replace (Z.of_nat (S (length bs)) * 8) with
      (Z.of_nat (length bs) * 8 + 8) by lia.
    rewrite Z.pow_add_r by lia.
    pose proof byte_unsigned_range a as Ha.
    lia.
Qed.

Lemma decode_int_drop_l: forall bs1 bs2,
    Memdata.decode_int bs2 = Z.shiftr (Memdata.decode_int (bs1 ++ bs2))
                                          (Z.of_nat (length bs1) * 8).
Proof.
  intros until bs2.
  pose proof (decode_int_app bs1 bs2) as Happ.
  pose proof length_ge_0 byte bs1 as Hlen.
  pose proof decode_int_range bs1 as Hrange.
  rewrite Happ.
  remember (Z.of_nat (length bs1) * 8) as m.
  remember (decode_int bs1) as n.
  rewrite Z.shiftr_div_pow2 by lia.
  apply Z.div_unique with (r := n); lia.
Qed.


Lemma read_bytes_drop_r: forall mem start_idx len bs x,
  (N.to_nat x <= len)%nat ->
  read_bytes mem start_idx len = Some bs ->
  exists bx,
    read_bytes mem start_idx (len - N.to_nat x) = Some bx.
Proof.
  intros until x. intros Hle Hbs.
  replace (len) with ((len - N.to_nat x) + N.to_nat x)%nat in Hbs by lia.
  pose proof (read_bytes_app_inv _ _ _ _ _ Hbs) as Hinv.
  destruct Hinv as (bs1 & bs2 & Hbs1 & Hbs2 & Hbs_app).
  exists bs1.
  eassumption.
Qed.

Lemma decode_int_drop_r: forall bs1 bs2,
  Memdata.decode_int bs1 = Memdata.decode_int (bs1 ++ bs2) mod 2^(Z.of_nat (length bs1) * 8).
Proof.
  intros until bs2.
  pose proof (decode_int_app bs1 bs2) as Happ.
  pose proof length_ge_0 byte bs1 as Hlen.
  pose proof decode_int_range bs1 as Hrange.
  rewrite Happ.
  remember (2 ^ (Z.of_nat (length bs1) * 8)) as m.
  rewrite Z.add_comm.
  rewrite Z_mod_plus with (c := m) by lia.
  rewrite Z.mod_small; lia.
Qed.


Lemma read_bytes_increase_start : forall mem start_idx len bs x,
  (N.to_nat x <= len)%nat ->
  read_bytes mem start_idx len = Some bs ->
  exists bsx,
    read_bytes mem (start_idx + x) (len - N.to_nat x) = Some bsx /\
    Memdata.decode_int bsx = Z.shiftr (Memdata.decode_int bs) (Z.of_N x * 8).
Proof.
  intros until x. intros Hlen Hbs.
  replace (len) with (N.to_nat x + (len - N.to_nat x))%nat in Hbs by lia.
  pose proof (read_bytes_app_inv _ _ _ _ _ Hbs) as Hinv.
  destruct Hinv as (bs1 & bs2 & Hbs1 & Hbs2 & Hbs_app).
  rewrite Nnat.N2Nat.id in Hbs2.
  exists bs2.
  split; [eassumption|].
  rewrite Hbs_app.
  pose proof (read_bytes_length _ _ _ _ Hbs1) as Hlen1.
  pose proof (decode_int_drop_l bs1 bs2) as Hdrop_dec.
  rewrite Hdrop_dec.
  f_equal. f_equal.
  unfold bytes.byte in Hlen1.
  rewrite Hlen1.
  lia.
Qed.

Lemma read_bytes_decrease_length : forall mem start_idx len bs x,
  (N.to_nat x <= len)%nat ->
  read_bytes mem start_idx len = Some bs ->
  exists bsx,
  read_bytes mem start_idx (len - N.to_nat x) = Some bsx /\
  Memdata.decode_int bsx = (Memdata.decode_int bs) mod 2^(Z.of_nat (len - N.to_nat x) * 8).
Proof.
  intros until x. intros Hlen Hbs.
  replace (len) with ((len - N.to_nat x) + N.to_nat x)%nat in Hbs by lia.
  pose proof (read_bytes_app_inv _ _ _ _ _ Hbs) as Hinv.
  destruct Hinv as (bs1 & bs2 & Hbs1 & Hbs2 & Hbs_app).
  remember (N.to_nat x) as m.
  exists bs1.
  split; [eassumption|].
  rewrite Hbs_app.
  pose proof (read_bytes_length _ _ _ _ Hbs1) as Hlen1.
  pose proof (decode_int_drop_r bs1 bs2) as Hdrop_dec.
  rewrite Hdrop_dec.
  do 4 f_equal.
  unfold bytes.byte in Hlen1.
  rewrite Hlen1.
  reflexivity.
Qed.

Lemma read_load_picked : forall i mem,
  0 <= i ->
  etable_values (ops_cell Load) i = 1 ->
  heap_rel (heap_map (etable_values eid_cell i)) (etable_values mpages_cell i) (etable_values maximal_memory_pages_cell i) mem ->
  exists bs,
  read_bytes mem (Z.to_N (effective_address i)) (Z.to_nat (etable_values len i)) = Some bs /\
  Memdata.decode_int bs = etable_values load_picked_u64_cell i.
Proof.
  intros i mem Hrange Hops Hheap_rel.
  pose(Hheap1 := read_heap1 i mem Hrange Hops Hheap_rel).
  pose(Hheap2 := read_heap2 i mem Hrange Hops Hheap_rel).
  destruct Hheap1 as [bs1 [Hread1 Hbs1]].
  rewrite effective_address_value; auto.
  pose(load_inner_pos_bound i Hrange Hops).
  pose(length_is_correct i Hrange Hops).
  pose(bytes_loaded_range i Hrange Hops).
  pose(end_inner_byte_range i Hrange Hops).
  pose(load_block_index_common i).
  unfold end_inner_byte, WASM_BLOCK_BYTE_SIZE in *.
  destruct (is_cross_block_bit i) as [Hcb0 | Hcb1].
  - replace(etable_values load_value_in_heap1 i) with (heap_value i) in Hbs1.
    2 : {
      unfold heap_value.
      rewrite(no_cross_block_no_heap2 i Hrange Hops Hcb0); lia.
    }
    apply(read_bytes_increase_start _ _ _ _ 
      (Z.to_N (etable_values load_inner_pos i))) in Hread1.
    rewrite Z2N.id in Hread1 by lia.
    rewrite Hbs1 in Hread1.
    destruct Hread1 as [bsx1 [Hreadx1 Hbsx1]].
    rewrite <- (Z2N.inj_mul 8 _)  in Hreadx1 by lia.
    rewrite Z.mul_comm in Hreadx1.
    rewrite <- Z2N.inj_add in Hreadx1 by lia.
    apply(read_bytes_decrease_length _ _ _ _ 
      (8 - Z.to_N (etable_values load_inner_pos i + etable_values len i))) in Hreadx1.
    rewrite <- (Nnat.N2Nat.inj_sub 8 _) in Hreadx1.
    rewrite <- Nnat.N2Nat.inj_sub in Hreadx1.
    rewrite <- (Z2N.inj_sub 8 _) in Hreadx1 by lia.
    rewrite <- (Z2N.inj_sub 8 _) in Hreadx1 by lia.
    rewrite <- Z2N.inj_sub in Hreadx1 by lia.
    rewrite Z_N_nat in Hreadx1.
    replace (8 - etable_values load_inner_pos i - (8 - (etable_values load_inner_pos i + etable_values len i))) 
      with (etable_values len i) in Hreadx1 by lia.
    rewrite Z2Nat.id in Hreadx1 by lia.
    destruct Hreadx1 as [bsx [Hreadx Hbsx]].
    exists bsx.
    rewrite Hreadx.
    rewrite Hbsx1 in Hbsx.
    rewrite <- len_modulus_and_len in Hbsx; auto.
    rewrite <- load_picked_from_heap_value in Hbsx; auto.
    rewrite <- (Z2N.inj_sub 8 _) by lia.
    rewrite Z_N_nat.
    rewrite Z_N_nat.
    rewrite <- (Z2Nat.inj_sub 8 _) by lia.
    rewrite <- Z2Nat.inj_le by lia.
    lia.
    rewrite Z_N_nat.
    rewrite <- (Z2Nat.inj_le _ 8); lia.
  - specialize (Hheap2 Hcb1).
    destruct Hheap2 as [bs2 [Hread2 Hbs2]].
    rewrite <- (Z2N.inj_mul 8 _) in Hread2 by lia.
    rewrite <- (Z2N.inj_mul 8 _) in Hread1 by lia.
    replace (8 * (etable_values load_block_index i + 1)) with
      (8 * etable_values load_block_index i + 8) in Hread2 by lia.
    rewrite Z2N.inj_add in Hread2 by lia.
    pose(Hread := read_bytes_combine _ _ _ _ _ _ Hread1 Hread2).
    change (read_bytes mem (Z.to_N (8 * etable_values load_block_index i)) (8+8)) with
      (read_bytes mem (Z.to_N (8 * etable_values load_block_index i)) 16) in Hread.
    destruct Hread as [Hread Hbs].
    rewrite Hbs1, Hbs2 in Hbs.
    simpl in Hbs.
    replace(etable_values load_value_in_heap2 i * Z.pow_pos 2 64 + 
      etable_values load_value_in_heap1 i) with (heap_value i) in Hbs.
    2 : {
      unfold heap_value; lia.
    }
    apply(read_bytes_increase_start _ _ _ _ 
      (Z.to_N (etable_values load_inner_pos i))) in Hread.
    rewrite Z2N.id in Hread by lia.
    replace (decode_int (bs1 ++ bs2)%list) with (decode_int (bs1 ++ bs2)) in Hread by auto.
    rewrite Hbs in Hread.
    destruct Hread as [bsx1 [Hreadx1 Hbsx1]].
    rewrite Z.mul_comm in Hreadx1.
    rewrite <- Z2N.inj_add in Hreadx1 by lia.
    apply(read_bytes_decrease_length _ _ _ _ 
      (16 - Z.to_N (etable_values load_inner_pos i + etable_values len i))) in Hreadx1.
    rewrite <- (Nnat.N2Nat.inj_sub 16 _) in Hreadx1.
    rewrite <- Nnat.N2Nat.inj_sub in Hreadx1.
    rewrite <- (Z2N.inj_sub 16 _) in Hreadx1 by lia.
    rewrite <- (Z2N.inj_sub 16 _) in Hreadx1 by lia.
    rewrite <- Z2N.inj_sub in Hreadx1 by lia.
    rewrite Z_N_nat in Hreadx1.
    replace (16 - etable_values load_inner_pos i - (16 - (etable_values load_inner_pos i + etable_values len i))) 
      with (etable_values len i) in Hreadx1 by lia.
    rewrite Z2Nat.id in Hreadx1 by lia.
    destruct Hreadx1 as [bsx [Hreadx Hbsx]].
    exists bsx.
    rewrite Hreadx.
    rewrite Hbsx1 in Hbsx.
    rewrite <- len_modulus_and_len in Hbsx; auto.
    rewrite <- load_picked_from_heap_value in Hbsx; auto.
    rewrite <- (Z2N.inj_sub 16 _) by lia.
    rewrite Z_N_nat.
    rewrite Z_N_nat.
    rewrite <- (Z2Nat.inj_sub 16 _) by lia.
    rewrite <- Z2Nat.inj_le by lia.
    lia.
    rewrite Z_N_nat.
    rewrite <- (Z2Nat.inj_le _ 16); lia.
Qed.

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
Proof.
  intros i mem Hrange Hops Hheap_rel.
  pose(Hrlp := read_load_picked i mem Hrange Hops Hheap_rel).
  destruct Hheap_rel as [heap_real_lookup heap_size heap_valid].  
  destruct Hrlp as [bs [Hrlp Hbs]].
  exists bs.
  split; auto.
  unfold load.
  assert(etable_values load_base i + etable_values opcode_load_offset i 
    + etable_values len i <= Z.of_N (mem_length mem)).
  - pose(memory_pages_not_exceeded i Hrange Hops).
    change (etable_values load_base i + etable_values opcode_load_offset i) with
      (effective_address i).
    rewrite(effective_address_value i Hrange Hops).
    replace (etable_values load_block_index i * WASM_BLOCK_BYTE_SIZE + 
      etable_values load_inner_pos i + etable_values len i) with
      (etable_values load_block_index i * WASM_BLOCK_BYTE_SIZE + (etable_values load_inner_pos i + etable_values len i)) by lia.
    replace (etable_values load_inner_pos i + etable_values len i) with
      (end_inner_byte i + 1).
    2 : {unfold end_inner_byte.
        replace(etable_values load_inner_pos i + etable_values len i - 1 + 1) with
          (etable_values load_inner_pos i + etable_values len i + (- (1) + 1)) by lia.
        rewrite Z.add_opp_diag_l.
        lia. }
    pose(end_inner_byte_range i Hrange Hops).
    unfold WASM_BLOCK_BYTE_SIZE, WASM_BLOCKS_PER_PAGE in *.
    destruct (is_cross_block_bit i) as [H0 | H1].
    - rewrite H0 in *.
      assert(etable_values load_block_index i + 1 <= etable_values current_memory_page_size i * 8192).
      - lia.
      rewrite heap_size in H.
      unfold mem_size in H.
      unfold ml_valid in heap_valid.
      unfold page_size in *.
      simpl in heap_valid, H.
      assert (65536 | Z.of_N (mem_length mem)).
      - apply Znumtheory.Zmod_divide; try lia.
        unfold mem_length.
        apply (f_equal Z.of_N) in heap_valid.
        rewrite N2Z.inj_mod in heap_valid.
        simpl in heap_valid; auto.
      rewrite N2Z.inj_div in H.
      apply (Zmult_le_compat_r _ _ 8) in H; try lia.
      replace (Z.of_N (mem_length mem) / Z.of_N 65536 * 8192 * 8) with
        (65536 * (Z.of_N (mem_length mem) / 65536)) in H by lia.
      rewrite <- Znumtheory.Zdivide_Zdiv_eq_2 in H; auto; try lia.
      rewrite (Z.mul_comm 65536 _) in H.
      rewrite Z_div_mult in H; try lia.
    - rewrite H1 in *.
      assert(etable_values load_block_index i + 1 + 1 <= etable_values current_memory_page_size i * 8192).
      - lia.
      rewrite heap_size in H.
      unfold mem_size in H.
      unfold ml_valid in heap_valid.
      unfold page_size in *.
      simpl in heap_valid, H.
      assert (65536 | Z.of_N (mem_length mem)).
      - apply Znumtheory.Zmod_divide; try lia.
        unfold mem_length.
        apply (f_equal Z.of_N) in heap_valid.
        rewrite N2Z.inj_mod in heap_valid.
        simpl in heap_valid; auto.
      rewrite N2Z.inj_div in H.
      apply (Zmult_le_compat_r _ _ 8) in H; try lia.
      replace (Z.of_N (mem_length mem) / Z.of_N 65536 * 8192 * 8) with
        (65536 * (Z.of_N (mem_length mem) / 65536)) in H by lia.
      rewrite <- Znumtheory.Zdivide_Zdiv_eq_2 in H; auto; try lia.
      rewrite (Z.mul_comm 65536 _) in H.
      rewrite Z_div_mult in H; try lia.
  assert(Hbase : 0 <= etable_values load_base i).
  - eapply read_with_value_range with (is_i32 := fun get => 1)
                           (sp := fun get => get sp_cell + 1)
                           (enable := fun get => get (ops_cell Load))
                           (loctyp := MTableModel.LocationType_Stack); auto.
    pose(sp_common i); lia.
    apply stack_read.
  rewrite <- (Z2N.id (etable_values load_base i)) in H by apply Hbase.
  pose(opcode_load_offset_common i).
  rewrite <- (Z2N.id (etable_values opcode_load_offset i)) in H by lia.
  rewrite <- N2Z.inj_add in H.
  pose(length_is_correct i Hrange Hops).
  pose(bytes_loaded_range i Hrange Hops).
  rewrite <- (Z2N.id (etable_values len i)) in H by lia.
  rewrite (Z_nat_N (etable_values len i)).
  rewrite <- N2Z.inj_add in H.
  replace (Z.of_N (Z.to_N (etable_values load_base i) + Z.to_N (etable_values opcode_load_offset i) + Z.to_N (etable_values len i)))
  with (Z.of_N (Z.to_N (etable_values load_base i) + (Z.to_N (etable_values opcode_load_offset i) + Z.to_N (etable_values len i)))) in H by lia.
  rewrite <- N2Z.inj_le in H.
  rewrite <- N.leb_le in H.
  rewrite H.
  rewrite <- Z2N.inj_add by lia.
  change (etable_values load_base i + etable_values opcode_load_offset i) with 
    (effective_address i); auto.
Qed.
