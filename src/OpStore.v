(* Copyright (C) CertiK 2024-2026 *)

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
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config Store i)) with (1 + etable_values is_cross_block i).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).

  destruct(is_cross_block_bit i) as [Hc | Hc]; rewrite Hc.
  - rewrite Z.add_0_r.
    assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap >= 1).
    - apply MTable.mtable_write_mops with
        (offset := etable_values load_block_index i)
        (is_i32 := 0)
        (value := etable_values store_value_in_heap1 i); auto.
      apply (alloc_memory_table_lookup_write_cell_with_value_correct _ _ _ _ _ _ 
        heap_write1 i Hrange); auto.
      - apply eid_common.
      - pose(load_block_index_common i); lia.
    lia.
  - change (1+1) with 2.
    assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap >= 2).
    - apply MTable.mtable_write_mops2 with
        (offset1 := etable_values load_block_index i)
        (offset2 := etable_values load_block_index i + 1)
        (is_i32_1 := 0)
        (is_i32_2 := 0)
        (value1 := etable_values store_value_in_heap1 i)
        (value2 := etable_values store_value_in_heap2 i); auto.
      apply (alloc_memory_table_lookup_write_cell_with_value_correct _ _ _ _ _ _ 
        heap_write1 i Hrange); auto.
      - apply eid_common.
      - pose(load_block_index_common i); lia.
      apply (alloc_memory_table_lookup_write_cell_with_value_correct _ _ _ _ _ _ 
        heap_write2 i Hrange); auto.
      - apply eid_common.
      - pose(load_block_index_common i); lia.
      - lia.
      lia.
    lia.
Qed.

Lemma load_one_number_of_bytes : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    (etable_values is_one_byte i = 1 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 0)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 1 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 0)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 1 /\ etable_values is_eight_bytes i = 0)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 1).
Proof.
  intros i Hrange Hops.
  pose(Hlength := op_store_length i Hrange).
  simpl in Hlength.
  replace (i+0) with i in * by lia.
  pose(Honebit := is_one_byte_bit i).
  pose(Htwobit := is_two_bytes_bit i).
  pose(Hfourbit := is_four_bytes_bit i).
  pose(Heightbit := is_eight_bytes_bit i).
  lia.
Qed.

Lemma len_value : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values len i = 1
 \/ etable_values len i = 2
 \/ etable_values len i = 4
 \/ etable_values len i = 8.
Proof.
  intros i Hrange Hops.
  pose(Hlen := op_store_len_gate i Hrange).
  simpl in Hlen.
  replace (i+0) with i in * by lia.
  pose(load_one_number_of_bytes i Hrange).
  lia.
Qed.



Lemma load_one_number_of_bytes_len : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    (etable_values is_one_byte i = 1 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 0 /\ etable_values len i = 1)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 1 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 0 /\ etable_values len i = 2)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 1 /\ etable_values is_eight_bytes i = 0 /\ etable_values len i = 4)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 1 /\ etable_values len i = 8).
Proof.
  intros i Hrange Hops.
  pose(Hlen := op_store_len_gate i Hrange).
  simpl in Hlen.
  replace (i+0) with i in * by lia.
  destruct (load_one_number_of_bytes i Hrange Hops) as [Hone | [Htwo | [Hfour | Height]]].
  - left. lia.
  - right. left. lia.
  - right. right. left. lia.
  - right. right. right. lia.
Qed.


Require Import ImageTableModel.
Require Import InjectivityHelper.

Lemma Store_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values ETableModel.enabled_cell i = 1 ->    
  etable_values (ops_cell Store) i = 1 ->
  exists lz off,
    program (wasm_pc st) = IStore (bool_of_Z (etable_values is_i32 i)) lz off
    /\ etable_values len i = len_of_LoadSize lz
    /\ etable_values opcode_store_offset i = Wasm_int.Int64.unsigned off.
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i Store Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  destruct  (load_one_number_of_bytes_len i Hrange Hops) as [Hsel | [Hsel | [Hsel | Hsel]]].
  - exists VAL8. exists (Wasm_int.Int64.repr (etable_values opcode_store_offset i)).
    split; [|split]; [| simpl; tauto | symmetry;  apply (common_unsigned_repr64 _ opcode_store_offset_common)].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl by (apply OpStoreModel.is_i32_bit).
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    f_equal.
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 Hsel5]]]]. 
    rewrite !Hsel2, !Hsel3, !Hsel4.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    f_equal.
    rewrite (common_unsigned_repr64 _ opcode_store_offset_common).
    reflexivity.
  - exists VAL16. exists (Wasm_int.Int64.repr (etable_values opcode_store_offset i)).
    split; [|split]; [| simpl; tauto | symmetry;  apply (common_unsigned_repr64 _ opcode_store_offset_common)].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl by (apply OpStoreModel.is_i32_bit).
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    f_equal.
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 Hsel5]]]]. 
    rewrite !Hsel2, !Hsel3, !Hsel4.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    f_equal.
    rewrite (common_unsigned_repr64 _ opcode_store_offset_common).
    reflexivity.
  - exists VAL32. exists (Wasm_int.Int64.repr (etable_values opcode_store_offset i)).
    split; [|split]; [| simpl; tauto | symmetry;  apply (common_unsigned_repr64 _ opcode_store_offset_common)].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl by (apply OpStoreModel.is_i32_bit).
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    f_equal.
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 Hsel5]]]]. 
    rewrite !Hsel2, !Hsel3, !Hsel4.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    f_equal.
    rewrite (common_unsigned_repr64 _ opcode_store_offset_common).
    reflexivity.
  - exists VAL64. exists (Wasm_int.Int64.repr (etable_values opcode_store_offset i)).
    split; [|split]; [| simpl; tauto | symmetry;  apply (common_unsigned_repr64 _ opcode_store_offset_common)].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl by (apply OpStoreModel.is_i32_bit).
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    f_equal.
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 Hsel5]]]]. 
    rewrite !Hsel2, !Hsel3, !Hsel4.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    f_equal.
    rewrite (common_unsigned_repr64 _ opcode_store_offset_common).
    reflexivity.
Qed.

Lemma load_block_inner_pos_bound : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    0 <= etable_values load_block_inner_pos i < WASM_BLOCK_BYTE_SIZE.
Proof.
  intros i Hrange Hops.
  pose(H := op_store_load_block_index_gate i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  pose(load_block_inner_pos_bits_0_bit i).
  pose(load_block_inner_pos_bits_1_bit i).
  pose(load_block_inner_pos_bits_2_bit i).
  unfold WASM_BLOCK_BYTE_SIZE.
  lia.
Qed.

Definition effective_address i := etable_values store_base i + etable_values opcode_store_offset i.

Lemma effective_address_value : forall i,
    0 <= i -> 
    etable_values (ops_cell Store) i = 1 ->
    effective_address i = 
    etable_values load_block_index i * WASM_BLOCK_BYTE_SIZE + etable_values load_block_inner_pos i.
Proof.
  intros i Hrange Hops.
  pose(H := op_store_load_block_index_gate i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  unfold effective_address.
  lia.
Qed.

Lemma effective_address_division_theorem : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    Z.div_eucl (effective_address i) WASM_BLOCK_BYTE_SIZE =
    (etable_values load_block_index i, etable_values load_block_inner_pos i).
Proof.
  intros i Hrange Hops.
  rewrite Zaux.Zdiv_eucl_unique.
  rewrite(effective_address_value i Hrange Hops).
  pose(load_block_inner_pos_bound i Hrange Hops).
  unfold WASM_BLOCK_BYTE_SIZE in *.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small by assumption.
  rewrite Z.add_0_r.
  rewrite Z.add_comm.
  rewrite Z_mod_plus by lia.
  rewrite Z.mod_small by assumption.
  reflexivity.
Qed.

Lemma cross_block_rem_range : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    0 <= etable_values cross_block_rem i < WASM_BLOCK_BYTE_SIZE.
Proof.
  intros i Hrange Hops.
  pose(H := op_store_cross_bloc i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  pose(cross_block_rem_diff_common i).
  unfold WASM_BLOCK_BYTE_SIZE.
  pose(cross_block_rem_common i).
  lia.
Qed.

Definition end_inner_byte i := 
    etable_values load_block_inner_pos i + etable_values len i - 1.

Lemma end_inner_byte_range : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    0 <= end_inner_byte i < (etable_values is_cross_block i + 1) * WASM_BLOCK_BYTE_SIZE.
Proof.
  intros i Hrange Hops.
  pose(H := op_store_cross_bloc i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  pose(Hbit := is_cross_block_bit i).
  unfold end_inner_byte.
  pose(Hremrange := cross_block_rem_range i Hrange).
  destruct Hbit as [? | ?]; [lia | lia].
Qed.

Lemma end_byte : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    Z.div_eucl (effective_address i + etable_values len i - 1) WASM_BLOCK_BYTE_SIZE = 
    (etable_values load_block_index i + etable_values is_cross_block i, etable_values cross_block_rem i).
Proof.
  intros i Hrange Hops.
  rewrite Zaux.Zdiv_eucl_unique.
  rewrite(effective_address_value i Hrange Hops).
  pose(H := op_store_cross_bloc i Hrange).
  simpl in H.
  replace (i+0) with i in H by lia.
  destruct H as [H _].
  pose(Hremrange := cross_block_rem_range i Hrange Hops).
  unfold WASM_BLOCK_BYTE_SIZE in *.
  replace(etable_values load_block_index i * 8 + etable_values load_block_inner_pos i + etable_values len i - 1)
  with (etable_values load_block_index i * 8 + (etable_values load_block_inner_pos i + etable_values len i - 1)) by lia.
  rewrite Z.div_add_l by congruence.
  replace(etable_values load_block_index i * 8 + (etable_values load_block_inner_pos i + etable_values len i - 1))
  with ((etable_values load_block_inner_pos i + etable_values len i - 1) + etable_values load_block_index i * 8) by lia.
  rewrite Z_mod_plus by lia.
  replace(etable_values load_block_inner_pos i + etable_values len i - 1)
  with (etable_values is_cross_block i * 8 + etable_values cross_block_rem i) by lia.
  rewrite Z.div_add_l by congruence.
  rewrite Z.div_small by assumption.
  rewrite(Z.add_comm _ (etable_values cross_block_rem i)).
  rewrite Z_mod_plus by lia.
  rewrite Z.mod_small by assumption.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma no_cross_block_no_heap2 : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values is_cross_block i = 0 ->
    etable_values load_value_in_heap2 i = 0.
Proof.
  intros i Hrange Hops.
  pose(H := op_store_cross_bloc i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  lia.
Qed.

Lemma len_modulus_range : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values len_modulus i = 2^8
 \/ etable_values len_modulus i = 2^16
 \/ etable_values len_modulus i = 2^32
 \/ etable_values len_modulus i = 2^64.
Proof.
  intros i Hrange Hops.
  pose(H := op_store_len_modulus_gate i Hrange).
  simpl in *.
  replace (i+0) with i in * by lia.
  pose(Hbytes := load_one_number_of_bytes i).
  lia.
Qed.

Lemma unchanged_value_is_tail_and_lead : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values unchanged_value i = etable_values load_tailing i +
    etable_values load_leading i * etable_values lookup_pow_modulus i *
    etable_values len_modulus i.
Proof.
  intros i Hrange Hops.
  pose(H := op_store_pick_value1 i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Definition loaded_value i := 
    etable_values load_value_in_heap1 i 
  + etable_values load_value_in_heap2 i * 2^64.

Lemma loaded_value_decomposition : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    loaded_value i = etable_values unchanged_value i + 
    etable_values load_picked_u64_cell i * etable_values lookup_pow_modulus i.
Proof.
  intros i Hrange Hops.
  pose(H := op_store_pick_value2 i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  unfold loaded_value.
  lia.
Qed.

Definition stored_value i := 
    etable_values store_value_in_heap1 i 
  + etable_values store_value_in_heap2 i * 2^64.

Lemma stored_value_decomposition : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    stored_value i = etable_values unchanged_value i + 
    etable_values store_value_wrapped i * etable_values lookup_pow_modulus i.
Proof.
  intros i Hrange Hops.
  pose(H := op_store_pick_value3 i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  unfold stored_value.
  lia.
Qed.

Lemma load_tailing_range : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    0 <= etable_values load_tailing i < etable_values lookup_pow_modulus i.
Proof.
  intros i Hrange Hops.
  pose(H := op_store_pick_helper_value_check i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  pose(load_tailing_U64 i).
  pose(load_tailing_diff_U64 i).
  lia.
Qed.

Lemma len_modulus_and_len : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values len_modulus i = 2^(etable_values len i * 8).
Proof.
  intros i Hrange Hops.
  pose(Hmodulus := op_store_len_modulus_gate i Hrange).
  pose(Hlen := op_store_len_gate i Hrange).
  simpl in *.
  replace(i+0) with i in * by lia.
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

Lemma load_picked_upper_bits_four_bytes_case : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values is_four_bytes i = 1 ->
    etable_values load_picked_u16_cells_le_2 i = 0 /\
    etable_values load_picked_u16_cells_le_3 i = 0.
Proof.
  intros i Hrange Hops Hfour.
  pose(H := op_store_pick_value_size_check i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  destruct H as [? _].
  pose(load_picked_u16_cells_le_2_U16 i).
  pose(load_picked_u16_cells_le_3_U16 i).
  lia.
Qed.

Lemma load_picked_length_four_bytes_case : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values is_four_bytes i = 1 ->
    0 <= etable_values load_picked_u64_cell i < 2^32.
Proof.
  intros i Hrange Hops Hfour.
  pose(Hu64 := load_picked_U64 i).
  pose(Hupper := load_picked_upper_bits_four_bytes_case i Hrange Hops Hfour).
  destruct Hupper.
  rewrite H, H0 in Hu64.
  simpl in Hu64.
  pose(load_picked_u16_cells_le_0_U16 i).
  pose(load_picked_u16_cells_le_1_U16 i).
  lia.
Qed.

Lemma load_picked_length_two_bytes_case : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values is_two_bytes i = 1 ->
    0 <= etable_values load_picked_u64_cell i < 2^16.
Proof. 
  intros i Hrange Hops Htwo.
  pose(H := op_store_pick_value_size_check i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [H _]].
  pose(load_picked_u16_cells_le_0_U16 i).
  lia.
Qed.

Lemma load_picked_length_one_byte_case : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values is_one_byte i = 1 ->
    0 <= etable_values load_picked_u64_cell i < 2^8.
Proof.
  intros i Hrange Hops Hone.
  pose(H := op_store_pick_value_size_check i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [_ [H _]]].
  pose(load_picked_byte_proof_U8 i).
  lia.
Qed.

(* Loaded value has the correct number of bytes *)
Lemma load_size : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    0 <= etable_values load_picked_u64_cell i < etable_values len_modulus i.
Proof.
  intros i Hrange Hops.
  pose(H := op_store_len_modulus_gate i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  pose(Hbytes := load_one_number_of_bytes i Hrange Hops).
  destruct Hbytes as [Hone | [Htwo | [Hfour | Height]]].
  - replace(etable_values len_modulus i) with (2^8) by lia.
    destruct Hone as [Hone _].
    apply(load_picked_length_one_byte_case i Hrange Hops Hone).
  - replace(etable_values len_modulus i) with (2^16) by lia.
    destruct Htwo as [_ [Htwo _]].
    apply(load_picked_length_two_bytes_case i Hrange Hops Htwo).
  - replace(etable_values len_modulus i) with (2^32) by lia.
    destruct Hfour as [_ [_ [Hfour _]]].
    apply(load_picked_length_four_bytes_case i Hrange Hops Hfour).
  - pose(Hu64 := load_picked_U64 i).
    pose(load_picked_u16_cells_le_0_U16 i).
    pose(load_picked_u16_cells_le_1_U16 i).
    pose(load_picked_u16_cells_le_2_U16 i).
    pose(load_picked_u16_cells_le_3_U16 i).
    lia.
Qed.

Lemma store_value_tailing_u16_decomposition : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values store_value_u16_cells_le_0 i =
    etable_values store_value_tailing_u16_u8_high i * 2^8 +
    etable_values store_value_tailing_u16_u8_low i.
Proof.
  intros i Hrange Hops.
  pose(H := op_store_tailing_u16_decompose i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Lemma store_value_wrapped_value : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values store_value_wrapped i =
    etable_values store_value_u64_cell i mod (etable_values len_modulus i).
Proof.
  intros i Hrange Hops.
  pose(Hsvwrap := op_store_value_wrap i Hrange).
  pose(Hmod := op_store_len_modulus_gate i Hrange); simpl in *.
  replace(i+0) with i in * by lia.
  pose(Hsval := store_value_U64 i).
  destruct(load_one_number_of_bytes i Hrange Hops) as [Hone | [Htwo | [Hfour | Height]]].
  - replace(etable_values len_modulus i) with (2^8) by lia.
    replace(etable_values store_value_u64_cell i) with 
      (etable_values store_value_u16_cells_le_0 i +
      (etable_values store_value_u16_cells_le_1 i * 2 ^ 8 +
      etable_values store_value_u16_cells_le_2 i * 2 ^ 24 +
      etable_values store_value_u16_cells_le_3 i * 2 ^ 40) * 2^8) by lia.
    rewrite Z_mod_plus by lia.
    rewrite(store_value_tailing_u16_decomposition i Hrange Hops).
    rewrite Z.add_comm.
    rewrite Z_mod_plus by lia.
    rewrite Z.mod_small by apply (store_value_tailing_u16_u8_low_U8 i).
    lia.
  - replace(etable_values len_modulus i) with (2^16) by lia.
    replace(etable_values store_value_u64_cell i) with 
      (etable_values store_value_u16_cells_le_0 i +
      (etable_values store_value_u16_cells_le_1 i +
      etable_values store_value_u16_cells_le_2 i * 2 ^ 16 +
      etable_values store_value_u16_cells_le_3 i * 2 ^ 32) * 2^16) by lia.
    rewrite Z_mod_plus by lia.
    rewrite Z.mod_small by apply (store_value_u16_cells_le_0_U16 i).
    lia.
  - replace(etable_values len_modulus i) with (2^32) by lia.
    replace(etable_values store_value_u64_cell i) with 
      (etable_values store_value_u16_cells_le_0 i +
      etable_values store_value_u16_cells_le_1 i * 2^16 +
      (etable_values store_value_u16_cells_le_2 i +
      etable_values store_value_u16_cells_le_3 i * 2 ^ 16) * 2^32) by lia.
    rewrite Z_mod_plus by lia.
    pose(store_value_u16_cells_le_0_U16 i).
    pose(store_value_u16_cells_le_1_U16 i).
    rewrite Z.mod_small by lia.
    lia.
  - replace(etable_values len_modulus i) with (2^64) by lia.
    pose(store_value_u16_cells_le_0_U16 i).
    pose(store_value_u16_cells_le_1_U16 i).
    pose(store_value_u16_cells_le_2_U16 i).
    pose(store_value_u16_cells_le_3_U16 i).
    rewrite Z.mod_small by lia.
    lia.
Qed.

Lemma store_value_wrapped_range : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    0 <= etable_values store_value_wrapped i < etable_values len_modulus i.
Proof.
  intros i Hrange Hops.
  rewrite store_value_wrapped_value; auto.
  apply Z.mod_pos_bound.
  pose(len_modulus_range i Hrange Hops).
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
       
Lemma lookup_pow_modulus_value : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values lookup_pow_modulus i = 2^(etable_values load_block_inner_pos i * 8).
Proof.
  intros i Hrange Hops.
  pose(H := op_store_pow_lookup i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  assert (Hpower_lookup_nonzero : etable_values lookup_pow_power i <> 0).
  {
    pose (load_block_inner_pos_bound i Hrange Hops).
    lia.
  }  
  replace(etable_values load_block_inner_pos i * 8) with
    (etable_values lookup_pow_power i - 128) by lia.
  apply(lookup_pow_values i Hrange Hpower_lookup_nonzero).
Qed.

Lemma memory_pages_not_exceeded : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values load_block_index i + etable_values is_cross_block i <
    etable_values mpages_cell i * WASM_BLOCKS_PER_PAGE.
Proof.
  intros i Hrange Hops.
  pose(H := op_store_allocated_address i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  pose(Hadd := address_within_allocated_pages_helper_common i).
  lia.
Qed.

Lemma load_picked_starts_at_load_block_inner_pos : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    Z.shiftr (loaded_value i) (etable_values load_block_inner_pos i * 8) =
    etable_values load_leading i * etable_values len_modulus i
    + etable_values load_picked_u64_cell i.
intros i Hrange Hops.
  rewrite loaded_value_decomposition; auto.
  rewrite unchanged_value_is_tail_and_lead; auto.
  pose(Hinner := load_block_inner_pos_bound i Hrange Hops).
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite lookup_pow_modulus_value; auto.
  rewrite Z.add_comm.
  rewrite Z.div_add_l by lia.
  rewrite(Z.add_comm (etable_values load_tailing i) _).
  rewrite <- Z.mul_assoc.
  rewrite(Z.mul_comm _ (etable_values len_modulus i)).
  rewrite Z.mul_assoc.
  rewrite Z.div_add_l by lia.
  rewrite <- lookup_pow_modulus_value; auto.
  rewrite Z.div_small by apply (load_tailing_range i Hrange Hops).
  lia.
Qed.

Lemma load_picked_from_loaded_value : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values load_picked_u64_cell i = 
    (Z.shiftr (loaded_value i) (etable_values load_block_inner_pos i * 8)) mod (etable_values len_modulus i).
Proof.
  intros i Hrange Hops.
  rewrite(load_picked_starts_at_load_block_inner_pos i Hrange Hops).
  pose(load_size i Hrange Hops).
  rewrite Z.add_comm.
  rewrite Z_mod_plus by lia.
  rewrite Z.mod_small; auto.
Qed.

Lemma store_value_wrapped_starts_at_load_block_inner_pos : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    Z.shiftr (stored_value i) (etable_values load_block_inner_pos i * 8) =
    etable_values load_leading i * etable_values len_modulus i
    + etable_values store_value_wrapped i.
Proof.
  intros i Hrange Hops.
  rewrite stored_value_decomposition; auto.
  rewrite unchanged_value_is_tail_and_lead; auto.
  pose(Hinner := load_block_inner_pos_bound i Hrange Hops).
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite lookup_pow_modulus_value; auto.
  rewrite Z.add_comm.
  rewrite Z.div_add_l by lia.
  rewrite(Z.add_comm (etable_values load_tailing i) _).
  rewrite <- Z.mul_assoc.
  rewrite(Z.mul_comm _ (etable_values len_modulus i)).
  rewrite Z.mul_assoc.
  rewrite Z.div_add_l by lia.
  rewrite <- lookup_pow_modulus_value; auto.
  rewrite Z.div_small by apply (load_tailing_range i Hrange Hops).
  lia.
Qed.

Lemma store_value_wrapped_from_stored_value : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    etable_values store_value_wrapped i = 
    (Z.shiftr (stored_value i) (etable_values load_block_inner_pos i * 8)) mod (etable_values len_modulus i).
Proof.
  intros i Hrange Hops.
  rewrite(store_value_wrapped_starts_at_load_block_inner_pos i Hrange Hops).
  pose(store_value_wrapped_range i Hrange Hops).
  rewrite Z.add_comm.
  rewrite Z_mod_plus by lia.
  rewrite Z.mod_small; auto.
Qed.

Require Import CommonMemory.

Lemma heap_rel_write : forall m p mp mem blk z,
  heap_rel m p mp mem ->
  0 <= blk ->
  0 <= z < 2^64 ->
  8 * blk + 8 <= Z.of_N (mem_length mem) ->
  exists mem',
    write_bytes mem (8 * Z.to_N blk) (Memdata.encode_int 8 z) = Some mem' /\ 
    heap_rel (set m blk z) p mp mem'.
Proof.
  intros until z. intros Hrel Hblk Hz Hlen.
  eapply CommonMemory.heap_rel_write; eassumption.
Qed.

Lemma heap_rel_write_combined : forall m p mp mem blk z z' x y,
  0 <= x < 8 ->
  0 < y <= 8 ->
  x < y ->
  0 <= z < 2^64 ->
  0 <= z' < 2 ^ 64 ->
  0 <= blk ->
  heap_rel m p mp mem ->
  8 * blk + 8 <= Z.of_N (mem_length mem) ->
  read_bytes mem (8 * Z.to_N blk) 8 = Some (Memdata.encode_int 8 z) ->
  z mod 2^(8 * x) = z' mod 2^(8 * x) ->
  Z.shiftr z (8 * y) = Z.shiftr z' (8 * y) ->
  exists mem',
    write_bytes mem (8 * Z.to_N blk + Z.to_N x)
    (Memdata.encode_int (Z.to_nat (y - x)) (Z.shiftr z' (8 * x))) = Some mem' /\
    heap_rel (set m blk z') p mp mem'.
Proof.
  intros m p mem blk z z' x y Hx Hy Hxy Hz Hheap_rel Hblk Hread Hmod Hshiftr.
  eapply CommonMemory.heap_rel_write_combined; eauto.
Qed.

Lemma heap_rel_write_same_lower_bits : forall m p mp mem blk z z' x,
  0 <= x < 8 ->
  0 <= z < 2^64 ->
  0 <= z' < 2^64 ->
  0 <= blk ->
  heap_rel m p mp mem ->
  8 * blk + 8 <= Z.of_N (mem_length mem) ->
  read_bytes mem (8 * Z.to_N blk) 8 = Some (Memdata.encode_int 8 z) ->
  z mod 2^(8 * x) = z' mod 2^(8 * x) ->
  exists mem',
    write_bytes mem (8 * Z.to_N blk + Z.to_N x) 
    (Memdata.encode_int (8 - Z.to_nat x) (Z.shiftr z' (8 * x))) = Some mem' /\ 
    heap_rel (set m blk z') p mp mem'.
Proof.
  intros m p mp mem blk z z' x Hx Hz Hz' Hblk Hheap_rel Hblk_len Hread Hmod.
  rewrite <- (Z2Nat.inj_sub 8 _) by lia.
  apply heap_rel_write_combined with (z:= z); auto; try lia.
  change (8*8) with 64.
  repeat rewrite Z.shiftr_div_pow2 by lia.
  repeat rewrite Z.div_small by lia.
  reflexivity.
Qed.

Lemma heap_rel_write_same_upper_bits : forall m p mp mem blk z z' x,
  0 < x <= 8 ->
  0 <= z < 2^64 ->
  0 <= z' < 2^64 ->
  0 <= blk ->
  heap_rel m p mp mem ->
  8 * blk + 8 <= Z.of_N (mem_length mem) ->
  read_bytes mem (8 * Z.to_N blk) 8 = Some (Memdata.encode_int 8 z) ->
  Z.shiftr z (8 * x) = Z.shiftr z' (8 * x) ->
  exists mem',
    write_bytes mem (8 * Z.to_N blk) (Memdata.encode_int (Z.to_nat x) z') = Some mem' /\ 
    heap_rel (set m blk z') p mp mem'.
Proof.
  intros m p mp mem blk z z' x Hx Hz Hz' Hblk Hheap_rel Hblk_len Hread Hmod.
  replace (8 * Z.to_N blk)%N with (8 * Z.to_N blk + Z.to_N 0)%N by lia.
  replace (Z.to_nat x) with (Z.to_nat (x - 0)) by lia.
  replace z' with (Z.shiftr z' (8 * 0)).
  apply heap_rel_write_combined with (z:= z); auto; try lia.
  - rewrite Z.shiftr_0_r.
    change(2^(8*0)) with 1.
    repeat rewrite Z.mod_1_r; auto.
  - rewrite Z.shiftr_0_r; auto.
Qed.

Lemma write_bytes_combine : forall mem mem' mem'' addr {len1 len2 : nat} val1 val2,
  0 <= val1 < 2 ^ (8 * Z.of_nat len1) ->
  (addr + N.of_nat (len1 + len2) <= mem_length mem)%N ->
  write_bytes mem addr
    (Memdata.encode_int len1 val1) = Some mem' ->
  write_bytes mem' (addr + N.of_nat len1) 
    (Memdata.encode_int len2 val2) = Some mem'' ->
  write_bytes mem addr
    (Memdata.encode_int (len1 + len2) 
    (val2 * 2^(Z.of_nat len1 * 8) + val1 mod 2^(Z.of_nat len1 * 8))) = Some mem''.
Proof.
  intros mem mem' mem'' addr len1 len2 val1 val2 Hval1 Hlen Hwrite1 Hwrite2.
  eapply CommonMemory.write_bytes_combine' ; eassumption.
Qed.

Lemma load_block_index_range : forall i mem,
  0 <= i ->
  etable_values (ops_cell Store) i = 1 ->
  etable_values mpages_cell i = Z.of_N (mem_size mem) ->
  ml_valid (mem_data mem) ->
  etable_values load_block_index i * WASM_BLOCK_BYTE_SIZE + 8 +
  (etable_values is_cross_block i * 8) <= Z.of_N (mem_length mem).
Proof.
  intros i mem Hrange Hops Hsz Hmvalid.
  pose(Hpages := memory_pages_not_exceeded i Hrange Hops).
  unfold WASM_BLOCK_BYTE_SIZE, WASM_BLOCKS_PER_PAGE in *.
  destruct (is_cross_block_bit i) as [H0 | H1].
  - rewrite H0 in *.
    assert(etable_values load_block_index i + 1 <= Z.of_N (mem_size mem) * 8192).
    - lia.
    unfold mem_size in H.
    unfold ml_valid in Hmvalid.
    unfold page_size in *.
    simpl in Hmvalid, H.
    assert (65536 | Z.of_N (mem_length mem)).
    - apply Znumtheory.Zmod_divide; try lia.
      unfold mem_length.
      apply (f_equal Z.of_N) in Hmvalid.
      rewrite N2Z.inj_mod in Hmvalid.
      simpl in Hmvalid; auto.
    rewrite N2Z.inj_div in H.
    apply (Zmult_le_compat_r _ _ 8) in H; try lia.
    replace (Z.of_N (mem_length mem) / Z.of_N 65536 * 8192 * 8) with
      (65536 * (Z.of_N (mem_length mem) / 65536)) in H by lia.
    rewrite <- Znumtheory.Zdivide_Zdiv_eq_2 in H; auto; try lia.
    rewrite (Z.mul_comm 65536 _) in H.
    rewrite Z_div_mult in H; try lia.
  - rewrite H1 in *.
    assert(etable_values load_block_index i + 1 + 1 <= Z.of_N (mem_size mem) * 8192).
    - lia.
    unfold mem_size in H.
    unfold ml_valid in Hmvalid.
    unfold page_size in *.
    simpl in Hmvalid, H.
    assert (65536 | Z.of_N (mem_length mem)).
    - apply Znumtheory.Zmod_divide; try lia.
      unfold mem_length.
      apply (f_equal Z.of_N) in Hmvalid.
      rewrite N2Z.inj_mod in Hmvalid.
      simpl in Hmvalid; auto.
    rewrite N2Z.inj_div in H.
    apply (Zmult_le_compat_r _ _ 8) in H; try lia.
    replace (Z.of_N (mem_length mem) / Z.of_N 65536 * 8192 * 8) with
      (65536 * (Z.of_N (mem_length mem) / 65536)) in H by lia.
    rewrite <- Znumtheory.Zdivide_Zdiv_eq_2 in H; auto; try lia.
    rewrite (Z.mul_comm 65536 _) in H.
    rewrite Z_div_mult in H; try lia.
Qed.

Lemma store_value_in_heap1_range : forall i,
  0 <= i ->
  etable_values (ops_cell Store) i = 1 ->
  0 <= etable_values store_value_in_heap1 i < 2^64.
Proof.
  intros i Hrange Hops.
  eapply write_with_value_range with 
    (is_i32 := fun get => 0)
    (sp := fun get => get load_block_index)
    (enable := fun get => get (ops_cell Store))
    (loctyp := MTableModel.LocationType_Heap); auto.
  - pose(load_block_index_common i); lia.
  - apply heap_write1.
Qed.

Lemma write_heap1 : forall i mem,
  0 <= i ->
  etable_values (ops_cell Store) i = 1 ->
  heap_rel (heap_map (etable_values eid_cell i)) (etable_values mpages_cell i) (etable_values maximal_memory_pages_cell i) mem ->
  exists new_mem,
    write_bytes mem (8 * Z.to_N (etable_values load_block_index i)) 
    (Memdata.encode_int 8 (etable_values store_value_in_heap1 i)) = Some (new_mem) /\
    heap_rel (set (heap_map (etable_values eid_cell i)) 
      (etable_values load_block_index i) 
      (etable_values store_value_in_heap1 i))
      (etable_values mpages_cell i)
      (etable_values maximal_memory_pages_cell i)
      new_mem.
Proof.
  intros i mem Hrange Hops Hheap_rel.
  apply(heap_rel_write _ _ _ _
    (etable_values load_block_index i)
    (etable_values store_value_in_heap1 i) 
    Hheap_rel).
  - apply load_block_index_common.
  - apply store_value_in_heap1_range; auto.
  - destruct Hheap_rel.
    pose(load_block_index_range i mem Hrange Hops heap_size heap_valid).
    pose(is_cross_block_bit i).
    unfold WASM_BLOCK_BYTE_SIZE in *.
    lia.
Qed.

Lemma load_value_in_heap1_range : forall i,
  0 <= i ->
  etable_values (ops_cell Store) i = 1 ->
  0 <= etable_values load_value_in_heap1 i < 2^64.
Proof.
  intros i Hrange Hops.
  eapply read_with_value_range with 
    (is_i32 := fun get => 0)
    (sp := fun get => get load_block_index)
    (enable := fun get => get (ops_cell Store))
    (loctyp := MTableModel.LocationType_Heap); auto.
  - pose(load_block_index_common i); lia.
  - apply heap_read1.
Qed.

Lemma load_value_in_heap2_range : forall i,
  0 <= i ->
  etable_values (ops_cell Store) i = 1 ->
  etable_values is_cross_block i = 1 ->
  0 <= etable_values load_value_in_heap2 i < 2^64.
Proof.
  intros i Hrange Hops Hcb.
  eapply read_with_value_range with 
    (is_i32 := fun get => 0)
    (sp := fun get => get load_block_index + 1)
    (enable := fun get => get (ops_cell Store) * get is_cross_block)
    (loctyp := MTableModel.LocationType_Heap); auto.
  - pose(load_block_index_common i); lia.
  - lia.
  - apply heap_read2.
Qed.

Lemma read_heap1 : forall i mem,
  0 <= i ->
  etable_values (ops_cell Store) i = 1 ->
  heap_rel (heap_map (etable_values eid_cell i)) (etable_values mpages_cell i) (etable_values maximal_memory_pages_cell i) mem ->
  exists bs,
    read_bytes mem (8 * Z.to_N (etable_values load_block_index i)) 8 =
    Some bs /\ Memdata.decode_int bs = etable_values load_value_in_heap1 i.
Proof.
  intros i mem Hrange Hops Hheap_rel .
  apply (heap_rel_lookup _ _ _ _ Hheap_rel).
  - destruct Hheap_rel.
    pose(Hl := load_block_index_range i mem Hrange Hops heap_size heap_valid).
    unfold WASM_BLOCK_BYTE_SIZE in *.
    pose(is_cross_block_bit i).
    pose(load_block_index_common i).
    rewrite Z2N.inj_le in Hl; lia.
  - eapply mtable_read with (is_i32 := 0).
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
Qed.

Lemma read_heap2 : forall i mem,
  0 <= i ->
  etable_values (ops_cell Store) i = 1 ->
  heap_rel (heap_map (etable_values eid_cell i)) (etable_values mpages_cell i) (etable_values maximal_memory_pages_cell i) mem ->
  etable_values is_cross_block i = 1 ->
  exists bs,
    read_bytes mem (8 * Z.to_N (etable_values load_block_index i + 1)) 8 =
    Some bs /\ Memdata.decode_int bs = etable_values load_value_in_heap2 i.
Proof.
  intros i mem Hrange Hops Hheap_rel Hcross.
  apply (heap_rel_lookup _ _ _ _ Hheap_rel).
  - destruct Hheap_rel.
    pose(Hl := load_block_index_range i mem Hrange Hops heap_size heap_valid).
    unfold WASM_BLOCK_BYTE_SIZE in *.
    pose(load_block_index_common i).
    rewrite Z2N.inj_le in Hl; lia.
  - eapply mtable_read with (is_i32 := 0).
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
Qed.

Lemma encode_decode : forall n b,
  length b = n ->
  Memdata.encode_int n (Memdata.decode_int b) = b.
Proof.
  unfold Memdata.decode_int.
  unfold Memdata.encode_int.
  unfold Memdata.rev_if_be.
  induction n.
  - intros.
    assert(b = nil).
    - destruct b; auto.
      simpl in H.
      discriminate.
    rewrite H0.
    destruct Archi.big_endian; simpl; auto.
  - intros.
    destruct b.
    - discriminate.
    - simpl in H.
      inversion H.
      rewrite H1.
      replace (S n) with (n + 1)%nat by lia.
      destruct Archi.big_endian.
      - simpl.
        rewrite Memdata.int_of_bytes_append.
        rewrite rev_length.
        rewrite H1.
        rewrite Memdata.bytes_of_int_append.
        rewrite rev_app_distr.
        rewrite (IHn b H1).
        simpl.
        rewrite Z.add_0_r.
        rewrite Integers.Byte.repr_unsigned; auto.
        rewrite <- H1.
        rewrite <- rev_length.
        apply Memdata.int_of_bytes_range.
      - change (i :: b) with ((i :: nil) ++ b).
        replace (n+1)%nat with (1+n)%nat by lia.
        rewrite Memdata.int_of_bytes_append.
        rewrite Memdata.bytes_of_int_append.
        rewrite (IHn b H1).
        simpl.
        rewrite Z.add_0_r.
        rewrite Integers.Byte.repr_unsigned; auto.
        apply Memdata.int_of_bytes_range.
Qed.     

Lemma two_le_mul : forall a b n m,
  0 <= a < n ->
  0 <= b < m ->
  0 <= a * m + b < m * n.
Proof.
  intros.
  assert(0 <= a <= n - 1). lia.
  assert(0 <= m). lia.
  destruct H1.
  apply(Z.mul_le_mono_nonneg_r a (n-1) m H2) in H3.
  lia.
Qed.

Lemma shiftr_eq_0 : forall a n,
  0 <= a ->
  0 <= n ->
  Z.shiftr a n = 0 ->
  a < 2^n.
Proof.
  intros.
  rewrite Z.shiftr_div_pow2 in H1; auto.
  rewrite Z.div_small_iff in H1 by lia.
  destruct H1; lia.
Qed.

Lemma no_cross_block_no_store_heap2 : forall i,
  0 <= i ->
  etable_values (ops_cell Store) i = 1 ->
  etable_values is_cross_block i = 0 ->
  etable_values store_value_in_heap2 i = 0.
Proof.
  intros i Hrange Hops Hcb.
  assert(0 <= stored_value i).
  - rewrite stored_value_decomposition; auto.
    rewrite unchanged_value_is_tail_and_lead; auto.
    pose(load_tailing_range i Hrange Hops).
    pose(load_leading_U64 i).
    pose(store_value_wrapped_range i Hrange Hops).
    assert(0 <= etable_values lookup_pow_modulus i). lia.
    assert(0 <= etable_values len_modulus i). lia.
    lia.
  assert(stored_value i < 2^64).
  - apply shiftr_eq_0; try lia.
    rewrite stored_value_decomposition; auto.
    assert(Hl : Z.shiftr (loaded_value i) 64 = 0).
    - unfold loaded_value.
      rewrite no_cross_block_no_heap2; auto.
      pose(load_value_in_heap1_range i Hrange Hops).
      rewrite Z.mul_0_l, Z.add_0_r.
      rewrite Z.shiftr_div_pow2 by lia.
      rewrite Z.div_small by lia; auto.
    rewrite loaded_value_decomposition in Hl; auto.
    rewrite unchanged_value_is_tail_and_lead in *; auto.
    pose(load_tailing_range i Hrange Hops).
    pose(load_block_inner_pos_bound i Hrange Hops).
    unfold WASM_BLOCK_BYTE_SIZE in *.
    rewrite lookup_pow_modulus_value in *; auto.
    replace 64 with (etable_values load_block_inner_pos i * 8 + (64 - 
      etable_values load_block_inner_pos i * 8)) in * by lia.
    rewrite <- Z.shiftr_shiftr in * by lia.
    rewrite(Z.shiftr_div_pow2 _ (etable_values load_block_inner_pos i * 8)) in Hl by lia.
    rewrite(Z.shiftr_div_pow2 _ (etable_values load_block_inner_pos i * 8)) by lia.
    rewrite Z.div_add in * by lia.
    rewrite Z.mul_comm in *.
    rewrite Z.mul_assoc in *.
    rewrite(Z.mul_comm _ 8) in *.
    rewrite Z.div_add in * by lia.
    rewrite Z.div_small in * by lia.
    rewrite Z.add_0_l in *.
    rewrite len_modulus_and_len in *; auto.
    replace (64 - 8 * etable_values load_block_inner_pos i) with 
      (etable_values len i * 8 + (64 - 
      etable_values load_block_inner_pos i * 8 - etable_values len i * 8)) in * by lia.
    pose(end_inner_byte_range i Hrange Hops).
    unfold end_inner_byte, WASM_BLOCK_BYTE_SIZE in *.
    rewrite <- Z.shiftr_shiftr in * by lia.
    pose(len_value i Hrange Hops).
    rewrite(Z.shiftr_div_pow2 _ (etable_values len i * 8)) by lia.
    rewrite(Z.shiftr_div_pow2 _ (etable_values len i * 8)) in Hl by lia.
    rewrite(Z.mul_comm _ (etable_values load_leading i)) in *.
    rewrite Z.div_add_l in * by lia.
    pose(store_value_wrapped_range i Hrange Hops).
    pose(load_size i Hrange Hops).
    rewrite len_modulus_and_len in *; auto.
    rewrite Z.div_small in * by lia.
    auto.
  unfold stored_value in *.
  pose(store_value_in_heap1_range i Hrange Hops).
  lia.
Qed.

Lemma store_value_in_heap2_range : forall i,
  0 <= i ->
  etable_values (ops_cell Store) i = 1 ->
  0 <= etable_values store_value_in_heap2 i < 2^64.
Proof.
  intros i Hrange Hops.
  destruct (is_cross_block_bit i).
  - rewrite no_cross_block_no_store_heap2; auto; lia.
  - eapply write_with_value_range with 
      (is_i32 := fun get => 0)
      (sp := fun get => get load_block_index + 1)
      (enable := fun get => get (ops_cell Store) * get is_cross_block)
      (loctyp := MTableModel.LocationType_Heap); auto.
    - pose(load_block_index_common i); lia.
    - lia.
    - apply heap_write2.
Qed.

Lemma cross_block_inner_pos_plus_len_range : forall i,
  0 <= i ->
  etable_values (ops_cell Store) i = 1 ->
  etable_values is_cross_block i = 1 ->
  8 < etable_values load_block_inner_pos i + etable_values len i <= 16.
Proof.
  intros i Hrange Hops Hcb.
  pose(H := op_store_cross_bloc i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  pose(cross_block_rem_range i Hrange Hops).
  unfold WASM_BLOCK_BYTE_SIZE in *.
  lia.
Qed.

Lemma encode_eq : forall n x y,
  x mod two_p (Z.of_nat n * 8) = y mod two_p (Z.of_nat n * 8) ->
  Memdata.encode_int n x = Memdata.encode_int n y.
Proof.
  intros.
  repeat rewrite <- Memdata.decode_encode_int in H.
  apply (f_equal (fun t => Memdata.encode_int n t)) in H.
  rewrite encode_decode in H by apply Memdata.encode_int_length.
  rewrite encode_decode in H by apply Memdata.encode_int_length; auto.
Qed.

Lemma shiftr_distr : forall k x y,
  k >= 0 ->
  Z.land x y = 0 ->
  Z.shiftr x k + Z.shiftr y k = Z.shiftr (x + y) k.
Proof.
  intros.
  repeat rewrite(Z.add_nocarry_lxor); auto.
  rewrite Z.shiftr_lxor; auto.
  rewrite <- Z.shiftr_land.
  rewrite H0.
  rewrite Z.shiftr_0_l; auto.
Qed.

Require Import IntegerFunctions.

Lemma land_0 : forall n x y,
  (0 <= n)%nat ->
  0 <= x < 2^(Z.of_nat n) ->
  Z.land x (Z.shiftl y (Z.of_nat n)) = 0.
Proof.
  intros n x y Hn xbound.
  apply Zbits.equal_same_bits. intros k kbound.
  rewrite Z.land_spec.
  rewrite Z.bits_0.
  destruct (Z.lt_decidable k (Z.of_nat n)) as [H|H].
  - rewrite Z.shiftl_spec_low by auto.
  rewrite Bool.andb_false_r.
  reflexivity.
  - rewrite bound_spec_n in xbound; [|lia|lia].
    specialize (xbound k).
    apply Znot_lt_ge in H.
    apply Z.ge_le in H.
    specialize(xbound H).
    rewrite xbound.
    rewrite Bool.andb_false_l.
    reflexivity.
Qed. 

Require OpLoadHelper.

Lemma write_store_value : forall i mem,
  0 <= i ->
  etable_values (ops_cell Store) i = 1 ->
  heap_rel (heap_map (etable_values eid_cell i)) (etable_values mpages_cell i) (etable_values maximal_memory_pages_cell i) mem ->
  exists new_mem,
    write_bytes mem (Z.to_N (effective_address i)) 
    (Memdata.encode_int (Z.to_nat (etable_values len i)) (etable_values store_value_u64_cell i))
    = Some (new_mem) /\ 
    (etable_values is_cross_block i = 0 ->
    heap_rel (set (heap_map (etable_values eid_cell i))
      (etable_values load_block_index i)
      (etable_values store_value_in_heap1 i))
      (etable_values mpages_cell i)
      (etable_values maximal_memory_pages_cell i)
      new_mem) /\
    (etable_values is_cross_block i = 1 ->
    heap_rel (set (set (heap_map (etable_values eid_cell i))
      (etable_values load_block_index i)
      (etable_values store_value_in_heap1 i))
      (etable_values load_block_index i + 1)
      (etable_values store_value_in_heap2 i))
      (etable_values mpages_cell i)
      (etable_values maximal_memory_pages_cell i)
      new_mem).
Proof.
  intros i mem Hrange Hops Hheap_rel.
  rewrite effective_address_value; auto.
  pose(load_block_index_common i).
  pose(load_block_inner_pos_bound i Hrange Hops).
  unfold WASM_BLOCK_BYTE_SIZE in *.
  rewrite Z2N.inj_add by lia.
  rewrite Z.mul_comm.
  rewrite Z2N.inj_mul by lia.
  change (Z.to_N 8) with 8%N.
  destruct (is_cross_block_bit i) as [H0 | H1].
  - assert(exists mem',
    write_bytes mem (8 * Z.to_N (etable_values load_block_index i) + Z.to_N (etable_values load_block_inner_pos i))
      (Memdata.encode_int (Z.to_nat 
        ((etable_values load_block_inner_pos i + etable_values len i) - 
        (etable_values load_block_inner_pos i)))
      (Z.shiftr (stored_value i) (8 * etable_values load_block_inner_pos i))) = Some mem' /\ 
    heap_rel (set (heap_map (etable_values eid_cell i)) 
      (etable_values load_block_index i) (stored_value i)) 
      (etable_values current_memory_page_size i)
      (etable_values maximal_memory_pages_cell i) mem').
    apply heap_rel_write_combined with (z:= (etable_values load_value_in_heap1 i)); auto; try lia.
    - pose(end_inner_byte_range i Hrange Hops).
      unfold end_inner_byte in *.
      unfold WASM_BLOCK_BYTE_SIZE in *.
      lia.
    - pose(len_value i Hrange Hops); lia.
    - apply load_value_in_heap1_range; auto.
    - unfold stored_value.
      rewrite no_cross_block_no_store_heap2; auto.
      rewrite Z.mul_0_l, Z.add_0_r.
      apply store_value_in_heap1_range; auto.
    - destruct Hheap_rel.
      pose(load_block_index_range i mem Hrange Hops heap_size heap_valid).
      unfold WASM_BLOCK_BYTE_SIZE in *.
      lia.
    - destruct(read_heap1 i mem Hrange Hops Hheap_rel) as [bs [Hr Hd]].
      rewrite Hr.
      apply (f_equal (fun t => Memdata.encode_int 8 t)) in Hd.
      rewrite encode_decode in Hd.
      rewrite Hd; auto.
      apply(OpLoadHelper.read_bytes_length _ _ _ _ Hr).
    - rewrite stored_value_decomposition; auto.
      replace(etable_values load_value_in_heap1 i) with (loaded_value i).
      2: {
        unfold loaded_value.
        rewrite no_cross_block_no_heap2; auto.
        lia.
      }
      rewrite loaded_value_decomposition; auto.
      rewrite unchanged_value_is_tail_and_lead; auto.
      rewrite(Z.mul_comm 8 _).
      rewrite <- lookup_pow_modulus_value; auto.
      pose(lookup_pow_modulus_value i Hrange Hops).
      repeat rewrite Z_mod_plus by lia; auto.
    - rewrite stored_value_decomposition; auto.
      replace(etable_values load_value_in_heap1 i) with (loaded_value i).
      2: {
        unfold loaded_value.
        rewrite no_cross_block_no_heap2; auto.
        lia.
      }
      rewrite loaded_value_decomposition; auto.
      rewrite unchanged_value_is_tail_and_lead; auto.
      pose(len_value i Hrange Hops).
      repeat rewrite Z.shiftr_div_pow2 by lia.
      rewrite(Z.mul_comm 8 _).
      rewrite Z.mul_add_distr_r.
      rewrite Z.pow_add_r by lia.
      rewrite <- lookup_pow_modulus_value; auto.
      rewrite <- len_modulus_and_len; auto.
      rewrite(Z.add_comm _ (etable_values load_picked_u64_cell i * etable_values lookup_pow_modulus i)).
      rewrite(Z.add_comm _ (etable_values store_value_wrapped i * etable_values lookup_pow_modulus i)).
      repeat rewrite Z.add_assoc.
      rewrite <- Z.mul_assoc.
      pose(lookup_pow_modulus_value i Hrange Hops).
      pose(len_modulus_range i Hrange Hops).
      repeat rewrite Z.div_add; try lia.
      repeat rewrite Z.div_small.
      lia.
      - apply two_le_mul.
        apply store_value_wrapped_range; auto.
        apply load_tailing_range; auto.
      - apply two_le_mul.
        apply load_size; auto.
        apply load_tailing_range; auto.
    destruct H as [mem' [Hw1 Hheap_rel1]].
    exists mem'.
    replace(etable_values load_block_inner_pos i + etable_values len i -
      etable_values load_block_inner_pos i) with (etable_values len i) in Hw1 by lia.
    replace(Memdata.encode_int (Z.to_nat (etable_values len i))
      (Z.shiftr (stored_value i) (8 * etable_values load_block_inner_pos i))) with
      (Memdata.encode_int (Z.to_nat (etable_values len i))
      (etable_values store_value_u64_cell i)) in Hw1.
    2: {
      rewrite stored_value_decomposition; auto.
      rewrite unchanged_value_is_tail_and_lead; auto.
      rewrite(Z.mul_comm 8 _).
      rewrite Z.shiftr_div_pow2 by lia.
      rewrite <- lookup_pow_modulus_value; auto.
      pose(lookup_pow_modulus_value i Hrange Hops).
      rewrite Z.div_add by lia.
      rewrite Z.mul_comm.
      rewrite Z.mul_assoc.
      rewrite Z.div_add by lia.
      rewrite Z.div_small by apply (load_tailing_range i Hrange Hops).
      rewrite Z.add_0_l.
      assert(etable_values store_value_u64_cell i mod two_p (Z.of_nat (Z.to_nat (etable_values len i)) * 8) =
        (etable_values len_modulus i * etable_values load_leading i + 
        etable_values store_value_wrapped i) mod two_p (Z.of_nat (Z.to_nat (etable_values len i)) * 8)).
      - pose(len_value i Hrange Hops).
        rewrite Z2Nat.id by lia.
        rewrite two_p_equiv.
        rewrite <- len_modulus_and_len; auto. 
        rewrite <- store_value_wrapped_value; auto.
        rewrite Z.add_comm, Z.mul_comm.
        pose(len_modulus_range i Hrange Hops).
        rewrite Z.mod_add by lia.
        rewrite Z.mod_small by apply (store_value_wrapped_range i Hrange Hops); auto.
      repeat rewrite <- Memdata.decode_encode_int in H.
      apply (f_equal (fun t => Memdata.encode_int (Z.to_nat (etable_values len i)) t)) in H.
      repeat rewrite encode_decode in H by apply Memdata.encode_int_length.
      auto.
    }
    split; auto.
    split; try lia.
    intros.
    replace(etable_values store_value_in_heap1 i) with (stored_value i); auto.
    unfold stored_value.
    rewrite no_cross_block_no_store_heap2; auto; lia. 
  - assert(exists mem',
    write_bytes mem (8 * Z.to_N (etable_values load_block_index i) + Z.to_N (etable_values load_block_inner_pos i))
      (Memdata.encode_int (8 - Z.to_nat (etable_values load_block_inner_pos i))
      (Z.shiftr (etable_values store_value_in_heap1 i) 
      (8 * etable_values load_block_inner_pos i))) = Some mem' /\ 
    heap_rel (set (heap_map (etable_values eid_cell i)) 
      (etable_values load_block_index i) (etable_values store_value_in_heap1 i)) 
      (etable_values current_memory_page_size i)
      (etable_values maximal_memory_pages_cell i) mem').
    apply heap_rel_write_same_lower_bits with (z := etable_values load_value_in_heap1 i); auto; try lia.
    - apply load_value_in_heap1_range; auto.
    - apply store_value_in_heap1_range; auto.
    - destruct Hheap_rel.
      pose(load_block_index_range i mem Hrange Hops heap_size heap_valid).
      unfold WASM_BLOCK_BYTE_SIZE in *.
      lia.
    - destruct(read_heap1 i mem Hrange Hops Hheap_rel) as [bs [Hr Hd]].
      rewrite Hr.
      apply (f_equal (fun t => Memdata.encode_int 8 t)) in Hd.
      rewrite encode_decode in Hd.
      rewrite Hd; auto.
      apply(OpLoadHelper.read_bytes_length _ _ _ _ Hr).
    - replace (etable_values load_value_in_heap1 i) with (loaded_value i mod 2^64).
      replace (etable_values store_value_in_heap1 i) with (stored_value i mod 2^64).
      assert((2 ^ (8 * etable_values load_block_inner_pos i) | 2^64)).
      - replace 64 with (8 * etable_values load_block_inner_pos i + (64 - 8 * etable_values load_block_inner_pos i)) by lia.
        rewrite Z.pow_add_r by lia.
        apply Z.divide_factor_l.
      repeat rewrite <- Znumtheory.Zmod_div_mod; auto; try lia.
      rewrite loaded_value_decomposition; auto.
      rewrite stored_value_decomposition; auto.
      rewrite(Z.mul_comm 8 _).
      rewrite lookup_pow_modulus_value; auto.
      repeat rewrite Z.mod_add by lia; auto.
      unfold stored_value.
      rewrite Z.mod_add by lia.
      rewrite Z.mod_small by apply (store_value_in_heap1_range i Hrange Hops); auto.
      unfold loaded_value.
      rewrite Z.mod_add by lia.
      rewrite Z.mod_small by apply (load_value_in_heap1_range i Hrange Hops); auto.
    destruct H as [mem' [Hw1 Hheap_rel1]].  
    assert(exists mem'',
    write_bytes mem' (8 * Z.to_N (etable_values load_block_index i + 1))
      (Memdata.encode_int (Z.to_nat (etable_values load_block_inner_pos i + etable_values len i - 8))
      (etable_values store_value_in_heap2 i)) = Some mem'' /\ 
    heap_rel (set (set (heap_map (etable_values eid_cell i)) 
      (etable_values load_block_index i) (etable_values store_value_in_heap1 i))
      (etable_values load_block_index i + 1)
      (etable_values store_value_in_heap2 i))
      (etable_values current_memory_page_size i)
      (etable_values maximal_memory_pages_cell i) mem'').
    apply heap_rel_write_same_upper_bits with (z:= etable_values load_value_in_heap2 i); auto; try lia.
    - pose(cross_block_inner_pos_plus_len_range i Hrange Hops H1).
      lia.
    - apply load_value_in_heap2_range; auto.
    - apply store_value_in_heap2_range; auto.
    - destruct Hheap_rel1.
      pose(load_block_index_range i mem' Hrange Hops heap_size heap_valid).
      unfold WASM_BLOCK_BYTE_SIZE in *.
      lia.
    - destruct Hheap_rel1.
      specialize(heap_rel_lookup (Z.to_N (etable_values load_block_index i + 1)) 
        (etable_values load_value_in_heap2 i)).
      pose(Hl := load_block_index_range i mem' Hrange Hops heap_size heap_valid).
      unfold WASM_BLOCK_BYTE_SIZE in *.
      rewrite H1 in Hl.
      rewrite Z.mul_comm in Hl.
      rewrite Z.mul_1_l in Hl.
      replace (8 * etable_values load_block_index i + 8 + 8) with
        (8 * (etable_values load_block_index i + 1) + 8) in Hl by lia.
      rewrite Z2N.inj_le in Hl; try lia.
      rewrite N2Z.id in Hl.
      rewrite Z2N.inj_add in Hl; try lia.
      rewrite Z2N.inj_mul in Hl; try lia.
      change (Z.to_N 8) with 8%N in Hl.
      apply heap_rel_lookup in Hl.
      destruct Hl as [bs [Hread Hdecode]].
      rewrite Hread, <- Hdecode.
      rewrite encode_decode; auto.
      apply(OpLoadHelper.read_bytes_length _ _ _ _ Hread).
      rewrite gso by lia.
      rewrite Z2N.id by lia.
      pose(read_heap2 i mem Hrange Hops Hheap_rel H1).
      eapply mtable_read with (is_i32 := 0).
      pose(Hread := alloc_memory_table_lookup_read_cell_with_value_correct
        _ _ _ _ _ _ heap_read2 i Hrange).
      simpl in Hread.
      apply Hread; auto; try lia.
      apply (eid_common i).
      pose(load_block_index_common i).
      assert(0 <= etable_values load_block_index i + 1 < 2 * common + 10). lia.
      simpl in H.
      lia.
    - replace (etable_values load_value_in_heap2 i) with (Z.shiftr (loaded_value i) 64).
      replace (etable_values store_value_in_heap2 i) with (Z.shiftr (stored_value i) 64).
      pose(cross_block_inner_pos_plus_len_range i Hrange Hops H1).
      repeat rewrite Z.shiftr_shiftr by lia.
      replace (64 + 8 * (etable_values load_block_inner_pos i + etable_values len i - 8)) with
        (etable_values load_block_inner_pos i * 8 + etable_values len i * 8) by lia.
      repeat rewrite Z.shiftr_div_pow2 by lia.
      rewrite loaded_value_decomposition; auto.
      rewrite stored_value_decomposition; auto.
      rewrite unchanged_value_is_tail_and_lead; auto.
      rewrite Z.pow_add_r by lia.
      rewrite <- lookup_pow_modulus_value; auto.
      rewrite <- len_modulus_and_len; auto.
      rewrite(Z.add_comm (etable_values load_tailing i) _).
      rewrite <- Z.mul_assoc.
      repeat rewrite <- Z.add_assoc.
      pose(lookup_pow_modulus_value i Hrange Hops).
      pose(len_modulus_range i Hrange Hops).
      repeat rewrite Z.div_add_l by lia.
      repeat rewrite Z.div_small; auto.
      pose(two_le_mul _ _ _ _
        (store_value_wrapped_range i Hrange Hops)
        (load_tailing_range i Hrange Hops)); lia.
      pose(two_le_mul _ _ _ _
        (load_size i Hrange Hops)
        (load_tailing_range i Hrange Hops)); lia.
      unfold stored_value.
      rewrite Z.shiftr_div_pow2 by lia.
      rewrite Z.div_add by lia.
      rewrite Z.div_small by apply (store_value_in_heap1_range i Hrange Hops); lia.
      unfold loaded_value.
      rewrite Z.shiftr_div_pow2 by lia.
      rewrite Z.div_add by lia.
      rewrite Z.div_small by apply (load_value_in_heap1_range i Hrange Hops); lia.
    destruct H as [mem'' [Hw2 Hheaprel2]].
    exists mem''.
    split.
    - replace(Memdata.encode_int (Z.to_nat (etable_values len i)) (etable_values store_value_u64_cell i)) with
        (Memdata.encode_int (8 - Z.to_nat (etable_values load_block_inner_pos i) 
        + Z.to_nat (etable_values load_block_inner_pos i + etable_values len i - 8)) 
        (etable_values store_value_in_heap2 i * 2^(Z.of_nat (8 - Z.to_nat (etable_values load_block_inner_pos i)) * 8) 
        + (Z.shiftr (etable_values store_value_in_heap1 i) (8 * etable_values load_block_inner_pos i) 
        mod 2^(Z.of_nat (8 - Z.to_nat (etable_values load_block_inner_pos i)) * 8)))).
      apply write_bytes_combine with (mem':= mem'); auto.
      - rewrite Nat2Z.inj_sub by lia.
        rewrite Z2Nat.id by lia.
        change (Z.of_nat 8) with 8.
        rewrite Z.mul_sub_distr_l.
        apply CommonData.shiftr_range; try lia.
        apply store_value_in_heap1_range; auto.
      - rewrite Nnat.Nat2N.inj_add.
        rewrite Nnat.Nat2N.inj_sub.
        repeat rewrite Z_nat_N.
        change (N.of_nat 8) with (Z.to_N 8).
        rewrite <- Z2N.inj_sub by lia.
        pose(cross_block_inner_pos_plus_len_range i Hrange Hops H1).
        rewrite <- Z2N.inj_add by lia.
        replace(8 - etable_values load_block_inner_pos i +
          (etable_values load_block_inner_pos i + etable_values len i - 8)) with
          (etable_values len i) by lia.
        destruct Hheap_rel.
        pose(load_block_index_range i mem Hrange Hops heap_size heap_valid).
        unfold WASM_BLOCK_BYTE_SIZE in *.
        lia.
      - rewrite Nnat.Nat2N.inj_sub.
        rewrite Z_nat_N.
        change (N.of_nat 8) with (Z.to_N 8).
        rewrite <- Z2N.inj_sub by lia.
        rewrite <- (Z2N.inj_mul 8 _) by lia.
        repeat rewrite <- Z2N.inj_add by lia.
        replace (8 * etable_values load_block_index i + etable_values load_block_inner_pos i +
          (8 - etable_values load_block_inner_pos i)) with (8 * (etable_values load_block_index i + 1)) by lia.
        rewrite Z2N.inj_mul by lia.
        change (Z.to_N 8) with 8%N; auto.
      - rewrite <- (Z2Nat.inj_sub 8 _) by lia.
        pose(cross_block_inner_pos_plus_len_range i Hrange Hops H1).
        rewrite <- Z2Nat.inj_add by lia.
        replace (8 - etable_values load_block_inner_pos i +
        (etable_values load_block_inner_pos i + etable_values len i - 8)) with
        (etable_values len i) by lia.
        apply encode_eq.
        repeat rewrite Z2Nat.id by lia.
        rewrite two_p_equiv.
        rewrite <- len_modulus_and_len; auto.
        rewrite <- store_value_wrapped_value; auto.
        rewrite(Z.mod_small _ (2^((8 - etable_values load_block_inner_pos i) * 8))).
        replace((8 - etable_values load_block_inner_pos i) * 8) with 
          (64 - 8 * etable_values load_block_inner_pos i) by lia.
        rewrite Z.pow_sub_r by lia.
        rewrite <- Znumtheory.Zdivide_Zdiv_eq_2; try lia.
        rewrite <- Z.shiftr_div_pow2 by lia.
        rewrite shiftr_distr; try lia.
        replace (etable_values store_value_in_heap2 i * 2 ^ 64 +
        etable_values store_value_in_heap1 i) with (stored_value i).
        rewrite store_value_wrapped_from_stored_value; auto.
        rewrite Z.mul_comm; auto.
        unfold stored_value; lia.
        rewrite Z.land_comm.
        rewrite <- Z.shiftl_mul_pow2 by lia.
        apply land_0 with (n:= 64%nat); [lia|].
        - apply store_value_in_heap1_range; auto.
        replace 64 with (64 - 8 * etable_values load_block_inner_pos i + 
            8 * etable_values load_block_inner_pos i) by lia.
        rewrite Z.pow_add_r by lia.
        apply Z.divide_factor_r.
        rewrite Z.shiftr_div_pow2 by lia.
        replace ((8 - etable_values load_block_inner_pos i) * 8) with
          (64 - 8 * etable_values load_block_inner_pos i) by lia.
        destruct(store_value_in_heap1_range i Hrange Hops).
        split.
        - apply Z_div_nonneg_nonneg; lia.
        - replace 64 with (64 - 8 * etable_values load_block_inner_pos i + 
            8 * etable_values load_block_inner_pos i) in H0 by lia.
          rewrite Z.pow_add_r in H0 by lia.
          apply Z.div_lt_upper_bound; auto; lia.
    split; auto; lia.
Qed.

Lemma store_base_range : forall i,
  0 <= i ->
  etable_values (ops_cell Store) i = 1 ->
  0 <= etable_values store_base i < 2^32.
Proof.
  intros i Hrange Hops.
  eapply read_with_value_range with 
    (is_i32 := fun get => 1)
    (sp := fun get => get sp_cell + 2)
    (enable := fun get => get (ops_cell Store))
    (loctyp := MTableModel.LocationType_Stack); auto.
  - pose(sp_common i); lia.
  - apply stack_read_pos.
Qed.

Lemma bytes_takefill_same_length : forall b n l,
  length l = n ->
  bytes_takefill b n l = l.
Proof.
  induction n.
  - intros l Hlen.
    destruct l.
    - simpl; auto.
    - simpl in Hlen.
      discriminate.
  - intros l Hlen.
    destruct l.
    - simpl in Hlen; discriminate.
    - simpl.
      rewrite (IHn l); auto.
Qed.

Lemma store_mops : forall i,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    etable_values (ops_cell Store) i = 1 ->
    mops_at_correct i ->
    (etable_values is_cross_block i = 0 ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 1) /\
    (etable_values is_cross_block i = 1 ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 2).
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with Store in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i Store Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  
  split.
  - intros Hcb.
    rewrite Hcb in *.
    assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap >= 1).
    {
      apply (write_cell_with_value_mops _ _ _ _ _ _ heap_write1 i Hrange); auto.
      - apply (eid_common i).
      - pose (load_block_index_common i); lia.
    }
    lia.
  - intros Hcb.
    rewrite Hcb in *.
    assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap >= 2).
    {
      apply (write_cell_with_value_mops2 _ _ _ _ _ _ _ _ _ _ heap_write1 heap_write2 i Hrange); auto; try lia.
      - apply (eid_common i).
      - pose (load_block_index_common i); lia.
      - pose (load_block_index_common i); lia.
    }
    lia.
Qed.

Lemma store_stored_value : forall i mem,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Store) i = 1 ->
  heap_rel (heap_map (etable_values eid_cell i)) (etable_values mpages_cell i) (etable_values maximal_memory_pages_cell i) mem ->
  exists new_mem,
    store mem (Z.to_N (etable_values store_base i))
    (Z.to_N (etable_values opcode_store_offset i))
    (Memdata.encode_int (Z.to_nat (etable_values len i)) (etable_values store_value_u64_cell i))
    (Z.to_nat (etable_values len i)) = Some (new_mem) /\
  heap_rel (heap_map (etable_values eid_cell (i + 1))) (etable_values mpages_cell i) (etable_values maximal_memory_pages_cell i) new_mem.
Proof.
  intros i mem Hrange Heid Henabled Hmops Hops Hheap_rel.
  destruct(write_store_value i mem Hrange Hops Hheap_rel) as [new_mem [Hw [Hcb0 Hcb1]]].
  exists new_mem.
  destruct Hheap_rel.
  split.
  - unfold store.
    pose(store_base_range i Hrange Hops).
    pose(opcode_store_offset_common i).
    pose(len_value i Hrange Hops).
    rewrite <- Z2N.inj_add by lia.
    rewrite Z_nat_N.
    rewrite <- Z2N.inj_add by lia.
    change(etable_values store_base i + etable_values opcode_store_offset i) with
      (effective_address i).
    assert(Hineq : effective_address i + etable_values len i <= Z.of_N (mem_length mem)).
    - pose(Hpages := memory_pages_not_exceeded i Hrange Hops).
      rewrite effective_address_value; auto.
      rewrite <- Z.add_assoc.
      replace (etable_values load_block_inner_pos i + etable_values len i) with
        (end_inner_byte i + 1).
      pose(load_block_index_range i mem Hrange Hops heap_size heap_valid).
      pose(end_inner_byte_range i Hrange Hops).
      unfold WASM_BLOCK_BYTE_SIZE in *.
      pose(is_cross_block_bit i).
      lia.
      unfold end_inner_byte; lia.  
    rewrite <- (Z2N.id (effective_address i + etable_values len i))in Hineq.
    2: unfold effective_address; lia.
    rewrite <- N2Z.inj_le in Hineq.
    rewrite <- N.leb_le in Hineq.
    rewrite Hineq.
    rewrite bytes_takefill_same_length; auto.
    apply Memdata.encode_int_length.
  - destruct(is_cross_block_bit i).
    - specialize(Hcb0 H).
      replace(heap_map (etable_values eid_cell (i+1))) with
        (set (heap_map (etable_values eid_cell i)) 
          (etable_values load_block_index i)
          (etable_values store_value_in_heap1 i)); auto.
      symmetry.
      unfold heap_map.
      rewrite eid_change; auto.
      apply mtable_write with (is_i32:= 0); auto.
      - pose(Hw1 := heap_write1).
        apply alloc_memory_table_lookup_write_cell_with_value_correct 
          with (i := i) in Hw1; auto; try lia.
        - apply eid_common.
        - pose(load_block_index_common i); lia.
      - pose(proj1 (store_mops i Hrange Heid Henabled Hops Hmops) H).
        lia.
    - specialize(Hcb1 H).
      replace(heap_map (etable_values eid_cell (i+1))) with
        (set (set (heap_map (etable_values eid_cell i)) 
          (etable_values load_block_index i)
          (etable_values store_value_in_heap1 i))
          (etable_values load_block_index i + 1)
          (etable_values store_value_in_heap2 i)); auto.
      symmetry.
      unfold heap_map.
      rewrite eid_change; auto.
      apply mtable_write_two with (is_i32_1:= 0) (is_i32_2:= 0); auto; try lia.
      - pose(Hw1 := heap_write1).
        apply alloc_memory_table_lookup_write_cell_with_value_correct
          with (i := i) in Hw1; auto; try lia.
        - apply eid_common.
        - pose(load_block_index_common i); lia.
      - pose(Hw2 := heap_write2).
        apply alloc_memory_table_lookup_write_cell_with_value_correct
          with (i := i) in Hw2; auto; try lia.
        - apply eid_common.
        - pose(load_block_index_common i); lia.
      - pose(proj2 (store_mops i Hrange Heid Henabled Hops Hmops) H).
        lia.
Qed.

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
Proof.
  intros i st mem v base xs Hrange Hrow_enabled Hmops Hop Hrel Hstk Hmem.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).

  replace v with (etable_values store_value_u64_cell i).
  2: {
    apply stack_rel_read_without_value with
      (i := i)
      (n := 0%nat)
      (col := memory_table_lookup_stack_read_val)
      (is_i32 := (fun get => get is_i32))
      (value := (fun get => get store_value_u64_cell))
      (enable := (fun get => get (ops_cell Store)))
      (st := st)
      (stk := v::base::xs); auto; try lia.
    - apply is_i32_bit.
    - replace  (fun get : etable_cols -> Z => get sp_cell + 1 + Z.of_nat 0)
         with  (fun get : etable_cols -> Z => get sp_cell + 1)
               by (extensionality get; lia).
      apply stack_read_val.
  }

  replace base with (etable_values store_base i).
  2: {
    apply stack_rel_read with
      (i := i)
      (n := 1%nat)
      (col := memory_table_lookup_stack_read_pos)
      (is_i32 := (fun get => 1))
      (enable := (fun get => get (ops_cell Store)))
      (st := st)
      (stk := v::base::xs); auto.
    - lia.
    - replace  (fun get : etable_cols -> Z => get sp_cell + 1 + Z.of_nat 1)
         with  (fun get : etable_cols -> Z => get sp_cell + 2)
               by (extensionality get; lia).
      apply stack_read_pos.
  }
  
  destruct (store_stored_value i (wasm_memory st)) as [new_mem [Hstore_new_mem Hstore_value]]; auto.
  { destruct Hrel.
    assumption. }
  exists new_mem.
  split; [auto|].

  apply (store_mops) in Hmops; auto. 
  destruct Hmops as [Hmops0 Hmops1].
  constructor.
  - rewrite fid_change with (idx := Store); auto.
    rewrite iid_change with (idx := Store); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st xs)).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_memory.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.
  - rewrite eid_change by auto.
    rewrite stack_update_memory.
    rewrite stack_update_stack_incr_iid.
    rewrite (sp_change i _ Hrange Hrow_enabled Hop).
    simpl.
    apply state_stack_rel in Hrel.
    rewrite Hstk in Hrel.
    simpl in Hrel.
    destruct Hrel as [_ [_ Hrel']].
    replace(etable_values sp_cell i + 2 + 1) with 
      (etable_values sp_cell i + 1 + 1 + 1) by lia.
    rewrite stack_no_write; auto.
    destruct st; simpl.
    assumption.
    pose(is_cross_block_bit i); lia.
  - rewrite eid_change by auto.
    rewrite globals_update_memory.
    rewrite globals_update_stack_incr_iid.
    rewrite globals_no_write; auto.
    destruct Hrel.
    destruct st; simpl.
    assumption.
    pose(is_cross_block_bit i); lia.
  - rewrite memory_update_memory.
    rewrite mpages_change with (idx:= Store); auto.
    simpl.
    rewrite Z.add_0_r; auto.
    rewrite maximal_memory_pages_change; auto.
  - rewrite callstack_update_memory, callstack_update_stack, callstack_incr_iid.
    rewrite (frame_id_change i Store); simpl; auto.
    rewrite (fid_change i Store); simpl; auto.
    destruct Hrel; assumption.
Qed.
