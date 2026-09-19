(* Copyright (C) CertiK 2024-2026 *)

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
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config BinShift i)) with 1.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  - apply MTable.mtable_write_mops with
      (offset := etable_values sp_cell i + 2)
      (is_i32 := etable_values is_i32 i)
      (value := etable_values res i); auto.
    apply (alloc_memory_table_lookup_write_cell_with_value_correct _ _ _ _ _ _ 
      stack_write i Hrange); auto.
    - apply eid_common.
    - apply is_i32_bit.
    - pose(sp_common i); lia.
  lia.
Qed.

Lemma only_one_right_op : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_r i = 1 <->
    (etable_values is_shr_u i = 1 /\ etable_values is_shr_s i = 0 /\ etable_values is_rotr i = 0) \/
    (etable_values is_shr_u i = 0 /\ etable_values is_shr_s i = 1 /\ etable_values is_rotr i = 0) \/
    (etable_values is_shr_u i = 0 /\ etable_values is_shr_s i = 0 /\ etable_values is_rotr i = 1).
Proof.
  intros i Hrange Hops.
  pose(H := bin_shift_op_select i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  pose(is_shr_s_bit i).
  pose(is_shr_u_bit i).
  pose(is_rotr_bit i).
  lia.
Qed.

Lemma only_one_left_op : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_l i = 1 <->
    (etable_values is_shl i = 1 /\ etable_values is_rotl i = 0) \/
    (etable_values is_shl i = 0 /\ etable_values is_rotl i = 1).
Proof.
  intros i Hrange Hops.
  pose(H := bin_shift_op_select i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  pose(is_shl_bit i).
  pose(is_rotl_bit i).
  lia.
Qed.

Lemma only_one_op : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    (etable_values is_r i = 1 /\ etable_values is_l i = 0) \/
    (etable_values is_r i = 0 /\ etable_values is_l i = 1).
Proof.
  intros i Hrange Hops.
  pose(H := bin_shift_op_select i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  pose(is_r_bit i).
  pose(is_l_bit i).
  lia.
Qed.

Lemma right_op_enabled : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_shr_u i = 1 \/ etable_values is_shr_s i = 1 \/ etable_values is_rotr i = 1 ->
    etable_values is_r i = 1.
Proof.
  intros i Hrange Hops.
  pose(H := bin_shift_op_select i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  pose(is_r_bit i).
  pose(is_shr_u_bit i).
  pose(is_shr_s_bit i).
  pose(is_rotr_bit i).
  lia.
Qed.

Lemma left_op_enabled : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_shl i = 1 \/ etable_values is_rotl i = 1 ->
    etable_values is_l i = 1.
Proof.
  intros i Hrange Hops.
  pose(H := bin_shift_op_select i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  pose(is_l_bit i).
  pose(is_shl_bit i).
  pose(is_rotl_bit i).
  lia.
Qed.

Definition BinShift_op i :=
  if (Z.eq_dec (etable_values is_shl i) 1) then SHL
  else if (Z.eq_dec (etable_values is_shr_u i) 1) then SHR_u
  else if (Z.eq_dec (etable_values is_shr_s i) 1) then SHR_s
  else if (Z.eq_dec (etable_values is_rotl i) 1) then ROTL
  else if (Z.eq_dec (etable_values is_rotr i) 1) then ROTR
  else ROTR.

Require Import ImageTableModel.
Require Import InjectivityHelper.

Lemma BinShift_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values ETableModel.enabled_cell i = 1 ->    
  etable_values (ops_cell BinShift) i = 1 ->
  exists op,
    program (wasm_pc st) = IBinShift (bool_of_Z (etable_values is_i32 i)) op
    /\ match op with
       | SHL   => etable_values is_shl i = 1
       | SHR_u => etable_values is_shr_u i = 1
       | SHR_s => etable_values is_shr_s i = 1
       | ROTL => etable_values is_rotl i = 1
       | ROTR => etable_values is_rotr i = 1
       end
    /\ op = BinShift_op i.
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i BinShift Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  destruct (only_one_op i Hrange Hops) as [[Hright1 Hright2] | [Hleft1 Hleft2]].
  - assert (Hshl : etable_values is_shl i = 0).
    { destruct (is_shl_bit i); auto.
      pose (left_op_enabled i Hrange Hops (or_introl ltac:(eauto))).
      congruence. }
    assert (Hrotl : etable_values is_rotl i = 0).
    { destruct (is_rotl_bit i); auto.
      pose (left_op_enabled i Hrange Hops (or_intror ltac:(eauto))).
      congruence. }
    rewrite (only_one_right_op i Hrange Hops) in Hright1.
    destruct Hright1 as [Hsel | [Hsel | Hsel]].
    +  exists SHR_u.       
       repeat split.
       2: { tauto. }
       {
       apply opcode_of_instruction_inj.
       rewrite <- Hopcode. clear Hopcode.
       unfold opcode_config, config_opcode, opcode_of_instruction.
       rewrite <- !Zplus_assoc.
       f_equal.
       destruct Hsel as [Hsel1 [Hsel2 Hsel3]].
       rewrite !Hshl, !Hrotl, !Hsel1, !Hsel2, !Hsel3.
       rewrite !Z.mul_0_l, !Z.add_0_l.
       rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
       f_equal.
       rewrite bool_of_Z_simpl.
       2: { apply OpBinShiftModel.is_i32_bit. }
       reflexivity. }
       { unfold BinShift_op.
         destruct Hsel as [Hsel1 [Hsel2 Hsel3]].
         rewrite !Hshl, !Hrotl, !Hsel1, !Hsel2, !Hsel3.       
         reflexivity. }
    +  exists SHR_s.    
       repeat split.
       { apply opcode_of_instruction_inj.
       rewrite <- Hopcode. clear Hopcode.
       unfold opcode_config, config_opcode, opcode_of_instruction.
       rewrite <- !Zplus_assoc.
       f_equal.
       destruct Hsel as [Hsel1 [Hsel2 Hsel3]].
       rewrite !Hshl, !Hrotl, !Hsel1, !Hsel2, !Hsel3.
       rewrite !Z.mul_0_l, !Z.add_0_l.
       rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
       f_equal.
       rewrite bool_of_Z_simpl.
       2: { apply OpBinShiftModel.is_i32_bit. }
       reflexivity. }
       { tauto. }
       { unfold BinShift_op.
         destruct Hsel as [Hsel1 [Hsel2 Hsel3]].
         rewrite !Hshl, !Hrotl, !Hsel1, !Hsel2, !Hsel3.
         reflexivity. }
    +  exists ROTR.
       repeat split.
       {apply opcode_of_instruction_inj.
       rewrite <- Hopcode. clear Hopcode.
       unfold opcode_config, config_opcode, opcode_of_instruction.
       rewrite <- !Zplus_assoc.
       f_equal.
       destruct Hsel as [Hsel1 [Hsel2 Hsel3]].
       rewrite !Hshl, !Hrotl, !Hsel1, !Hsel2, !Hsel3.
       rewrite !Z.mul_0_l, !Z.add_0_l.
       rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
       f_equal.
       rewrite bool_of_Z_simpl.
       2: { apply OpBinShiftModel.is_i32_bit. }
       reflexivity. }
       { tauto. }
       { unfold BinShift_op.
         destruct Hsel as [Hsel1 [Hsel2 Hsel3]].
         rewrite !Hshl, !Hrotl, !Hsel1, !Hsel2, !Hsel3.
         reflexivity. }
  - assert (Hshr_u : etable_values is_shr_u i = 0).
    { destruct (is_shr_u_bit i); auto.
      pose (right_op_enabled i Hrange Hops (or_introl ltac:(eauto))).
      congruence. }
    assert (Hshr_s : etable_values is_shr_s i = 0).
    { destruct (is_shr_s_bit i); auto.
      pose (right_op_enabled i Hrange Hops (or_intror (or_introl ltac:(eauto)))).
      congruence. }
    assert (Hrotr : etable_values is_rotr i = 0).
    { destruct (is_rotr_bit i); auto.
      pose (right_op_enabled i Hrange Hops (or_intror (or_intror ltac:(eauto)))).
      congruence. } 
    rewrite (only_one_left_op i Hrange Hops) in Hleft2.
    destruct Hleft2 as [Hsel |Hsel ].
    +  exists SHL.
       repeat split.
       { apply opcode_of_instruction_inj.
       rewrite <- Hopcode. clear Hopcode.
       unfold opcode_config, config_opcode, opcode_of_instruction.
       rewrite <- !Zplus_assoc.
       f_equal.
       destruct Hsel as [Hsel1 Hsel2].
       rewrite !Hshr_u, !Hshr_s, !Hrotr, !Hsel1, !Hsel2.
       rewrite !Z.mul_0_l, !Z.add_0_l.
       rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
       f_equal.
       rewrite bool_of_Z_simpl.
       2: { apply OpBinShiftModel.is_i32_bit. }
       reflexivity. }
       { tauto. }
       { unfold BinShift_op.
         destruct Hsel as [Hsel1 Hsel2].
         rewrite !Hshr_u, !Hshr_s, !Hrotr, !Hsel1, !Hsel2.
         reflexivity. }
    +  exists ROTL.
       repeat split.
       { apply opcode_of_instruction_inj.
       rewrite <- Hopcode. clear Hopcode.
       unfold opcode_config, config_opcode, opcode_of_instruction.
       rewrite <- !Zplus_assoc.
       f_equal.
       destruct Hsel as [Hsel1 Hsel2].
       rewrite !Hshr_u, !Hshr_s, !Hrotr, !Hsel1, !Hsel2.
       rewrite !Z.mul_0_l, !Z.add_0_l.
       rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
       f_equal.
       rewrite bool_of_Z_simpl.
       2: { apply OpBinShiftModel.is_i32_bit. }
       reflexivity. }
       { tauto. }
       { unfold BinShift_op.
         destruct Hsel as [Hsel1 Hsel2].
         rewrite !Hshr_u, !Hshr_s, !Hrotr, !Hsel1, !Hsel2.
         reflexivity. }
Qed.

Lemma rhs_modulus_value : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    (etable_values is_i32 i = 0 -> etable_values rhs_modulus i = 64) /\
    (etable_values is_i32 i = 1 -> etable_values rhs_modulus i = 32).
Proof.
  intros i Hrange Hops.
  pose(H := bin_shift_modulus i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Lemma size_modulus_value : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values size_modulus i = 2^(etable_values rhs_modulus i).
Proof.
  intros i Hrange Hops.
  pose(H := bin_shift_modulus i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  pose(Hbit := is_i32_bit i).
  pose(Hrhs := rhs_modulus_value i Hrange Hops).
  destruct Hrhs.
  destruct Hbit as [Hbit0 | Hbit1].
  - apply H0 in Hbit0.
    rewrite Hbit0.
    lia.
  - apply H1 in Hbit1.
    rewrite Hbit1.
    lia.
Qed.

Lemma rhs_rem_range : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    0 <= etable_values rhs_rem i < etable_values rhs_modulus i.
Proof.
  intros i Hrange Hops.
  pose(H := bin_shift_rhs_rem i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  pose(rhs_rem_common i).
  pose(rhs_rem_diff_common i).
  lia.
Qed.

Lemma rhs_division : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    Z.div_eucl (etable_values rhs_u16_cells_le_0 i) (etable_values rhs_modulus i)
    = (etable_values rhs_round i, etable_values rhs_rem i).
Proof.
  intros i Hrange Hops.
  rewrite(Zaux.Zdiv_eucl_unique _ _).
  pose(H := bin_shift_rhs_rem i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [H _].
  replace(etable_values rhs_u16_cells_le_0 i) with
    (etable_values rhs_round i * etable_values rhs_modulus i
    + etable_values rhs_rem i) by lia.
  pose(Hrem := rhs_rem_range i Hrange Hops).
  assert(Hmod : etable_values rhs_modulus i > 0).
  - pose(rhs_modulus_value i Hrange Hops).
    pose(Hbit := is_i32_bit i).
    lia.
  rewrite(Z.div_add_l _ _ _) by lia.
  rewrite(Z.div_small _ _) by apply Hrem.
  rewrite(Z.add_0_r _).
  rewrite(Z.add_comm _ _).
  rewrite(Z_mod_plus _ _ _) by apply Hmod.
  rewrite(Z.mod_small _ _) by apply Hrem.
  reflexivity.
Qed.

Lemma rhs_mod_rhs_modulus : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values rhs_u64_cell i mod etable_values rhs_modulus i =
    etable_values rhs_rem i.
Proof.
  intros i Hrange Hops.
  assert(etable_values rhs_u64_cell i mod etable_values rhs_modulus i
    = etable_values rhs_u16_cells_le_0 i mod etable_values rhs_modulus i).
  - pose(Hrmod := rhs_modulus_value i Hrange Hops).
    pose(Hbit := is_i32_bit i).
    pose(H64 := rhs_U64 i).
    destruct Hbit as [H0 | H1].
    - replace(etable_values rhs_u64_cell i) with
      (etable_values rhs_u16_cells_le_0 i +
      (etable_values rhs_u16_cells_le_1 i * 2^10
      +etable_values rhs_u16_cells_le_2 i * 2^26
      +etable_values rhs_u16_cells_le_3 i * 2^42)
      *etable_values rhs_modulus i) by lia.
      apply(Z_mod_plus_full _ _ _).
    - replace(etable_values rhs_u64_cell i) with
      (etable_values rhs_u16_cells_le_0 i +
      (etable_values rhs_u16_cells_le_1 i * 2^11
      +etable_values rhs_u16_cells_le_2 i * 2^27
      +etable_values rhs_u16_cells_le_3 i * 2^43)
      *etable_values rhs_modulus i) by lia.
      apply(Z_mod_plus_full _ _ _).
  rewrite H.
  replace(etable_values rhs_u16_cells_le_0 i mod etable_values rhs_modulus i)
  with (etable_values rhs_rem i); auto.
  assert(etable_values rhs_modulus i <> 0).
  pose(Hrmod := rhs_modulus_value i Hrange Hops).
  pose(Hbit := is_i32_bit i).
  lia.
  pose(Hrdiv := rhs_division i Hrange Hops).
  pose(H1 := Z.div_eucl_eq 
    (etable_values rhs_u16_cells_le_0 i) 
    (etable_values rhs_modulus i) H0).
  rewrite Hrdiv in H1.
  rewrite H1.
  rewrite(Z.mul_comm _ _).
  rewrite(Z.add_comm _ _).
  rewrite(Z.mod_add _ _ _) by apply H0.
  pose(Hrem := rhs_rem_range i Hrange Hops).
  rewrite(Z.mod_small _ _) by apply Hrem.
  reflexivity.
Qed.

Lemma lookup_pow_power_value : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 -> 
    etable_values lookup_pow_modulus i = 2^(etable_values rhs_rem i).
Proof.
  intros i Hrange Hops.
  pose(H := bin_shift_modulus_pow_lookup i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  assert(H1: etable_values lookup_pow_power i - 128 = etable_values rhs_rem i) by lia.
  clear H.
  assert (Hpower_nonzero: etable_values lookup_pow_power i <> 0).
  {
    pose (rhs_rem_range i Hrange Hops).
    lia.
  }
  assert (Hin:=ETableModel.c8d i Hrange).
  apply RTable.in_op_table_power in Hin; auto.
  rewrite <- H1.
  lia.
Qed.

Lemma is_r_rem_range : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_r i = 1 ->
    0 <= etable_values rem i < etable_values lookup_pow_modulus i.
Proof.
  intros i Hrange Hops Hr.
  pose(H := bin_shift_is_r i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  pose(diff_U64 i).
  pose(rem_U64 i).
  unfold Wasm_int.Int64.modulus in *.
  rewrite(two_power_nat_equiv _) in *.
  simpl in *.
  lia.
Qed.

Lemma is_r_lhs_div : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_r i = 1 ->
    Z.div_eucl (etable_values lhs_u64_cell i) (etable_values lookup_pow_modulus i)
    = (etable_values round i, etable_values rem i).
Proof.
  intros i Hrange Hops Hr.
  pose(H := bin_shift_is_r i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [H _].
  replace(etable_values lhs_u64_cell i) with
    (etable_values round i * etable_values lookup_pow_modulus i
    + etable_values rem i) by lia.
  pose(Hrem := is_r_rem_range i Hrange Hops Hr).
  assert(Hmod : etable_values lookup_pow_modulus i > 0).
  - lia.
  rewrite(Zaux.Zdiv_eucl_unique _ _).
  rewrite(Z.div_add_l _ _ _) by lia.
  rewrite(Z.div_small _ _) by apply Hrem.
  rewrite(Z.add_0_r _).
  rewrite(Z.add_comm _ _).
  rewrite(Z_mod_plus _ _ _) by apply Hmod.
  rewrite(Z.mod_small _ _) by apply Hrem.
  reflexivity.
Qed.

Lemma is_r_lhs_shifted_by_rhs_rem : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_r i = 1 ->
    Z.shiftr (etable_values lhs_u64_cell i) (etable_values rhs_rem i)
    = etable_values round i.
Proof.
  intros i Hrange Hops Hr.
  pose(Hlhsdiv := is_r_lhs_div i Hrange Hops Hr).
  assert(etable_values lookup_pow_modulus i <> 0).
  - pose(is_r_rem_range i Hrange Hops Hr). lia.
  pose(H1 := Z.div_eucl_eq 
  (etable_values lhs_u64_cell i) 
  (etable_values lookup_pow_modulus i) H).
  rewrite Hlhsdiv in H1.
  rewrite H1.
  rewrite(Z.shiftr_div_pow2 _ _) by apply (rhs_rem_common i).
  rewrite(lookup_pow_power_value i Hrange Hops).
  rewrite(Z.add_comm _ _).
  rewrite(Z.mul_comm _ _).
  rewrite(Z_div_plus _ _ _).
  2 : {
    pose(rhs_rem_common i). lia.
  }
  rewrite(Z.div_small _ _).
  2 : {
    pose(is_r_rem_range i Hrange Hops Hr).
    rewrite <- (lookup_pow_power_value i Hrange Hops).
    assumption.
  }
  reflexivity.
Qed.

Lemma shr_u_correct : forall i l r m,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_shr_u i = 1 ->
    etable_values lhs_u64_cell i = l ->
    etable_values rhs_u64_cell i = r ->
    etable_values rhs_modulus i = m ->
    etable_values res i = shr_u l r m.
Proof.
  intros i l r m Hrange Hops Hshru Hlhs Hrhs Hmod.
  unfold shr_u.
  rewrite <- Hlhs, <- Hrhs, <- Hmod.
  rewrite(rhs_mod_rhs_modulus i Hrange Hops).
  assert(Hr : etable_values is_r i = 1).
  - pose(right_op_enabled i Hrange Hops); lia.
  rewrite(is_r_lhs_shifted_by_rhs_rem i Hrange Hops Hr).
  pose(Hgate := bin_shift_shr_u i Hrange).
  simpl in Hgate.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Lemma degree_helper_value : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values degree_helper i =
    (etable_values lookup_pow_modulus i - 1) *
    etable_values size_modulus i.
Proof.
  intros i Hrange Hops.
  pose(H := bin_shift_shr_s i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Lemma is_shr_s_pad_value : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_shr_s i = 1 ->
    etable_values pad i * etable_values lookup_pow_modulus i =
    etable_values lhs_flag_bit_cell i * etable_values degree_helper i.
Proof.
  intros i Hrange Hops Hshrs.
  pose(H := bin_shift_shr_s i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Lemma lhs_bit_32 : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_i32 i = 1 ->
    0 <= etable_values lhs_u64_cell i < 2^32.
Proof.
  intros i Hrange Hops Hi32.
  assert(0 <= etable_values lhs_u64_cell i < 2^(64 - (etable_values is_i32 i) * 32)).
  - eapply read_range with (is_i32 := fun get => get is_i32)
                           (sp := fun get => get sp_cell + 2)
                           (value := fun get => get lhs_u64_cell)
                           (enable := fun get => get (ops_cell BinShift))
                           (loctyp := MTableModel.LocationType_Stack); auto.
    pose (sp_common i); lia.
    apply stack_read_lhs.
  rewrite Hi32 in H.
  lia.
Qed.

Lemma sixteen_most_significant_bits_of_lhs : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values lhs_u16_cells_le_3 i + etable_values is_i32 i
    * (etable_values lhs_u16_cells_le_1 i - etable_values lhs_u16_cells_le_3 i)
    = Z.shiftr (etable_values lhs_u64_cell i) (48 - etable_values is_i32 i * 32).
Proof.
  intros i Hrange Hops.
  pose(Hlhs := lhs_U64 i).
  pose(Hu16 := lhs_u16_cells_U16).
  destruct Hu16 as [H0 [H1 [H2 H3]]].
  specialize(H0 i); specialize(H1 i); specialize(H2 i); specialize(H3 i).
  rewrite Hlhs.
  pose(H := is_i32_bit i).
  rewrite(Z.shiftr_div_pow2 _ _) by lia.
  destruct H as [Hbit0 | Hbit1].
  - rewrite Hbit0; simpl.
    rewrite(Z.div_add _ _ _) by lia.
    rewrite(Z.div_small _ _) by lia.
    lia.
  - rewrite Hbit1.
    replace(etable_values lhs_u16_cells_le_3 i + 1 *
      (etable_values lhs_u16_cells_le_1 i - etable_values lhs_u16_cells_le_3 i)) with
      (etable_values lhs_u16_cells_le_1 i) by lia.
    simpl.
    replace(etable_values lhs_u16_cells_le_0 i +
      etable_values lhs_u16_cells_le_1 i * Z.pow_pos 2 16 +
      etable_values lhs_u16_cells_le_2 i * Z.pow_pos 2 32 +
      etable_values lhs_u16_cells_le_3 i * Z.pow_pos 2 48) with
      (etable_values lhs_u16_cells_le_0 i +
      (etable_values lhs_u16_cells_le_1 i +
      etable_values lhs_u16_cells_le_2 i * Z.pow_pos 2 16 +
      etable_values lhs_u16_cells_le_3 i * Z.pow_pos 2 32) * Z.pow_pos 2 16) by lia.
    rewrite(Z.div_add _ _ _) by lia.
    rewrite(Z.div_small _ _) by apply H0.
    pose(lhs_bit_32 i Hrange Hops Hbit1).
    assert(etable_values lhs_u16_cells_le_2 i = 0 /\ etable_values lhs_u16_cells_le_3 i = 0).
    - lia.
    lia.
Qed.

Lemma lhs_flag_bit_cell_is_most_significant_bit_of_lhs : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values lhs_flag_bit_cell i =
    Z.shiftr (etable_values lhs_u64_cell i) (63 - (etable_values is_i32 i) * 32).
Proof.
  intros i Hrange Hops.
  pose(H := lhs_flag_bit_dyn i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [Hdecomp [Hflag_range _]].
  replace(63 - etable_values is_i32 i * 32) with
    (48 - etable_values is_i32 i * 32 + 15) by lia.
  rewrite <- (Z.shiftr_shiftr _ _ _) by lia.
  rewrite <- (sixteen_most_significant_bits_of_lhs i Hrange Hops).
  replace(etable_values lhs_u16_cells_le_3 i + etable_values is_i32 i *
    (etable_values lhs_u16_cells_le_1 i - etable_values lhs_u16_cells_le_3 i)) with
    (etable_values lhs_flag_bit_cell i * 2^15 + etable_values lhs_flag_u16_rem_cell i) by lia.
  rewrite(Z.shiftr_div_pow2 _ _) by lia.
  rewrite(Z.div_add_l _ _ _) by lia.
  rewrite(Z.div_small _ _).
  lia.
  pose(lhs_flag_u16_rem_cell_common i).
  pose(lhs_flag_u16_rem_diff_cell_common i).
  lia.
Qed.

Lemma lookup_divides_size : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    (etable_values lookup_pow_modulus i | etable_values size_modulus i).
Proof.
  intros i Hrange Hops.
  pose(rhs_rem_range i Hrange Hops).
  rewrite(lookup_pow_power_value i Hrange Hops).
  rewrite(size_modulus_value i Hrange Hops).
  replace(2^(etable_values rhs_modulus i)) with 
    (2^(etable_values rhs_rem i) * 
    2^(etable_values rhs_modulus i - etable_values rhs_rem i)).
  apply(Z.divide_factor_l _ _).
  rewrite <- (Z.pow_add_r _ _ _); try lia.
  replace(etable_values rhs_rem i + (etable_values rhs_modulus i - etable_values rhs_rem i)) with
  (etable_values rhs_modulus i) by lia.
  reflexivity.
Qed.

Lemma shr_s_correct : forall i l r m,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_shr_s i = 1 ->
    etable_values lhs_u64_cell i = l ->
    etable_values rhs_u64_cell i = r ->
    etable_values rhs_modulus i = m ->
    etable_values res i = shr_s l r m.
Proof.
  intros i l r m Hrange Hops Hshr Hlhs Hrhs Hmod.
  pose(Hgate := bin_shift_shr_s i Hrange); simpl in *.
  replace(i+0) with i in * by lia.
  destruct Hgate as [_ [_ [Hgate _]]].
  assert(Hr : etable_values is_r i = 1).
  - pose(right_op_enabled i Hrange Hops); lia.
  replace(etable_values res i) with (etable_values round i + etable_values pad i) by lia.
  rewrite <- Hlhs, <- Hrhs, <- Hmod.
  pose(Hpad := is_shr_s_pad_value i Hrange Hops Hshr).
  unfold shr_s.
  replace(etable_values rhs_modulus i - 1) with
    (63 - etable_values is_i32 i * 32).
  2 : {
    pose(is_i32_bit i).
    pose(rhs_modulus_value i Hrange Hops).
    lia.
  }
  rewrite <- (lhs_flag_bit_cell_is_most_significant_bit_of_lhs i Hrange Hops). 
  pose(Hflag := lhs_flag_bit_cell_bit i).
  destruct Hflag as [Hflag0 | Hflag1].
  - rewrite Hflag0 in *; simpl.
    rewrite(Z.mul_0_l _) in Hpad.
    assert(etable_values pad i = 0).
    - eapply(Z.mul_eq_0_l _ (etable_values lookup_pow_modulus i)); auto.
      pose(is_r_rem_range i Hrange Hops Hr). lia.
    rewrite H.
    rewrite(rhs_mod_rhs_modulus i Hrange Hops).
    rewrite(is_r_lhs_shifted_by_rhs_rem i Hrange Hops Hr).
    lia.
  - rewrite Hflag1 in *; simpl.
    rewrite(rhs_mod_rhs_modulus i Hrange Hops).
    rewrite(is_r_lhs_shifted_by_rhs_rem i Hrange Hops Hr).
    rewrite(Z.shiftl_mul_pow2 _ _).
    2: {
      pose(rhs_rem_range i Hrange Hops).
      lia.
    }
    pose(rhs_rem_range i Hrange Hops).
    rewrite(Z.pow_sub_r _ _ _); try lia.
    rewrite <- (lookup_pow_power_value i Hrange Hops).
    rewrite <- (size_modulus_value i Hrange Hops).
    rewrite(Z.add_comm _ _).
    rewrite(Z.add_comm (etable_values round i) _).
    rewrite(Z.add_cancel_r _ _ _).
    rewrite(Z.mul_1_l _) in Hpad.
    rewrite(degree_helper_value i Hrange Hops) in Hpad.
    apply(f_equal (fun t => t / (etable_values lookup_pow_modulus i))) in Hpad.
    assert(Hlookup : etable_values lookup_pow_modulus i <> 0).
    - pose(is_r_rem_range i Hrange Hops Hr).
      lia.
    rewrite(Z.div_mul _ _ Hlookup) in Hpad.
    rewrite <- (Znumtheory.Zdivide_Zdiv_eq_2 _ _ _); auto.
    - pose(is_r_rem_range i Hrange Hops Hr).
      lia.
    - apply(lookup_divides_size i Hrange Hops).
Qed.

Lemma rotr_correct : forall i l r m,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_rotr i = 1 ->
    etable_values lhs_u64_cell i = l ->
    etable_values rhs_u64_cell i = r ->
    etable_values rhs_modulus i = m ->
    etable_values res i = rotr l r m.
Proof.
  intros i l r m Hrange Hops Hrotr Hlhs Hrhs Hmod.
  pose(Hgate := bin_shift_is_rotr i Hrange); simpl in *.
  replace(i+0) with i in * by lia.
  assert(Hr : etable_values is_r i = 1).
  - pose(right_op_enabled i Hrange Hops); lia.
  unfold rotr.
  rewrite <- Hlhs, <- Hrhs, <- Hmod.
  rewrite(rhs_mod_rhs_modulus i Hrange Hops).
  rewrite(is_r_lhs_shifted_by_rhs_rem i Hrange Hops Hr).
  rewrite <- (lookup_pow_power_value i Hrange Hops).
  replace(etable_values lhs_u64_cell i mod etable_values lookup_pow_modulus i)
    with (etable_values rem i).
  2 : {
    pose(Hdiv := is_r_lhs_div i Hrange Hops Hr).
    pose(Heucl := Zaux.Zdiv_eucl_unique (etable_values lhs_u64_cell i) (etable_values lookup_pow_modulus i)).
    rewrite Hdiv in Heucl.
    apply(pair_equal_spec _ _ _ _) in Heucl.
    lia.
  }
  pose(rhs_rem_range i Hrange Hops).
  rewrite(Z.shiftl_mul_pow2 _ _) by lia.
  rewrite(Z.pow_sub_r _ _ _) by lia.
  rewrite <- (lookup_pow_power_value i Hrange Hops).
  rewrite <- (size_modulus_value i Hrange Hops).
  assert(0 < etable_values lookup_pow_modulus i).
  - pose(is_r_rem_range i Hrange Hops Hr).
    lia.
  pose(lookup_divides_size i Hrange Hops).
  rewrite <- (Znumtheory.Zdivide_Zdiv_eq_2 _ _ _); auto.
  assert(Hres : etable_values res i * etable_values lookup_pow_modulus i =
    etable_values round i * etable_values lookup_pow_modulus i +
    etable_values rem i * etable_values size_modulus i) by lia.
  apply(f_equal (fun t => t / (etable_values lookup_pow_modulus i))) in Hres.
  rewrite(Z.div_add_l _ _ _) in Hres; try lia.
  rewrite(Z.div_mul _ _) in Hres; try lia.
Qed.

Lemma is_l_rem_range : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_l i = 1 ->
    0 <= etable_values rem i < etable_values size_modulus i.
Proof.
  intros i Hrange Hops Hl.
  pose(H := bin_shift_is_l i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  pose(rem_U64 i).
  pose(diff_U64 i).
  lia.
Qed.

Lemma is_l_lhs_decomp : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_l i = 1 ->
    etable_values lhs_u64_cell i * etable_values lookup_pow_modulus i =
    etable_values round i * etable_values size_modulus i + etable_values rem i.
Proof.
  intros i Hrange Hops Hl.
  pose(H := bin_shift_is_l i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Lemma is_l_lhs_div : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_l i = 1 ->
    Z.div_eucl (etable_values lhs_u64_cell i * etable_values lookup_pow_modulus i)
      (etable_values size_modulus i) =
    (etable_values round i, etable_values rem i).
Proof.
  intros i Hrange Hops Hl.
  pose(H := bin_shift_is_l i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [H _].
  rewrite(is_l_lhs_decomp i Hrange Hops Hl).
  pose(Hrem := is_l_rem_range i Hrange Hops Hl).
  assert(Hmod : etable_values size_modulus i > 0).
  - lia.
  rewrite(Zaux.Zdiv_eucl_unique _ _).
  rewrite(Z.div_add_l _ _ _) by lia.
  rewrite(Z.div_small _ _) by apply Hrem.
  rewrite(Z.add_0_r _).
  rewrite(Z.add_comm _ _).
  rewrite(Z_mod_plus _ _ _) by apply Hmod.
  rewrite(Z.mod_small _ _) by apply Hrem.
  reflexivity.
Qed.

Lemma is_l_lhs_shifted_by_rhs_rem : forall i,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_l i = 1 ->
    Z.shiftl (etable_values lhs_u64_cell i) (etable_values rhs_rem i)
    = etable_values lhs_u64_cell i * etable_values lookup_pow_modulus i.
Proof.
  intros i Hrange Hops Hl.
  pose(Hrem := rhs_rem_common i).
  rewrite(Z.shiftl_mul_pow2 _ _) by apply Hrem.
  rewrite <- (lookup_pow_power_value i Hrange Hops).
  reflexivity.
Qed.

Lemma shl_correct : forall i l r m,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_shl i = 1 ->
    etable_values lhs_u64_cell i = l ->
    etable_values rhs_u64_cell i = r ->
    etable_values rhs_modulus i = m ->
    etable_values res i = shl l r m.
Proof.
  intros i l r m Hrange Hops Hshl Hlhs Hrhs Hmod.
  pose(Hgate := bin_shift_shl i Hrange); simpl in *.
  replace(i+0) with i in * by lia.
  assert(Hl : etable_values is_l i = 1).
  - pose(left_op_enabled i Hrange Hops); lia.
  rewrite <- Hlhs, <- Hrhs, <- Hmod.
  unfold shl.
  rewrite(rhs_mod_rhs_modulus i Hrange Hops).
  rewrite(is_l_lhs_shifted_by_rhs_rem i Hrange Hops Hl).
  rewrite(is_l_lhs_decomp i Hrange Hops Hl).
  rewrite <- (size_modulus_value i Hrange Hops).
  rewrite(Z.add_comm _ _).
  pose(size_modulus_value i Hrange Hops).
  pose(rhs_modulus_value i Hrange Hops).
  pose(is_i32_bit i).
  rewrite(Z.mod_add _ _ _) by lia.
  rewrite(Z.mod_small _ _) by apply (is_l_rem_range i Hrange Hops Hl).
  lia.
Qed.

Lemma div_is_mul_inverse : forall a b c,
    b <> 0 ->
    c <> 0 ->
    (c | b) ->
    a / (b / c) = a * c / b.
Proof.
  intros a b c Hb Hc Hdiv.
  destruct Hdiv.
  rewrite H.
  rewrite(Z.div_mul _ _ Hc).
  rewrite(Zdiv_mult_cancel_r _ _ _ Hc).
  reflexivity.
Qed.

Lemma rotl_correct : forall i l r m,
    0 <= i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_rotl i = 1 ->
    etable_values lhs_u64_cell i = l ->
    etable_values rhs_u64_cell i = r ->
    etable_values rhs_modulus i = m ->
    etable_values res i = rotl l r m.
Proof.
  intros i l r m Hrange Hops Hrotl Hlhs Hrhs Hmod.
  pose(Hgate := bin_shift_rotl i Hrange); simpl in *.
  replace(i+0) with i in * by lia.
  assert(Hl : etable_values is_l i = 1).
  - pose(left_op_enabled i Hrange Hops); lia.
  rewrite <- Hlhs, <- Hrhs, <- Hmod.
  unfold rotl.
  rewrite(rhs_mod_rhs_modulus i Hrange Hops).
  rewrite(is_l_lhs_shifted_by_rhs_rem i Hrange Hops Hl).
  rewrite(is_l_lhs_decomp i Hrange Hops Hl).
  rewrite <- (size_modulus_value i Hrange Hops).
  rewrite(Z.add_comm _ (etable_values rem i)).
  pose(size_modulus_value i Hrange Hops).
  pose(rhs_modulus_value i Hrange Hops).
  pose(is_i32_bit i).
  rewrite(Z.mod_add _ _ _) by lia.
  rewrite(Z.mod_small _ _) by apply (is_l_rem_range i Hrange Hops Hl).
  pose(rhs_rem_range i Hrange Hops).
  rewrite(Z.shiftr_div_pow2 _ _) by lia.
  rewrite(Z.pow_sub_r _ _ _) by lia.
  rewrite <- (lookup_pow_power_value i Hrange Hops).
  rewrite <- (size_modulus_value i Hrange Hops).
  pose(lookup_pow_power_value i Hrange Hops).
  pose(lookup_divides_size i Hrange Hops).
  rewrite(div_is_mul_inverse _ _ _); auto; try lia.
  rewrite(is_l_lhs_decomp i Hrange Hops Hl).
  rewrite(Z.div_add_l _ _ _) by lia.
  rewrite(Z.div_small _ _) by apply (is_l_rem_range i Hrange Hops Hl).
  lia.
Qed.

Lemma binshift_mops : forall i,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    etable_values (ops_cell BinShift) i = 1 ->
    mops_at_correct i ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Hrow_enabled Hop_class Hops.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with BinShift in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i BinShift Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).

  assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  {
    apply (write_cell_with_value_mops _ _ _ _ _ _ stack_write i Hrange); auto.
    - apply (eid_common i).
    - apply (is_i32_bit).
    - pose (sp_common i); lia.
  }
  lia.
Qed.

Theorem BinShift_Shr_U_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_shr_u i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) (shr_u xl xr (64 - etable_values is_i32 i * 32) :: xs)).
Proof.
  intros i st xl xr xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (binshift_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].
  assert (Hrhs: etable_values rhs_u64_cell i = xr).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get rhs_u64_cell)
                                 (enable := fun get => get (ops_cell BinShift)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs_u64_cell i = xl).
  {
    eapply stack_rel_read_2_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get lhs_u64_cell)
                                 (enable := fun get => get (ops_cell BinShift)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = shr_u xl xr (64 - (etable_values is_i32 i) * 32)).
  {
    apply (shr_u_correct i _ _ _ Hrange Hop Hop_class Hlhs Hrhs).
    pose(rhs_modulus_value i Hrange Hop).
    pose(is_i32_bit i).
    lia.
  }
  rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hrhs Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := BinShift); auto.
    rewrite iid_change with (idx := BinShift); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get is_i32)
                                (enable := fun get => get (ops_cell BinShift)); auto; try lia.
  - apply (is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i BinShift); auto.
  - pose (mpages_change i BinShift); simpl in *; lia.        
  - rewrite (frame_id_change i BinShift); auto; reflexivity.
  - rewrite (fid_change i BinShift); auto.
  - apply stack_write.
Qed.

Theorem BinShift_Shr_S_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_shr_s i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) (shr_s xl xr (64 - etable_values is_i32 i * 32) :: xs)).
Proof.
  intros i st xl xr xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (binshift_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hrhs: etable_values rhs_u64_cell i = xr).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get rhs_u64_cell)
                                 (enable := fun get => get (ops_cell BinShift)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs_u64_cell i = xl).
  {
    eapply stack_rel_read_2_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get lhs_u64_cell)
                                 (enable := fun get => get (ops_cell BinShift)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = shr_s xl xr (64 - (etable_values is_i32 i) * 32)).
  {
    apply (shr_s_correct i _ _ _ Hrange Hop Hop_class Hlhs Hrhs).
    pose(rhs_modulus_value i Hrange Hop).
    pose(is_i32_bit i).
    lia.
  }
  rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hrhs Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := BinShift); auto.
    rewrite iid_change with (idx := BinShift); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get is_i32)
                                (enable := fun get => get (ops_cell BinShift)); auto; try lia.
  - apply (is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i BinShift); auto.
  - pose (mpages_change i BinShift); simpl in *; lia.        
  - rewrite (frame_id_change i BinShift); auto; reflexivity.
  - rewrite (fid_change i BinShift); auto.
  - apply stack_write.
Qed.

Theorem BinShift_Rotr_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_rotr i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) (rotr xl xr (64 - etable_values is_i32 i * 32) :: xs)).
Proof.
  intros i st xl xr xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (binshift_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hrhs: etable_values rhs_u64_cell i = xr).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get rhs_u64_cell)
                                 (enable := fun get => get (ops_cell BinShift)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs_u64_cell i = xl).
  {
    eapply stack_rel_read_2_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get lhs_u64_cell)
                                 (enable := fun get => get (ops_cell BinShift)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = rotr xl xr (64 - (etable_values is_i32 i) * 32)).
  {
    apply (rotr_correct i _ _ _ Hrange Hop Hop_class Hlhs Hrhs).
    pose(rhs_modulus_value i Hrange Hop).
    pose(is_i32_bit i).
    lia.
  }
  rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hrhs Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := BinShift); auto.
    rewrite iid_change with (idx := BinShift); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get is_i32)
                                (enable := fun get => get (ops_cell BinShift)); auto; try lia.
  - apply (is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i BinShift); auto.
  - pose (mpages_change i BinShift); simpl in *; lia.        
  - rewrite (frame_id_change i BinShift); auto; reflexivity.
  - rewrite (fid_change i BinShift); auto.
  - apply stack_write.
Qed.

Theorem BinShift_Shl_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_shl i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) (shl xl xr (64 - etable_values is_i32 i * 32) :: xs)).
Proof.
  intros i st xl xr xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (binshift_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hrhs: etable_values rhs_u64_cell i = xr).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get rhs_u64_cell)
                                 (enable := fun get => get (ops_cell BinShift)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs_u64_cell i = xl).
  {
    eapply stack_rel_read_2_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get lhs_u64_cell)
                                 (enable := fun get => get (ops_cell BinShift)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = shl xl xr (64 - (etable_values is_i32 i) * 32)).
  {
    apply (shl_correct i _ _ _ Hrange Hop Hop_class Hlhs Hrhs).
    pose(rhs_modulus_value i Hrange Hop).
    pose(is_i32_bit i).
    lia.
  }
  rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hrhs Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := BinShift); auto.
    rewrite iid_change with (idx := BinShift); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get is_i32)
                                (enable := fun get => get (ops_cell BinShift)); auto; try lia.
  - apply (is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i BinShift); auto.
  - pose (mpages_change i BinShift); simpl in *; lia.        
  - rewrite (frame_id_change i BinShift); auto; reflexivity.
  - rewrite (fid_change i BinShift); auto.
  - apply stack_write.
Qed.

Theorem BinShift_Rotl_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinShift) i = 1 ->
    etable_values is_rotl i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) (rotl xl xr (64 - etable_values is_i32 i * 32) :: xs)).
Proof.
  intros i st xl xr xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (binshift_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hrhs: etable_values rhs_u64_cell i = xr).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get rhs_u64_cell)
                                 (enable := fun get => get (ops_cell BinShift)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs_u64_cell i = xl).
  {
    eapply stack_rel_read_2_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get lhs_u64_cell)
                                 (enable := fun get => get (ops_cell BinShift)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = rotl xl xr (64 - (etable_values is_i32 i) * 32)).
  {
    apply (rotl_correct i _ _ _ Hrange Hop Hop_class Hlhs Hrhs).
    pose(rhs_modulus_value i Hrange Hop).
    pose(is_i32_bit i).
    lia.
  }
  rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hrhs Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := BinShift); auto.
    rewrite iid_change with (idx := BinShift); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.
  
  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get is_i32)
                                (enable := fun get => get (ops_cell BinShift)); auto; try lia.
  - apply (is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i BinShift); auto.
  - pose (mpages_change i BinShift); simpl in *; lia.        
  - rewrite (frame_id_change i BinShift); auto; reflexivity.
  - rewrite (fid_change i BinShift); auto.
  - apply stack_write.
Qed.
