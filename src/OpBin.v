(* Copyright (C) CertiK 2024-2026 *)

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
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config Bin i)) with 1.
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
    - apply OpBinModel.is_i32_bit.
    - pose(sp_common i); lia.
  lia.
Qed.

Lemma only_one_selector : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    (etable_values is_add i = 1 /\ etable_values is_sub i = 0 /\ etable_values is_mul i = 0 /\ etable_values is_div_u i = 0 /\ etable_values is_rem_u i = 0 /\ etable_values is_div_s i = 0 /\ etable_values is_rem_s i = 0) \/
    (etable_values is_add i = 0 /\ etable_values is_sub i = 1 /\ etable_values is_mul i = 0 /\ etable_values is_div_u i = 0 /\ etable_values is_rem_u i = 0 /\ etable_values is_div_s i = 0 /\ etable_values is_rem_s i = 0) \/
    (etable_values is_add i = 0 /\ etable_values is_sub i = 0 /\ etable_values is_mul i = 1 /\ etable_values is_div_u i = 0 /\ etable_values is_rem_u i = 0 /\ etable_values is_div_s i = 0 /\ etable_values is_rem_s i = 0) \/
    (etable_values is_add i = 0 /\ etable_values is_sub i = 0 /\ etable_values is_mul i = 0 /\ etable_values is_div_u i = 1 /\ etable_values is_rem_u i = 0 /\ etable_values is_div_s i = 0 /\ etable_values is_rem_s i = 0) \/
    (etable_values is_add i = 0 /\ etable_values is_sub i = 0 /\ etable_values is_mul i = 0 /\ etable_values is_div_u i = 0 /\ etable_values is_rem_u i = 1 /\ etable_values is_div_s i = 0 /\ etable_values is_rem_s i = 0) \/
    (etable_values is_add i = 0 /\ etable_values is_sub i = 0 /\ etable_values is_mul i = 0 /\ etable_values is_div_u i = 0 /\ etable_values is_rem_u i = 0 /\ etable_values is_div_s i = 1 /\ etable_values is_rem_s i = 0) \/
    (etable_values is_add i = 0 /\ etable_values is_sub i = 0 /\ etable_values is_mul i = 0 /\ etable_values is_div_u i = 0 /\ etable_values is_rem_u i = 0 /\ etable_values is_div_s i = 0 /\ etable_values is_rem_s i = 1).
Proof.
  intros i Hrange Hops.
  pose(H := bin_selector i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  pose(Hadd := is_add_bit i).
  pose(Hsub := is_sub_bit i).
  pose(Hmul := is_mul_bit i).
  pose(Hdivu := is_div_u_bit i).
  pose(Hremu := is_rem_u_bit i).
  pose(Hdivs := is_div_s_bit i).
  pose(Hrems := is_rem_s_bit i).
  pose(Hcommon := CommonModel.common_lt_order).
  simpl Z.shiftl in Hcommon.
  destruct Hadd.
  destruct Hsub.
  destruct Hmul.
  destruct Hdivu.
  destruct Hremu.
  destruct Hdivs.
  destruct Hrems.
  - rewrite H0, H1, H2, H3, H4, H5, H6, Hops in H.
    replace(1 * (0 + 0 + 0 + 0 + 0 + 0 + 0 - 1)) with (-1) in H by lia.
    destruct H as [H _].
    apply Znumtheory.Zmod_divide in H; [| lia].
    rewrite (Z.divide_opp_r _ 1) in H.
    apply Z.divide_pos_le in H; [| lia].
    assert(field_order > 1) by lia.
    contradiction.
  - right. right. right. right. right. right. 
    rewrite Z.mod_small in H by lia. lia.
  destruct Hrems.
  - right. right. right. right. right. left. 
    rewrite Z.mod_small in H by lia. lia.
  - assert(1 = 0). 
    rewrite Z.mod_small in H by lia. lia. lia.
  destruct Hdivs.
  destruct Hrems.
  - right. right. right. right. left.
    rewrite Z.mod_small in H by lia. lia.
  - assert(1 = 0). 
    rewrite Z.mod_small in H by lia. lia. lia.
  - assert(1 = 0). 
    rewrite Z.mod_small in H by lia. lia. lia.
  - rewrite Z.mod_small in H by lia.
    destruct Hremu.
    destruct Hdivs.
    destruct Hrems.
    right. right. right. left. lia.
    assert(1 = 0). lia. lia.
    assert(1 = 0 \/ 2 = 0). lia. lia.
    assert(1 = 0 \/ 2 = 0 \/ 3 = 0). lia. lia.
  - rewrite Z.mod_small in H by lia.
    right. right. left. lia.
  - rewrite Z.mod_small in H by lia.
    right. left. lia.
  - rewrite Z.mod_small in H by lia.
    left. lia.
Qed.

Require Import ImageTableModel.
Require Import InjectivityHelper.

Definition Bin_op i :=
  if (Z.eq_dec (etable_values is_add i) 1) then ADD
  else if (Z.eq_dec (etable_values is_sub i) 1) then SUB
  else if (Z.eq_dec (etable_values is_mul i) 1) then MUL
  else if (Z.eq_dec (etable_values is_div_u i) 1) then DIV_u
  else if (Z.eq_dec (etable_values is_rem_u i) 1) then REM_u
  else if (Z.eq_dec (etable_values is_div_s i) 1) then DIV_s
  else REM_s.

Lemma Bin_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values ETableModel.enabled_cell i = 1 ->
  etable_values (ops_cell Bin) i = 1 ->
  exists op,
    op = Bin_op i
    /\ program (wasm_pc st) = IBin (bool_of_Z (etable_values is_i32 i)) op
    /\ match op with
         ADD => etable_values is_add i = 1
       | SUB => etable_values is_sub i = 1
       | MUL => etable_values is_mul i = 1
       | DIV_u => etable_values is_div_u i = 1
       | REM_u => etable_values is_rem_u i = 1
       | DIV_s => etable_values is_div_s i = 1
       | REM_s => etable_values is_rem_s i = 1 end.
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i Bin Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  destruct (only_one_selector i Hrange Hops) as [Hsel | [Hsel | [Hsel | [Hsel | [Hsel | [Hsel | Hsel]]]]]].
  - exists ADD.
    split. {
      unfold Bin_op.
      destruct Hsel as [H1 _].
      rewrite H1. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpBinModel.is_i32_bit. }
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 [Hsel6 Hsel7]]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    reflexivity.

  - exists SUB.
    split. {
      unfold Bin_op.
      destruct Hsel as [H1 [H2 _]].
      rewrite H1, H2. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 [Hsel6 Hsel7]]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpBinModel.is_i32_bit. }
    reflexivity.

  - exists MUL.
    split. {
      unfold Bin_op.
      destruct Hsel as [H1 [H2 [H3 _]]].
      rewrite H1, H2, H3. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 [Hsel6 Hsel7]]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpBinModel.is_i32_bit. }
    reflexivity.

  - exists DIV_u.
    split. {
      unfold Bin_op.
      destruct Hsel as [H1 [H2 [H3 [H4 _]]]].
      rewrite H1, H2, H3, H4. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 [Hsel6 Hsel7]]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpBinModel.is_i32_bit. }
    reflexivity.

  - exists REM_u.
    split. {
      unfold Bin_op.
      destruct Hsel as [H1 [H2 [H3 [H4 [H5 _]]]]].
      rewrite H1, H2, H3, H4, H5. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 [Hsel6 Hsel7]]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpBinModel.is_i32_bit. }
    reflexivity.

  - exists DIV_s.
    split. {
      unfold Bin_op.
      destruct Hsel as [H1 [H2 [H3 [H4 [H5 [H6 _]]]]]].
      rewrite H1, H2, H3, H4, H5, H6. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 [Hsel6 Hsel7]]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpBinModel.is_i32_bit. }
    reflexivity.

  - exists REM_s.
    split. {
      unfold Bin_op.
      destruct Hsel as [H1 [H2 [H3 [H4 [H5 [H6 _]]]]]].
      rewrite H1, H2, H3, H4, H5, H6. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 [Hsel6 Hsel7]]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpBinModel.is_i32_bit. }
    reflexivity.
Qed.

Lemma size_modulus_value : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values size_modulus i mod field_order = 2^(64 - etable_values is_i32 i * 32).
Proof.
  intros i Hrange Hops.
  pose(H := bin_size_modulus i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  pose(CommonModel.int_lt_order).
  destruct(OpBinModel.is_i32_bit i) as [Hbit | Hbit]; rewrite Hbit in *.
  - rewrite Hops in H.
    rewrite Z.mul_0_l, Z.add_0_r, Z.mul_1_l in H.
    destruct H as [H _].
    apply Zmod_divides in H; [| lia].
    destruct H as [c H].
    rewrite Z.sub_move_r in H.
    apply (f_equal (fun t => t mod field_order)) in H.
    rewrite Z.add_comm, Z.mul_comm in H.
    rewrite Z.mod_add in H by lia.
    rewrite (Z.mod_small (2^64) _) in H; auto.
    lia.
  - rewrite Hops in H.
    repeat rewrite Z.mul_1_l in H.
    replace (etable_values size_modulus i - 18446744073709551616 +
      18446744069414584320) with (etable_values size_modulus i - 2^32) in H by lia.
    destruct H as [H _].
    apply Zmod_divides in H; [| lia].
    destruct H as [c H].
    rewrite Z.sub_move_r in H.
    apply (f_equal (fun t => t mod field_order)) in H.
    rewrite Z.add_comm, Z.mul_comm in H.
    rewrite Z.mod_add in H by lia.
    rewrite (Z.mod_small (2^32) _) in H; auto.
    lia.
Qed.

Lemma res_range : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    0 <= etable_values res i < etable_values size_modulus i mod field_order.
Proof.
  intros i Hrange Hops.
  replace(etable_values size_modulus i mod field_order) with 
    (2^(64 - (etable_values is_i32 i) * 32)).
  eapply write_with_value_range with (is_i32 := fun get => get is_i32)
                                 (sp := fun get => get sp_cell + 2)
                                 (enable := fun get => get (ops_cell Bin))
                                 (loctyp := MTableModel.LocationType_Stack); auto.
  - pose (sp_common i); lia.
  - apply (OpBinModel.is_i32_bit i).
  - apply stack_write.
  pose(Hsize := size_modulus_value i Hrange Hops).
  destruct (OpBinModel.is_i32_bit i) as [H0 | H1].
  - rewrite H0 in *; lia.
  - rewrite H1 in *; lia.
Qed.

Lemma res_le_int64 : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    0 <= etable_values res i < 2^64.
Proof.
  intros i Hrange Hops.
  pose(res_range i Hrange Hops).
  rewrite size_modulus_value in *; auto.
  destruct(OpBinModel.is_i32_bit i) as [H | H]; rewrite H in *; lia.
Qed.

Lemma lhs_range : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    0 <= etable_values lhs_u64_cell i < 2^(64 - (etable_values is_i32 i) * 32).
Proof.
  intros i Hrange Hops.
  eapply read_range with (is_i32 := fun get => get is_i32)
                           (sp := fun get => get sp_cell + 2)
                           (value := fun get => get lhs_u64_cell)
                           (enable := fun get => get (ops_cell Bin))
                           (loctyp := MTableModel.LocationType_Stack); auto.
    - pose (sp_common i); lia.
    - apply (OpBinModel.is_i32_bit i).
    - apply stack_read_lhs.
Qed.

Lemma lhs_le_int64 : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    0 <= etable_values lhs_u64_cell i < 2^64.
Proof.
  intros i Hrange Hops.
  pose(lhs_range i Hrange Hops).
  destruct(OpBinModel.is_i32_bit i) as [H | H]; rewrite H in *; lia.
Qed.

Lemma rhs_range : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    0 <= etable_values rhs_u64_cell i < 2^(64 - (etable_values is_i32 i) * 32).
Proof.
  intros i Hrange Hops.
  - eapply read_range with (is_i32 := fun get => get is_i32)
                           (sp := fun get => get sp_cell + 1)
                           (value := fun get => get rhs_u64_cell)
                           (enable := fun get => get (ops_cell Bin))
                           (loctyp := MTableModel.LocationType_Stack); auto.
    - pose (sp_common i); lia.
    - apply (OpBinModel.is_i32_bit i).
    - apply stack_read_rhs.
Qed.

Lemma rhs_le_int64 : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    0 <= etable_values rhs_u64_cell i < 2^64.
Proof.
  intros i Hrange Hops.
  pose(rhs_range i Hrange Hops).
  destruct(OpBinModel.is_i32_bit i) as [H | H]; rewrite H in *; lia.
Qed.

Lemma add_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_add i = 1 ->
    etable_values lhs_u64_cell i = l ->
    etable_values rhs_u64_cell i = r ->
    etable_values res i = (l + r) mod (2^(64 - (etable_values is_i32 i) * 32)).
Proof.
  intros i l r Hrange Hops Hadd Hl Hr.
  pose(H := bin_add i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  rewrite Hl, Hr, Hops, Hadd in H.
  rewrite Z.mul_1_l in H.
  destruct H as [H _].
  pose(CommonModel.int_lt_order).
  apply Zmod_divides in H; [| lia].
  destruct H as [c H].
  pose(Hsize := size_modulus_value i Hrange Hops).
  apply Znumtheory.Zmod_divide_minus in Hsize; [| lia].
  apply Znumtheory.Zdivide_Zdiv_eq in Hsize; [| lia].
  remember ((etable_values size_modulus i - 2^(64 - etable_values is_i32 i * 32)) / field_order) as c'.
  rewrite Z.sub_move_r in Hsize.
  repeat rewrite Z.sub_move_r in H.
  rewrite Hsize in H.
  apply (f_equal (fun t => t mod field_order)) in H.
  rewrite (Z.mod_small (l+r)) in H.
  2: {
    pose(lhs_le_int64 i Hrange Hops).
    pose(rhs_le_int64 i Hrange Hops).
    lia.
  }
  replace (field_order * c + etable_values overflow i *
    (field_order * c' + 2 ^ (64 - etable_values is_i32 i * 32)) +
    etable_values res i) with (etable_values res i + 
    etable_values overflow i * 2 ^ (64 - etable_values is_i32 i * 32)
    + (c + etable_values overflow i * c') * field_order) in H by lia.
  rewrite Z.mod_add in H by lia.
  rewrite Z.mod_small in H.
  2: {
    pose(res_le_int64 i Hrange Hops).
    destruct(overflow_bit i).
    destruct(OpBinModel.is_i32_bit i) as [Hbit | Hbit]; rewrite Hbit in *; lia.
    destruct(OpBinModel.is_i32_bit i) as [Hbit | Hbit]; rewrite Hbit in *; lia.
  }
  apply (f_equal (fun t => t mod (2 ^ (64 - etable_values is_i32 i * 32)))) in H.
  pose(OpBinModel.is_i32_bit i).
  rewrite Z.mod_add in H by lia.
  rewrite(Z.mod_small (etable_values res i) _) in H; auto.
  rewrite <- size_modulus_value; auto.
  apply res_range; auto.
Qed.

Lemma sub_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_sub i = 1 ->
    etable_values lhs_u64_cell i = l ->
    etable_values rhs_u64_cell i = r ->
    etable_values res i = (l - r) mod (2^(64 - etable_values is_i32 i * 32)).
Proof.
  intros i l r Hrange Hops Hsub Hl Hr.
  pose(H := bin_sub i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  rewrite Hl, Hr, Hops, Hsub in H.
  rewrite Z.mul_1_l in H.
  destruct H as [H _].
  pose(CommonModel.int_lt_order).
  apply Zmod_divides in H; [| lia].
  destruct H as [c H].
  pose(Hsize := size_modulus_value i Hrange Hops).
  apply Znumtheory.Zmod_divide_minus in Hsize; [| lia].
  apply Znumtheory.Zdivide_Zdiv_eq in Hsize; [| lia].
  remember ((etable_values size_modulus i - 2^(64 - etable_values is_i32 i * 32)) / field_order) as c'.
  rewrite Z.sub_move_r in Hsize.
  repeat rewrite Z.sub_move_r in H.
  rewrite Hsize in H.
  apply (f_equal (fun t => t mod field_order)) in H.
  rewrite (Z.mod_small (r + etable_values res i)) in H.
  2: {
    pose(res_le_int64 i Hrange Hops).
    pose(rhs_le_int64 i Hrange Hops).
    lia.
  }
  replace (field_order * c + etable_values overflow i *
    (field_order * c' + 2 ^ (64 - etable_values is_i32 i * 32)) + l) 
    with (l + etable_values overflow i * 2 ^ (64 - etable_values is_i32 i * 32)
    + (c + etable_values overflow i * c') * field_order) in H by lia.
  rewrite Z.mod_add in H by lia.
  rewrite Z.mod_small in H.
  2: {
    pose(lhs_le_int64 i Hrange Hops).
    destruct(overflow_bit i).
    destruct(OpBinModel.is_i32_bit i) as [Hbit | Hbit]; rewrite Hbit in *; lia.
    destruct(OpBinModel.is_i32_bit i) as [Hbit | Hbit]; rewrite Hbit in *; lia.
  }
  rewrite Z.add_move_l in H.
  rewrite Z.add_sub_swap in H.
  apply (f_equal (fun t => t mod (2 ^ (64 - etable_values is_i32 i * 32)))) in H.
  pose(OpBinModel.is_i32_bit i).
  rewrite Z.mod_add in H by lia.
  rewrite(Z.mod_small (etable_values res i) _) in H; auto.
  rewrite <- size_modulus_value; auto.
  apply res_range; auto.
Qed.

Lemma mul_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_mul i = 1 ->
    etable_values lhs_u64_cell i = l ->
    etable_values rhs_u64_cell i = r ->
    etable_values res i = (l * r) mod (2^(64 - etable_values is_i32 i * 32)).
Proof.
  intros i l r Hrange Hops Hmul Hl Hr.
  pose(H := bin_mul_constraints i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  rewrite Hl, Hr, Hops, Hmul in H.
  rewrite Z.mul_1_l in H.
  destruct H as [H _].
  pose(CommonModel.int_lt_order).
  apply Zmod_divides in H; [| lia].
  destruct H as [c H].
  pose(Hsize := size_modulus_value i Hrange Hops).
  apply Znumtheory.Zmod_divide_minus in Hsize; [| lia].
  apply Znumtheory.Zdivide_Zdiv_eq in Hsize; [| lia].
  remember ((etable_values size_modulus i - 2^(64 - etable_values is_i32 i * 32)) / field_order) as c'.
  rewrite Z.sub_move_r in Hsize.
  repeat rewrite Z.sub_move_r in H.
  rewrite Hsize in H.
  apply (f_equal (fun t => t mod field_order)) in H.
  rewrite (Z.mod_small (l * r)) in H.
  2: {
    pose(lhs_le_int64 i Hrange Hops).
    pose(rhs_le_int64 i Hrange Hops).
    assert(0 <= l * r < 2^128).
    - change (2^128) with (2^64 * 2^64).
      split; [lia |].
      apply Zmult_lt_compat; lia.
      lia.
  }
  replace (field_order * c + etable_values res i + etable_values aux1 i *
    (field_order * c' + 2 ^ (64 - etable_values is_i32 i * 32))) 
    with (etable_values res i + etable_values aux1 i * 2 ^ (64 - etable_values is_i32 i * 32)
    + (c + etable_values aux1 i * c') * field_order) in H by lia.
  rewrite Z.mod_add in H by lia.
  rewrite Z.mod_small in H.
  2: {
    pose(res_le_int64 i Hrange Hops).
    destruct(aux1_U64 i).
    change Wasm_int.Int64.modulus with (2^64) in *.
    destruct(OpBinModel.is_i32_bit i) as [Hbit | Hbit]; rewrite Hbit in *; lia.
  }
  apply (f_equal (fun t => t mod (2 ^ (64 - etable_values is_i32 i * 32)))) in H.
  pose(OpBinModel.is_i32_bit i).
  rewrite Z.mod_add in H by lia.
  rewrite(Z.mod_small (etable_values res i) _) in H; auto.
  rewrite <- size_modulus_value; auto.
  apply res_range; auto.
Qed.

Lemma mod_move : forall a b n,
    n > 0 ->
    (a - b) mod n = 0 ->
    a mod n = b mod n.
Proof.
  intros.
  rewrite Zmod_divides in H0 by lia.
  destruct H0 as [c H0].
  rewrite Z.sub_move_r in H0.
  apply (f_equal (fun t => t mod n)) in H0.
  rewrite Z.add_comm, Z.mul_comm in H0.
  rewrite Z_mod_plus in H0 by lia; auto.
Qed.

Lemma unsigned_aux1_range : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_u i = 1 \/ etable_values is_rem_u i = 1 ->
    0 <= etable_values aux1 i < etable_values rhs_u64_cell i.
Proof.
  intros i Hrange Hops Hu.
  pose(H := bin_div_u_rem_u_constraints i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [H _]].
  replace(etable_values is_rem_u i + etable_values is_div_u i) with 1 in H.
  2: { pose(only_one_selector i Hrange Hops); lia. }
  rewrite Hops in H.
  rewrite Z.mul_1_l in H.
  pose(CommonModel.int_lt_order).
  apply mod_move in H; try lia.
  pose(rhs_le_int64 i Hrange Hops).
  pose(aux1_U64 i).
  pose(aux2_U64 i).
  change Wasm_int.Int64.modulus with (2^64) in *.
  rewrite Z.mod_small in H by lia.
  rewrite Z.mod_small in H by lia.
  lia.
Qed.

Lemma d_range : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    0 <= etable_values d_u64_cell i < 2^64.
Proof.
  intros i Hrange Hops.
  pose(d_U64 i).
  destruct(d_u16_cells_U16) as [H0 [H1 [H2 H3]]].
  specialize (H0 i); specialize (H1 i); specialize (H2 i); specialize (H3 i).
  lia.
Qed.

Lemma unsigned_lhs_decomp : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_u i = 1 \/ etable_values is_rem_u i = 1 ->
    etable_values lhs_u64_cell i = 
    etable_values d_u64_cell i * etable_values rhs_u64_cell i +
    etable_values aux1 i.
Proof.
  intros i Hrange Hops Hu.
  pose(H := bin_div_u_rem_u_constraints i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [H _].
  replace(etable_values is_rem_u i + etable_values is_div_u i) with 1 in H.
  2: { pose(only_one_selector i Hrange Hops); lia. }
  rewrite Hops in H.
  rewrite Z.mul_1_l in H.
  pose(CommonModel.int_lt_order).
  rewrite <- Z.sub_add_distr in H.
  apply mod_move in H; try lia.
  rewrite Z.mod_small in H.
  rewrite Z.mod_small in H; try lia.
  pose(rhs_le_int64 i Hrange Hops).
  pose(d_range i Hrange Hops).
  destruct (aux1_U64 i) as [? Halt].
  change Wasm_int.Int64.modulus with (2^64) in *.
  split; try lia.
  assert(etable_values rhs_u64_cell i * etable_values d_u64_cell i < 2^64 * 2^64).
  - apply Zmult_lt_compat; lia.
    pose proof (Z.add_lt_mono _ _ _ _ H1 Halt).
    lia.
  pose(lhs_le_int64 i Hrange Hops); lia.
Qed.

Lemma unsigned_lhs_div_unique : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_u i = 1 \/ etable_values is_rem_u i = 1 ->
    Z.div_eucl (etable_values lhs_u64_cell i) (etable_values rhs_u64_cell i) =
    (etable_values d_u64_cell i, etable_values aux1 i).
Proof.
  intros i Hrange Hops Hu.
  rewrite(Zaux.Zdiv_eucl_unique _ _).
  rewrite(unsigned_lhs_decomp i Hrange Hops Hu).
  pose(unsigned_aux1_range i Hrange Hops Hu).
  rewrite(Z.div_add_l _ _) by lia.
  rewrite(Z.div_small _ _) by assumption.
  rewrite(Z.add_comm _ (etable_values aux1 i)).
  rewrite(Z.mod_add _ _ _) by lia.
  rewrite(Z.mod_small _ _) by assumption.
  rewrite(Z.add_0_r _).
  reflexivity.
Qed.

Lemma div_u_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_u i = 1 ->
    etable_values lhs_u64_cell i = l ->
    etable_values rhs_u64_cell i = r ->
    etable_values res i = l / r.
Proof.
  intros i l r Hrange Hops Hdivu Hl Hr.
  pose(H := bin_div_u_rem_u_constraints i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [_ [H _]]].
  replace(etable_values res i) with (etable_values d_u64_cell i).
  2: {
    rewrite Hops, Hdivu in H.
    rewrite Z.mul_1_l in H.
    pose(CommonModel.int_lt_order).
    apply mod_move in H; try lia.
    pose(d_range i Hrange Hops).
    pose(res_le_int64 i Hrange Hops).
    rewrite Z.mod_small in H by lia.
    rewrite Z.mod_small in H by lia; auto.
  }
  pose(Hdiv := unsigned_lhs_div_unique i Hrange Hops).
  pose(Heucl := Zaux.Zdiv_eucl_unique l r).
  rewrite Hl, Hr in *.
  rewrite Hdiv in Heucl by lia.
  apply (pair_equal_spec _ _ _ _) in Heucl.
  lia.
Qed.

Lemma rem_u_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_rem_u i = 1 ->
    etable_values lhs_u64_cell i = l ->
    etable_values rhs_u64_cell i = r ->
    etable_values res i = l mod r.
Proof.
  intros i l r Hrange Hops Hremu Hl Hr.
  pose(H := bin_div_u_rem_u_constraints i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [_ [_ [H _]]]].
  replace(etable_values res i) with (etable_values aux1 i).
  2: {
    rewrite Hops, Hremu in H.
    rewrite Z.mul_1_l in H.
    pose(CommonModel.int_lt_order).
    apply mod_move in H; [| lia].
    pose(res_le_int64 i Hrange Hops).
    rewrite Z.mod_small in H by lia.
    pose(aux1_U64 i).
    change Wasm_int.Int64.modulus with (2^64) in *.
    rewrite Z.mod_small in H by lia; auto.
  }
  pose(Hdiv := unsigned_lhs_div_unique i Hrange Hops).
  pose(Heucl := Zaux.Zdiv_eucl_unique l r).
  rewrite Hl, Hr in *.
  rewrite Hdiv in Heucl by lia.
  apply (pair_equal_spec _ _ _ _) in Heucl.
  lia.
Qed.

Lemma res_flag_value : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values res_flag i mod field_order =
    (Z.lxor (etable_values lhs_flag_bit_cell i) (etable_values rhs_flag_bit_cell i)).
Proof.
  intros i Hrange Hops.
  pose(H := bin_res_flag i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  rewrite Hops, Z.mul_1_l in H.
  destruct H as [H _].
  pose(Hlbit := lhs_flag_bit_cell_bit i).
  pose(Hrbit := rhs_flag_bit_cell_bit i).
  pose(CommonModel.int_lt_order).
  destruct Hlbit as [Hl0 | Hl1].
  - rewrite Hl0 in *.
    rewrite (Z.lxor_0_l _).
    rewrite Z.add_0_l, Z.mul_0_l, Z.sub_0_r in H.
    apply mod_move in H; [| lia].
    rewrite(Z.mod_small (etable_values rhs_flag_bit_cell i) _) in H by lia.
    auto.
  - destruct Hrbit as [Hr0 | Hr1].
    - rewrite Hl1, Hr0 in *.
      rewrite (Z.lxor_0_r _).
      change (1 + 0 - 2 * 0) with 1 in H.
      apply mod_move in H; [| lia].
      rewrite(Z.mod_small 1 _) in H by lia.
      auto.
    - rewrite Hl1, Hr1 in *.
      rewrite (Z.lxor_nilpotent _).
      change (1 + 1 - 2 * 1) with 0 in H.
      rewrite Z.sub_0_r in H; auto.
Qed.

Lemma res_flag_bit : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values res_flag i mod field_order = 0 \/ 
    etable_values res_flag i mod field_order = 1.
Proof.
  intros i Hrange Hops.
  rewrite(res_flag_value i Hrange Hops).
  pose(Hl := lhs_flag_bit_cell_bit i).
  pose(Hr := rhs_flag_bit_cell_bit i).
  destruct Hl as [Hl0 | Hl1].
  - rewrite Hl0.
    rewrite (Z.lxor_0_l _).
    assumption.
  - rewrite Hl1.
    destruct Hr as [Hr0 | Hr1].
    - rewrite Hr0.
      rewrite (Z.lxor_0_r _).
      auto.
    - rewrite Hr1.
      rewrite (Z.lxor_nilpotent _).
      auto.
Qed.

Lemma is_div_s_or_rem_s_value : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_s i = 1 \/ etable_values is_rem_s i = 1 ->
    etable_values is_div_s_or_rem_s i = 1.
Proof. 
  intros i Hrange Hops Hs.
  pose(H := bin_div_s_rem_s_constraints_common i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [H _].
  rewrite Hops, Z.mul_1_l in H.
  pose(CommonModel.int_lt_order).
  apply mod_move in H; [| lia].
  pose(is_div_s_or_rem_s_bit i).
  rewrite Z.mod_small in H by lia.
  pose(is_div_s_bit i).
  pose(is_rem_s_bit i).
  rewrite Z.mod_small in H by lia.
  pose(only_one_selector i Hrange Hops).
  lia.
Qed.

Lemma normalized_lhs_value : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    (etable_values lhs_flag_bit_cell i = 0 -> 
      etable_values normalized_lhs i mod field_order = etable_values lhs_u64_cell i) /\
    (etable_values lhs_flag_bit_cell i = 1 ->
      etable_values normalized_lhs i mod field_order = 
      etable_values size_modulus i mod field_order - etable_values lhs_u64_cell i).
Proof.
  intros i Hrange Hops.
  pose(H := bin_div_s_rem_s_constraints_common i Hrange).
  unfold ForallP in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [H _]].
  simpl value in H.
  rewrite Hops, Z.mul_1_l in H.
  pose(CommonModel.int_lt_order).
  split; intros.
  - rewrite H0 in H.
    rewrite Z.mul_0_r, Z.add_0_r in H.
    rewrite Z.sub_0_r, Z.mul_1_r in H.
    apply mod_move in H; [| lia].
    pose(lhs_le_int64 i Hrange Hops).
    rewrite(Z.mod_small (etable_values lhs_u64_cell i) _) in H by lia.
    auto.
  - rewrite H0 in *.
    rewrite Z.sub_diag, Z.mul_0_r, Z.add_0_l in H.
    rewrite Z.mul_1_r in H.
    apply mod_move in H; [| lia]; auto. 
    rewrite <- Zminus_mod_idemp_l in H.
    rewrite(Z.mod_small (etable_values size_modulus i mod field_order 
      - etable_values lhs_u64_cell i)) in H; auto.
    rewrite size_modulus_value; auto.
    pose(lhs_range i Hrange Hops).
    split; try lia.
    destruct(OpBinModel.is_i32_bit i) as [Hbit | Hbit]; rewrite Hbit; lia.
Qed.

Lemma normalized_rhs_value : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    (etable_values rhs_flag_bit_cell i = 0 -> 
      etable_values normalized_rhs i mod field_order = etable_values rhs_u64_cell i) /\
    (etable_values rhs_flag_bit_cell i = 1 ->
      etable_values normalized_rhs i mod field_order = 
      etable_values size_modulus i mod field_order - etable_values rhs_u64_cell i).
Proof.
  intros i Hrange Hops.
  pose(H := bin_div_s_rem_s_constraints_common i Hrange).
  unfold ForallP in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [_ [H _]]].
  simpl value in H.
  rewrite Hops, Z.mul_1_l in H.
  pose(CommonModel.int_lt_order).
  split; intros.
  - rewrite H0 in H.
    rewrite Z.mul_0_r, Z.add_0_r in H.
    rewrite Z.sub_0_r, Z.mul_1_r in H.
    apply mod_move in H; [| lia].
    pose(rhs_le_int64 i Hrange Hops).
    rewrite(Z.mod_small (etable_values rhs_u64_cell i) _) in H by lia.
    auto.
  - rewrite H0 in *.
    rewrite Z.sub_diag, Z.mul_0_r, Z.add_0_l in H.
    rewrite Z.mul_1_r in H.
    apply mod_move in H; [| lia]; auto. 
    rewrite <- Zminus_mod_idemp_l in H.
    rewrite(Z.mod_small (etable_values size_modulus i mod field_order 
      - etable_values rhs_u64_cell i)) in H; auto.
    rewrite size_modulus_value; auto.
    pose(rhs_range i Hrange Hops).
    split; try lia.
    destruct(OpBinModel.is_i32_bit i) as [Hbit | Hbit]; rewrite Hbit; lia.
Qed.

Lemma sixteen_most_significant_bits_of_lhs : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
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
  pose(H := OpBinModel.is_i32_bit i).
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
    pose(lhs_range i Hrange Hops).
    rewrite Hbit1 in *.
    assert(etable_values lhs_u16_cells_le_2 i = 0 /\ etable_values lhs_u16_cells_le_3 i = 0).
    - lia.
    lia.
Qed.

Lemma lhs_flag_bit_cell_is_most_significant_bit_of_lhs : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
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
  pose(CommonModel.common_lt_order); simpl Z.shiftl in *.
  apply mod_move in Hdecomp; [| lia].
  rewrite Z.mod_small in Hdecomp.
  2: {
    pose(lhs_flag_bit_cell_bit i).
    pose(lhs_flag_u16_rem_cell_common i).
    lia.
  }
  rewrite Z.mod_small in Hdecomp.
  2: {
    pose(CommonModel.int_lt_order).
    destruct(lhs_u16_cells_U16) as [_ [H1 [_ H3]]].
    specialize (H1 i); specialize (H3 i).
    destruct (OpBinModel.is_i32_bit i) as [H | H]; rewrite H; lia.
  }
  replace(etable_values lhs_u16_cells_le_3 i + etable_values is_i32 i *
    (etable_values lhs_u16_cells_le_1 i - etable_values lhs_u16_cells_le_3 i)) with
    (etable_values lhs_flag_bit_cell i * 2^15 + etable_values lhs_flag_u16_rem_cell i) by lia.
  rewrite(Z.shiftr_div_pow2 _ _) by lia.
  rewrite(Z.div_add_l _ _ _) by lia.
  rewrite(Z.div_small _ _).
  lia.
  apply mod_move in Hflag_range; [| lia].
  pose(lhs_flag_u16_rem_cell_common i).
  pose(lhs_flag_u16_rem_diff_cell_common i).
  rewrite Z.mod_small in Hflag_range by lia.
  rewrite Z.mod_small in Hflag_range by lia.
  lia.
Qed.

Lemma sixteen_most_significant_bits_of_rhs : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values rhs_u16_cells_le_3 i + etable_values is_i32 i
    * (etable_values rhs_u16_cells_le_1 i - etable_values rhs_u16_cells_le_3 i)
    = Z.shiftr (etable_values rhs_u64_cell i) (48 - etable_values is_i32 i * 32).
Proof.
  intros i Hrange Hops.
  pose(Hrhs := rhs_U64 i).
  pose(Hu16 := rhs_u16_cells_U16).
  destruct Hu16 as [H0 [H1 [H2 H3]]].
  specialize(H0 i); specialize(H1 i); specialize(H2 i); specialize(H3 i).
  rewrite Hrhs.
  pose(H := OpBinModel.is_i32_bit i).
  rewrite(Z.shiftr_div_pow2 _ _) by lia.
  destruct H as [Hbit0 | Hbit1].
  - rewrite Hbit0; simpl.
    rewrite(Z.div_add _ _ _) by lia.
    rewrite(Z.div_small _ _) by lia.
    lia.
  - rewrite Hbit1.
    replace(etable_values rhs_u16_cells_le_3 i + 1 *
      (etable_values rhs_u16_cells_le_1 i - etable_values rhs_u16_cells_le_3 i)) with
      (etable_values rhs_u16_cells_le_1 i) by lia.
    simpl.
    replace(etable_values rhs_u16_cells_le_0 i +
      etable_values rhs_u16_cells_le_1 i * Z.pow_pos 2 16 +
      etable_values rhs_u16_cells_le_2 i * Z.pow_pos 2 32 +
      etable_values rhs_u16_cells_le_3 i * Z.pow_pos 2 48) with
      (etable_values rhs_u16_cells_le_0 i +
      (etable_values rhs_u16_cells_le_1 i +
      etable_values rhs_u16_cells_le_2 i * Z.pow_pos 2 16 +
      etable_values rhs_u16_cells_le_3 i * Z.pow_pos 2 32) * Z.pow_pos 2 16) by lia.
    rewrite(Z.div_add _ _ _) by lia.
    rewrite(Z.div_small _ _) by apply H0.
    pose(rhs_range i Hrange Hops).
    rewrite Hbit1 in *.
    assert(etable_values rhs_u16_cells_le_2 i = 0 /\ etable_values rhs_u16_cells_le_3 i = 0).
    - lia.
    lia.
Qed.

Lemma rhs_flag_bit_cell_is_most_significant_bit_of_rhs : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values rhs_flag_bit_cell i =
    Z.shiftr (etable_values rhs_u64_cell i) (63 - (etable_values is_i32 i) * 32).
Proof.
  intros i Hrange Hops.
  pose(H := rhs_flag_bit_dyn i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [Hdecomp [Hflag_range _]].
  replace(63 - etable_values is_i32 i * 32) with
    (48 - etable_values is_i32 i * 32 + 15) by lia.
  rewrite <- (Z.shiftr_shiftr _ _ _) by lia.
  rewrite <- (sixteen_most_significant_bits_of_rhs i Hrange Hops).
  pose(CommonModel.common_lt_order); simpl Z.shiftl in *.
  apply mod_move in Hdecomp; [| lia].
  rewrite Z.mod_small in Hdecomp.
  2: {
    pose(rhs_flag_bit_cell_bit i).
    pose(rhs_flag_u16_rem_cell_common i).
    lia.
  }
  rewrite Z.mod_small in Hdecomp.
  2: {
    pose(CommonModel.int_lt_order).
    destruct(rhs_u16_cells_U16) as [_ [H1 [_ H3]]].
    specialize (H1 i); specialize (H3 i).
    destruct (OpBinModel.is_i32_bit i) as [H | H]; rewrite H; lia.
  }
  replace(etable_values rhs_u16_cells_le_3 i + etable_values is_i32 i *
    (etable_values rhs_u16_cells_le_1 i - etable_values rhs_u16_cells_le_3 i)) with
    (etable_values rhs_flag_bit_cell i * 2^15 + etable_values rhs_flag_u16_rem_cell i) by lia.
  rewrite(Z.shiftr_div_pow2 _ _) by lia.
  rewrite(Z.div_add_l _ _ _) by lia.
  rewrite(Z.div_small _ _).
  lia.
  apply mod_move in Hflag_range; [| lia].
  pose(rhs_flag_u16_rem_cell_common i).
  pose(rhs_flag_u16_rem_diff_cell_common i).
  rewrite Z.mod_small in Hflag_range by lia.
  rewrite Z.mod_small in Hflag_range by lia.
  lia.
Qed.

Lemma normalized_is_abs : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values normalized_lhs i mod field_order = 
      abs (etable_values lhs_u64_cell i) (64 - (etable_values is_i32 i) * 32) /\
    etable_values normalized_rhs i mod field_order = 
      abs (etable_values rhs_u64_cell i) (64 - (etable_values is_i32 i) * 32).
Proof. 
  intros i Hrange Hops.
  pose(normalized_lhs_value i Hrange Hops).
  pose(normalized_rhs_value i Hrange Hops).
  pose(Hsize := size_modulus_value i Hrange Hops).
  pose(Hbit := OpBinModel.is_i32_bit i).
  pose(Hlflag := lhs_flag_bit_cell_is_most_significant_bit_of_lhs i Hrange Hops).
  pose(Hrflag := rhs_flag_bit_cell_is_most_significant_bit_of_rhs i Hrange Hops).
  unfold abs.
  pose(Hlflagbit := lhs_flag_bit_cell_bit i).
  pose(Hrflagbit := rhs_flag_bit_cell_bit i).
  replace(64 - etable_values is_i32 i * 32 - 1) with 
    (63 - etable_values is_i32 i * 32) by lia.
  rewrite <- Hlflag, <- Hrflag.
  rewrite <- Hsize.
  split.
  - destruct Hlflagbit as [H0 | H1].
    - rewrite H0 in *. 
      replace(0 =? 1) with false. lia.
      symmetry.
      apply Z.eqb_neq; lia.
    - rewrite H1 in *.
      rewrite Z.eqb_refl; lia.
  - destruct Hrflagbit as [H0 | H1].
    - rewrite H0 in *. 
      replace(0 =? 1) with false. lia.
      symmetry.
      apply Z.eqb_neq; lia.
    - rewrite H1 in *.
      rewrite Z.eqb_refl; lia.
Qed.
    
Lemma d_leading_u16_value : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_s_or_rem_s i = 1 ->
    (etable_values is_i32 i = 0 -> 
      etable_values d_leading_u16 i mod field_order = etable_values d_u16_cells_le_3 i) /\
    (etable_values is_i32 i = 1 -> 
      etable_values d_leading_u16 i mod field_order = etable_values d_u16_cells_le_1 i).
Proof.
  intros i Hrange Hops Hs.
  pose(H := bin_div_s_rem_s_constraints_common i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [_ [_ [H _]]]].
  rewrite Hops, Hs in H.
  rewrite Z.mul_1_l in H.
  pose(CommonModel.int_lt_order).
  apply mod_move in H; [| lia].
  symmetry in H.
  rewrite Z.mod_small in H.
  symmetry in H; lia.
  destruct(d_u16_cells_U16) as [_ [H1 [_ H3]]].
  specialize (H1 i); specialize (H3 i).
  pose(OpBinModel.is_i32_bit i).
  lia.
Qed.

Lemma d_leading_u16_range_when_res_flag_zero : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_s_or_rem_s i = 1 ->
    etable_values res_flag i = 0 ->
    0 <= etable_values d_leading_u16 i mod field_order < 2^15.
Proof.
  intros i Hrange Hops Hs Hres_flag.
  pose(H := bin_div_s_rem_s_constraints_common i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [_ [_ [_ [H _]]]]].
  rewrite Hres_flag in H.
  rewrite Z.opp_0 in H.
  rewrite Hops, Hs, Z.mul_1_l, Z.mul_1_r in H.
  pose(CommonModel.int_lt_order).
  apply mod_move in H; [| lia].
  rewrite <- Zplus_mod_idemp_l in H.
  pose(d_leading_u16_value i Hrange Hops Hs).
  pose(H16 := d_u16_cells_U16).
  destruct H16 as [_ [Hd1 [_ Hd3]]].
  specialize (Hd1 i); specialize (Hd3 i).
  pose(OpBinModel.is_i32_bit i).
  pose(d_flag_helper_diff_common i).
  rewrite Z.mod_small in H.
  rewrite(Z.mod_small 32767) in H by lia.
  lia.
  pose(CommonModel.common_lt_order); simpl Z.shiftl in *.
  lia.
Qed.

Lemma signed_aux1_range : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_s_or_rem_s i = 1 ->
    0 <= etable_values aux1 i < etable_values normalized_rhs i mod field_order.
Proof.
  intros i Hrange Hops Hs.
  pose(H := bin_div_s_rem_s_constraints_common i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [_ [_ [_ [_ [_ [H _]]]]]]].
  rewrite Hops, Hs, Z.mul_1_l in H.
  pose(CommonModel.int_lt_order).
  apply mod_move in H; [| lia].
  pose(aux1_U64 i).
  pose(aux2_U64 i).
  change Wasm_int.Int64.modulus with (2^64) in *.
  rewrite Z.mod_small in H by lia.
  lia.
Qed.

Lemma normalized_rhs_range : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    0 <= etable_values normalized_rhs i mod field_order <= 2^64.
Proof.
  intros i Hrange Hops.
  rewrite (proj2 (normalized_is_abs i Hrange Hops)).
  unfold abs.
  destruct (Z.shiftr (etable_values rhs_u64_cell i) 
    (64 - etable_values is_i32 i * 32 - 1) =? 1).
  - pose(rhs_range i Hrange Hops).
    destruct (OpBinModel.is_i32_bit i) as [H | H]; rewrite H in *; lia.
  - pose (rhs_le_int64 i Hrange Hops); lia.
Qed.
  
Lemma signed_normalized_lhs_decomp : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_s_or_rem_s i = 1 ->
    etable_values normalized_lhs i mod field_order =
    etable_values d_u64_cell i * (etable_values normalized_rhs i mod field_order) +
    etable_values aux1 i.
Proof.
  intros i Hrange Hops Hs.
  pose(H := bin_div_s_rem_s_constraints_common i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [_ [_ [_ [_ [H _]]]]]].
  rewrite Hops, Hs, Z.mul_1_l in H.
  rewrite <- Z.sub_add_distr in H.
  pose(CommonModel.int_lt_order).
  apply mod_move in H; [| lia].
  rewrite <- Zplus_mod_idemp_l in H.
  rewrite <- Zmult_mod_idemp_l in H.
  symmetry in H.
  rewrite Z.mod_small in H.
  2: {
    pose(normalized_rhs_range i Hrange Hops).
    pose(d_range i Hrange Hops).
    pose(aux1_U64 i).
    change Wasm_int.Int64.modulus with (2^64) in *.
    destruct a.
    destruct a0.
    pose proof (Zmult_le_compat_r _ _ _ H1 H2).
    assert(etable_values normalized_rhs i mod field_order * 
      etable_values d_u64_cell i < 2^64 * 2^64) by lia.
    rewrite Z.mod_small by lia.
    lia.
  }
  rewrite Z.mod_small in H; try lia.
  pose(normalized_rhs_range i Hrange Hops).
  pose(d_range i Hrange Hops).
  destruct a.
  destruct a0.
  pose proof (Zmult_le_compat_r _ _ _ H1 H2).
  lia.
Qed.

Lemma signed_normalized_lhs_div_unique : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_s_or_rem_s i = 1 ->
    Z.div_eucl (etable_values normalized_lhs i mod field_order) 
      (etable_values normalized_rhs i mod field_order) =
    (etable_values d_u64_cell i, etable_values aux1 i).
Proof.
  intros i Hrange Hops Hs.
  rewrite(Zaux.Zdiv_eucl_unique _ _).
  rewrite(signed_normalized_lhs_decomp i Hrange Hops Hs).
  pose(signed_aux1_range i Hrange Hops Hs).
  rewrite(Z.div_add_l _ _) by lia.
  rewrite(Z.div_small _ _) by assumption.
  rewrite(Z.add_comm _ (etable_values aux1 i)).
  rewrite(Z.mod_add _ _ _) by lia.
  rewrite(Z.mod_small _ _) by assumption.
  rewrite(Z.add_0_r _).
  reflexivity.
Qed.

Lemma div_s_degree_helper1_value : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_s i = 1 ->
    etable_values degree_helper1 i mod field_order =
    (etable_values res_flag i mod field_order) * 
    (etable_values d_u64_cell i + etable_values res i).
Proof.
  intros i Hrange Hops Hdivs.
  pose(H := bin_div_s_constraints_res i Hrange). 
  unfold ForallP in H.
  simpl value in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [H _]].
  rewrite Hops, Hdivs, Z.mul_1_l in H.
  pose(CommonModel.int_lt_order).
  apply mod_move in H; [| lia].
  rewrite H.
  rewrite Z.mul_comm.
  rewrite <- Zmult_mod_idemp_l.
  rewrite Z.mod_small; auto.
  rewrite res_flag_value; auto.
  pose(d_range i Hrange Hops).
  pose(res_le_int64 i Hrange Hops).
  pose(CommonModel.int_lt_order).
  destruct(lhs_flag_bit_cell_bit i) as [Hl | Hl]; rewrite Hl.
  - rewrite Z.lxor_0_l.
    pose(rhs_flag_bit_cell_bit i).
    lia.
  - destruct(rhs_flag_bit_cell_bit i) as [Hr | Hr]; rewrite Hr.
    - rewrite Z.lxor_0_r; lia.
    - rewrite Z.lxor_nilpotent; lia.
Qed.

Lemma signed_d_range : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values (is_div_s_or_rem_s) i = 1 ->
    0 <= etable_values d_u64_cell i < etable_values size_modulus i mod field_order.
Proof.
  intros i Hrange Hops Hs.
  rewrite size_modulus_value; auto.
  destruct (OpBinModel.is_i32_bit i) as [H0 | H1].
  - rewrite H0.
    pose(d_range i Hrange Hops).
    lia.
  - rewrite H1.
    replace (etable_values d_u64_cell i) with 
      (etable_values normalized_lhs i mod field_order / (etable_values normalized_rhs i mod field_order)).
    2 : {
      pose(Hdiv := signed_normalized_lhs_div_unique i Hrange Hops Hs).
      pose(Heucl := Zaux.Zdiv_eucl_unique (etable_values normalized_lhs i mod field_order) 
        (etable_values normalized_rhs i mod field_order)).
      rewrite Heucl in Hdiv.
      apply(pair_equal_spec _ _ _ _) in Hdiv.
      lia.
    }
    assert(Hlrange : 0 <= etable_values normalized_lhs i mod field_order < 2^32).
    - pose(Habs := normalized_is_abs i Hrange Hops).
      destruct Habs as [Hlabs _].
      rewrite Hlabs.
      unfold abs.
      replace (64 - etable_values is_i32 i * 32 - 1) with
        (63 - etable_values is_i32 i * 32) by lia.
      rewrite <- (lhs_flag_bit_cell_is_most_significant_bit_of_lhs i Hrange Hops).
      pose(Hflag := lhs_flag_bit_cell_bit i).
      destruct Hflag as [Hflag0 | Hflag1].
      - rewrite Hflag0.
        replace (0 =? 1) with false.
        pose(lhs_range i Hrange Hops).
        rewrite H1 in *.
        lia.
        symmetry.
        rewrite Z.eqb_neq; lia.
      - rewrite Hflag1.
        rewrite Z.eqb_refl.
        pose(lhs_range i Hrange Hops).
        assert(0 < etable_values lhs_u64_cell i).
        rewrite(lhs_flag_bit_cell_is_most_significant_bit_of_lhs i Hrange Hops) in Hflag1.
        rewrite H1 in Hflag1.
        rewrite(Z.shiftr_div_pow2 _ _) in Hflag1 by lia.
        change (63 - 1 * 32) with 31 in Hflag1.
        pose(Hldecomp := Z_div_mod (etable_values lhs_u64_cell i) (2^31)).
        rewrite(Zaux.Zdiv_eucl_unique _ _) in Hldecomp by lia.
        rewrite Hflag1 in Hldecomp.
        destruct Hldecomp; try lia.
        rewrite H1 in *.
        lia.
    assert(0 < etable_values normalized_rhs i mod field_order).
    - pose(signed_aux1_range i Hrange Hops Hs). lia.
    assert(0 <= etable_values normalized_lhs i mod field_order < 
      2^32 * (etable_values normalized_rhs i mod field_order)) by lia.
    destruct H0.
    apply(Zdiv_lt_upper_bound _ _ _ H) in H2.
    change (64 - 1 * 32) with 32.
    apply(Z_div_nonneg_nonneg _ 
      (etable_values normalized_rhs i mod field_order)) in H0; try lia.
Qed.
    
Lemma div_s_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_s i = 1 ->
    etable_values lhs_u64_cell i = l ->
    etable_values rhs_u64_cell i = r ->
    etable_values res i = div_s l r (64 - etable_values is_i32 i * 32).
Proof.
  intros i l r Hrange Hops Hdivs Hlhs Hrhs.
  destruct(bin_div_s_constraints_res i Hrange) as [Hunsigned Hgate]. 
  simpl in Hgate.
  simpl value in Hunsigned.
  replace(i+0) with i in * by lia.
  pose(CommonModel.int_lt_order).
  rewrite <- Hlhs, <- Hrhs.
  unfold div_s.
  replace(64 - etable_values is_i32 i * 32 - 1) with
    (63 - etable_values is_i32 i * 32) by lia.
  pose(Habs := normalized_is_abs i Hrange Hops).
  destruct Habs as [Habsl Habsr].
  rewrite <- Habsl, <- Habsr.
  rewrite <- (lhs_flag_bit_cell_is_most_significant_bit_of_lhs i Hrange Hops).
  rewrite <- (rhs_flag_bit_cell_is_most_significant_bit_of_rhs i Hrange Hops).
  rewrite <- (res_flag_value i Hrange Hops).
  rewrite <- size_modulus_value; auto.
  pose(is_div_s_or_rem_s_value i Hrange Hops).
  rewrite(signed_normalized_lhs_decomp i Hrange Hops) by lia.
  pose(signed_aux1_range i Hrange Hops).
  rewrite(Z.div_add_l _ _ _) by lia.
  rewrite(Z.div_small _ _) by lia.
  destruct(res_flag_bit i Hrange Hops) as [H0 | H1].
  - rewrite H0 in *.
    replace (0 =? 1) with false.
    rewrite Hops, Hdivs, Z.mul_1_l in Hunsigned.
    rewrite <- Zmult_mod_idemp_r in Hunsigned.
    rewrite <- Zminus_mod_idemp_r in Hunsigned.
    rewrite H0 in Hunsigned.
    rewrite Z.sub_0_r in Hunsigned.
    rewrite(Z.mod_small 1 _) in Hunsigned by lia.
    rewrite Z.mul_1_r in Hunsigned.
    apply mod_move in Hunsigned; [| lia].
    pose(res_le_int64 i Hrange Hops).
    rewrite Z.mod_small in Hunsigned by lia.
    pose(d_range i Hrange Hops).
    rewrite Z.mod_small in Hunsigned by lia; lia.
    symmetry.
    rewrite Z.eqb_neq; lia.
  - rewrite H1 in *.
    rewrite Z.eqb_refl.
    rewrite(Z.add_0_r _).
    destruct Hgate as [_ [Hgate _]].
    pose(Hdg := div_s_degree_helper1_value i Hrange Hops Hdivs).
    rewrite H1 in Hdg.
    rewrite(Z.mul_1_l _) in Hdg.
    pose(Hd := signed_d_range i Hrange Hops).
    pose(Hres := res_range i Hrange Hops).
    rewrite Hops, Hdivs, Z.mul_1_l in Hgate.
    rewrite <- Zmult_mod_idemp_r in Hgate.
    assert(0 <= etable_values degree_helper1 i mod field_order).
    - apply Z.mod_pos_bound; lia.
    assert(0 = etable_values degree_helper1 i mod field_order \/ 
      0 < etable_values degree_helper1 i mod field_order) by lia.
    destruct H0 as [Hdh | Hdh].
    - rewrite <- Hdh in *.
      replace(etable_values d_u64_cell i) with 0 by lia.
      rewrite(Z.sub_0_r _).
      rewrite(Z_mod_same_full _).
      lia.
    - assert(etable_values res i + etable_values d_u64_cell i 
        - etable_values size_modulus i mod field_order = 0).
      - apply Znumtheory.Zmod_divide in Hgate; [| lia].
        apply Znumtheory.prime_mult in Hgate; [| apply CommonModel.field_order_prime].
        destruct Hgate as [Hpdiv | Hcontra].
        - apply Znumtheory.Zdivide_mod in Hpdiv.
          apply mod_move in Hpdiv; [| lia].
          rewrite Z.mod_small in Hpdiv; [lia |].
          pose(res_le_int64 i Hrange Hops).
          pose(d_range i Hrange Hops).
          lia.
        - apply Znumtheory.Zdivide_mod in Hcontra.
          rewrite Zmod_mod in Hcontra.
          lia.
      replace(etable_values res i) with 
        (etable_values size_modulus i mod field_order - 
        etable_values d_u64_cell i) by lia.
      rewrite(Z.mod_small _ (etable_values size_modulus i mod field_order)); auto.
      lia.
Qed.

Lemma rem_s_degree_helper2_value : forall i,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_rem_s i = 1 ->
    etable_values degree_helper2 i mod field_order = 
    (etable_values lhs_flag_bit_cell i) * 
    (etable_values aux1 i + etable_values res i).
Proof.
  intros i Hrange Hops Hrems.
  pose(H := bin_rem_s_constraints_res i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [_ [H _]].
  rewrite Hops, Hrems, Z.mul_1_l in H.
  pose(CommonModel.int_lt_order).
  apply mod_move in H; [| lia].
  rewrite H.
  rewrite Z.mod_small; [lia |].
  pose(lhs_flag_bit_cell_bit i).
  pose(aux1_U64 i).
  pose(res_le_int64 i Hrange Hops).
  change Wasm_int.Int64.modulus with (2^64) in *.
  lia.
Qed.

Lemma rem_s_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_rem_s i = 1 ->
    etable_values lhs_u64_cell i = l ->
    etable_values rhs_u64_cell i = r ->
    etable_values res i = rem_s l r (64 - etable_values is_i32 i * 32).
Proof.
  intros i l r Hrange Hops Hrems Hlhs Hrhs.
  destruct(bin_rem_s_constraints_res i Hrange) as [Hunsigned Hgate]; simpl in Hgate.
  simpl value in Hunsigned.
  replace(i+0) with i in * by lia.
  pose(CommonModel.int_lt_order).
  rewrite <- Hlhs, <- Hrhs.
  unfold rem_s.
  replace(64 - etable_values is_i32 i * 32 - 1) with
    (63 - etable_values is_i32 i * 32) by lia.
  pose(Habs := normalized_is_abs i Hrange Hops).
  destruct Habs as [Habsl Habsr].
  rewrite <- Habsl, <- Habsr.
  rewrite <- (lhs_flag_bit_cell_is_most_significant_bit_of_lhs i Hrange Hops).
  rewrite <- size_modulus_value; auto.
  pose(is_div_s_or_rem_s_value i Hrange Hops).
  rewrite(signed_normalized_lhs_decomp i Hrange Hops) by lia.
  pose(signed_aux1_range i Hrange Hops).
  rewrite(Z.add_comm _ _).
  rewrite(Z.mod_add _ _ _) by lia.
  rewrite(Z.mod_small (etable_values aux1 i) _) by lia.
  destruct(lhs_flag_bit_cell_bit i) as [H0 | H1].
  - rewrite H0 in *.
    rewrite Z.eqb_refl.
    rewrite Hops, Hrems, Z.mul_1_l in Hunsigned.
    rewrite Z.sub_0_r, Z.mul_1_r in Hunsigned.
    apply mod_move in Hunsigned; [| lia].
    pose(res_le_int64 i Hrange Hops).
    rewrite Z.mod_small in Hunsigned by lia.
    pose(aux1_U64 i).
    change Wasm_int.Int64.modulus with (2^64) in *.
    rewrite Z.mod_small in Hunsigned by lia; auto.
  - rewrite H1 in *.
    replace (1 =? 0) with false.
    2: {
      symmetry.
      rewrite Z.eqb_neq; lia.
    }
    destruct Hgate as [_ [Hgate _]].
    pose(Hdg := rem_s_degree_helper2_value i Hrange Hops Hrems).
    rewrite H1 in Hdg.
    rewrite(Z.mul_1_l _) in Hdg.
    pose(Hres := res_range i Hrange Hops).
    assert(0 <= etable_values degree_helper2 i mod field_order).
    - apply Z.mod_pos_bound; lia.
    assert(0 = etable_values degree_helper2 i mod field_order \/ 
      0 < etable_values degree_helper2 i mod field_order) by lia.
    destruct H0 as [Hdh | Hdh].
    - rewrite Hdh in *.
      replace(etable_values aux1 i) with 0 by lia.
      rewrite(Z.sub_0_r _).
      rewrite(Z_mod_same_full _).
      lia.
    - assert(etable_values res i + etable_values aux1 i 
        - etable_values size_modulus i mod field_order = 0).
      - rewrite Hops, Hrems, Z.mul_1_l in Hgate.
        rewrite <- Zmult_mod_idemp_r in Hgate.
        apply Znumtheory.Zmod_divide in Hgate; [| lia].
        apply Znumtheory.prime_mult in Hgate; [| apply CommonModel.field_order_prime].
        destruct Hgate as [Hpdiv | Hcontra].
        - apply Znumtheory.Zdivide_mod in Hpdiv.
          apply mod_move in Hpdiv; [| lia].
          rewrite Z.mod_small in Hpdiv; [lia |].
          pose(res_le_int64 i Hrange Hops).
          pose(aux1_U64 i).
          change Wasm_int.Int64.modulus with (2^64) in *.
          lia.
        - apply Znumtheory.Zdivide_mod in Hcontra.
          rewrite Zmod_mod in Hcontra.
          lia.
      replace(etable_values res i) with 
        (etable_values size_modulus i mod field_order 
        - etable_values aux1 i) by lia.
      rewrite(Z.mod_small _ (etable_values size_modulus i mod field_order)) by lia; auto.
Qed.

Lemma bin_mops : forall i,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    etable_values (ops_cell Bin) i = 1 ->
    mops_at_correct i ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0.
Proof.
  intros i Hrange Hrow_enabled Hop_class Hops.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with Bin in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i Bin Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).

  assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  {
    apply (write_cell_with_value_mops _ _ _ _ _ _ stack_write i Hrange); auto.
    - apply (eid_common i).
    - apply (OpBinModel.is_i32_bit).
    - pose (sp_common i); lia.
  }
  lia.
Qed.

Theorem Bin_Add_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_add i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) ((xl + xr) mod 2^(64 - etable_values is_i32 i * 32):: xs)).
Proof.
  intros i st xl xr xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (bin_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hrhs: etable_values rhs_u64_cell i = xr).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get rhs_u64_cell)
                                 (enable := fun get => get (ops_cell Bin)).
    - apply Hrange.
    - apply Hop.
    - apply (OpBinModel.is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs_u64_cell i = xl).
  {
    eapply stack_rel_read_2_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get lhs_u64_cell)
                                 (enable := fun get => get (ops_cell Bin)).
    - apply Hrange.
    - apply Hop.
    - apply (OpBinModel.is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = (xl + xr) mod 2^(64 - etable_values is_i32 i * 32)).
  {
    apply (add_correct i _ _ Hrange Hop Hop_class Hlhs Hrhs).
  }
  rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hrhs Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Bin); auto.
    rewrite iid_change with (idx := Bin); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get is_i32)
                                (enable := fun get => get (ops_cell Bin)); auto; try lia.
  - apply (OpBinModel.is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i Bin); auto.
  - pose (mpages_change i Bin); simpl in *; lia.
  - rewrite (frame_id_change i Bin); auto; reflexivity.
  - rewrite (fid_change i Bin); auto.
  - apply stack_write.
Qed.

Theorem Bin_Sub_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_sub i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) ((xl - xr) mod 2^(64 - etable_values is_i32 i * 32):: xs)).
Proof.
  intros i st xl xr xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (bin_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hrhs: etable_values rhs_u64_cell i = xr).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get rhs_u64_cell)
                                 (enable := fun get => get (ops_cell Bin)).
    - apply Hrange.
    - apply Hop.
    - apply (OpBinModel.is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs_u64_cell i = xl).
  {
    eapply stack_rel_read_2_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get lhs_u64_cell)
                                 (enable := fun get => get (ops_cell Bin)).
    - apply Hrange.
    - apply Hop.
    - apply (OpBinModel.is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = (xl - xr) mod 2^(64 - etable_values is_i32 i * 32)).
  {
    apply (sub_correct i _ _ Hrange Hop Hop_class Hlhs Hrhs).
  }
  rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hrhs Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Bin); auto.
    rewrite iid_change with (idx := Bin); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get is_i32)
                                (enable := fun get => get (ops_cell Bin)); auto; try lia.
  - apply (OpBinModel.is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i Bin); auto.
  - pose (mpages_change i Bin); simpl in *; lia.        
  - rewrite (frame_id_change i Bin); auto; reflexivity.
  - rewrite (fid_change i Bin); auto.
  - apply stack_write.
Qed.

Theorem Bin_Mul_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_mul i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) ((xl * xr) mod 2^(64 - etable_values is_i32 i * 32):: xs)).
Proof.
  intros i st xl xr xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (bin_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hrhs: etable_values rhs_u64_cell i = xr).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get rhs_u64_cell)
                                 (enable := fun get => get (ops_cell Bin)).
    - apply Hrange.
    - apply Hop.
    - apply (OpBinModel.is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs_u64_cell i = xl).
  {
    eapply stack_rel_read_2_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get lhs_u64_cell)
                                 (enable := fun get => get (ops_cell Bin)).
    - apply Hrange.
    - apply Hop.
    - apply (OpBinModel.is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = (xl * xr) mod 2^(64 - etable_values is_i32 i * 32)).
  {
    apply (mul_correct i _ _ Hrange Hop Hop_class Hlhs Hrhs).
  }
  rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hrhs Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Bin); auto.
    rewrite iid_change with (idx := Bin); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get is_i32)
                                (enable := fun get => get (ops_cell Bin)); auto; try lia.
  - apply (OpBinModel.is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i Bin); auto.
  - pose (mpages_change i Bin); simpl in *; lia.        
  - rewrite (frame_id_change i Bin); auto; reflexivity.
  - rewrite (fid_change i Bin); auto.
  - apply stack_write.
Qed.

Theorem Bin_Div_U_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_u i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) ((xl / xr):: xs)).
Proof.
  intros i st xl xr xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (bin_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hrhs: etable_values rhs_u64_cell i = xr).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get rhs_u64_cell)
                                 (enable := fun get => get (ops_cell Bin)).
    - apply Hrange.
    - apply Hop.
    - apply (OpBinModel.is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs_u64_cell i = xl).
  {
    eapply stack_rel_read_2_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get lhs_u64_cell)
                                 (enable := fun get => get (ops_cell Bin)).
    - apply Hrange.
    - apply Hop.
    - apply (OpBinModel.is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = xl / xr).
  {
    apply (div_u_correct i _ _ Hrange Hop Hop_class Hlhs Hrhs).
  }
  rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hrhs Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Bin); auto.
    rewrite iid_change with (idx := Bin); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get is_i32)
                                (enable := fun get => get (ops_cell Bin)); auto; try lia.
  - apply (OpBinModel.is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i Bin); auto.
  - pose (mpages_change i Bin); simpl in *; lia.        
  - rewrite (frame_id_change i Bin); auto; reflexivity.
  - rewrite (fid_change i Bin); auto.
  - apply stack_write.
Qed.

Theorem Bin_Rem_U_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_rem_u i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) ((xl mod xr):: xs)).
Proof.
  intros i st xl xr xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (bin_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hrhs: etable_values rhs_u64_cell i = xr).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get rhs_u64_cell)
                                 (enable := fun get => get (ops_cell Bin)).
    - apply Hrange.
    - apply Hop.
    - apply (OpBinModel.is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs_u64_cell i = xl).
  {
    eapply stack_rel_read_2_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get lhs_u64_cell)
                                 (enable := fun get => get (ops_cell Bin)).
    - apply Hrange.
    - apply Hop.
    - apply (OpBinModel.is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = xl mod xr).
  {
    apply (rem_u_correct i _ _ Hrange Hop Hop_class Hlhs Hrhs).
  }
  rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hrhs Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Bin); auto.
    rewrite iid_change with (idx := Bin); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get is_i32)
                                (enable := fun get => get (ops_cell Bin)); auto; try lia.
  - apply (OpBinModel.is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i Bin); auto.
  - pose (mpages_change i Bin); simpl in *; lia.        
  - rewrite (frame_id_change i Bin); auto; reflexivity.
  - rewrite (fid_change i Bin); auto.
  - apply stack_write.
Qed.

Theorem Bin_Div_S_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_div_s i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) (div_s xl xr (64 - etable_values is_i32 i * 32):: xs)).
Proof.
  intros i st xl xr xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (bin_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hrhs: etable_values rhs_u64_cell i = xr).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get rhs_u64_cell)
                                 (enable := fun get => get (ops_cell Bin)).
    - apply Hrange.
    - apply Hop.
    - apply (OpBinModel.is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs_u64_cell i = xl).
  {
    eapply stack_rel_read_2_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get lhs_u64_cell)
                                 (enable := fun get => get (ops_cell Bin)).
    - apply Hrange.
    - apply Hop.
    - apply (OpBinModel.is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = div_s xl xr (64 - etable_values is_i32 i * 32)).
  {
    apply (div_s_correct i _ _ Hrange Hop Hop_class Hlhs Hrhs).
  }
  rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hrhs Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Bin); auto.
    rewrite iid_change with (idx := Bin); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get is_i32)
                                (enable := fun get => get (ops_cell Bin)); auto; try lia.
  - apply (OpBinModel.is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i Bin); auto.
  - pose (mpages_change i Bin); simpl in *; lia.        
  - rewrite (frame_id_change i Bin); auto; reflexivity.
  - rewrite (fid_change i Bin); auto.
  - apply stack_write.
Qed.

Theorem Bin_Rem_S_correct : forall i st xl xr xs,
    0 <= i ->
    (etable_values ETableModel.enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Bin) i = 1 ->
    etable_values is_rem_s i = 1 ->
    state_rel i st ->
    wasm_stack st = xr::xl::xs ->
    state_rel (i+1) (update_stack (incr_iid st) (rem_s xl xr (64 - etable_values is_i32 i * 32):: xs)).
Proof.
  intros i st xl xr xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (bin_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hrhs: etable_values rhs_u64_cell i = xr).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get rhs_u64_cell)
                                 (enable := fun get => get (ops_cell Bin)).
    - apply Hrange.
    - apply Hop.
    - apply (OpBinModel.is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs_u64_cell i = xl).
  {
    eapply stack_rel_read_2_without_value with (is_i32 := fun get => get is_i32)
                                 (value := fun get => get lhs_u64_cell)
                                 (enable := fun get => get (ops_cell Bin)).
    - apply Hrange.
    - apply Hop.
    - apply (OpBinModel.is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = rem_s xl xr (64 - etable_values is_i32 i * 32)).
  {
    apply (rem_s_correct i _ _ Hrange Hop Hop_class Hlhs Hrhs).
  }
  rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hrhs Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Bin); auto.
    rewrite iid_change with (idx := Bin); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.
    
  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get is_i32)
                                (enable := fun get => get (ops_cell Bin)); auto; try lia.
  - apply (OpBinModel.is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i Bin); auto.
  - pose (mpages_change i Bin); simpl in *; lia.        
  - rewrite (frame_id_change i Bin); auto; reflexivity.
  - rewrite (fid_change i Bin); auto.
  - apply stack_write.
Qed.
