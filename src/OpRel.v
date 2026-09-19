(* Copyright (C) CertiK 2024-2026 *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETable.
Require Import MTable.

Require Import OpRelModel.

(* Proofs about op_rel.rs. *)

Require Import Wasm.numerics.
Require Import Lia.
Require Import MTable.
Require Import Bool.

Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_rel : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Rel i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config Rel i)) with 1.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  - apply MTable.mtable_write_mops with
      (offset := etable_values sp_cell i + 2)
      (is_i32 := etable_values is_i32_cell i)
      (value := etable_values res i); auto.
    apply (alloc_memory_table_lookup_write_cell_with_value_correct _ _ _ _ _ _ 
      stack_write i Hrange); auto.
    - apply eid_common.
    - apply is_i32_bit.
    - pose(sp_common i); lia.
  lia.
Qed.

Lemma unique_rel_op_type: forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
        (etable_values op_is_eq_cell i = 1 /\  etable_values op_is_ne_cell i = 0 /\ etable_values op_is_lt_cell i = 0 /\ etable_values op_is_gt_cell i = 0 /\ etable_values op_is_le_cell i = 0 /\ etable_values op_is_ge_cell i = 0) 
    \/  (etable_values op_is_eq_cell i = 0 /\  etable_values op_is_ne_cell i = 1 /\ etable_values op_is_lt_cell i = 0 /\ etable_values op_is_gt_cell i = 0 /\ etable_values op_is_le_cell i = 0 /\ etable_values op_is_ge_cell i = 0) 
    \/  (etable_values op_is_eq_cell i = 0 /\  etable_values op_is_ne_cell i = 0 /\ etable_values op_is_lt_cell i = 1 /\ etable_values op_is_gt_cell i = 0 /\ etable_values op_is_le_cell i = 0 /\ etable_values op_is_ge_cell i = 0) 
    \/  (etable_values op_is_eq_cell i = 0 /\  etable_values op_is_ne_cell i = 0 /\ etable_values op_is_lt_cell i = 0 /\ etable_values op_is_gt_cell i = 1 /\ etable_values op_is_le_cell i = 0 /\ etable_values op_is_ge_cell i = 0) 
    \/  (etable_values op_is_eq_cell i = 0 /\  etable_values op_is_ne_cell i = 0 /\ etable_values op_is_lt_cell i = 0 /\ etable_values op_is_gt_cell i = 0 /\ etable_values op_is_le_cell i = 1 /\ etable_values op_is_ge_cell i = 0) 
    \/  (etable_values op_is_eq_cell i = 0 /\  etable_values op_is_ne_cell i = 0 /\ etable_values op_is_lt_cell i = 0 /\ etable_values op_is_gt_cell i = 0 /\ etable_values op_is_le_cell i = 0 /\ etable_values op_is_ge_cell i = 1).   
Proof.
    intros i Hrange Hops.
    pose(H := rel_selector i Hrange).
    simpl in H.  

    replace (i+0) with i in * by lia.
    pose(Heq := op_is_eq_bit i).
    pose(Hne := op_is_ne_bit i).
    pose(Hlt := op_is_lt_bit i).
    pose(Hgt := op_is_gt_bit i).
    pose(Hle := op_is_le_bit i).  (* destruct the last two to prevent stack overflow *)
    pose(Hge := op_is_ge_bit i).
    destruct Hge as [Hge0 | Hge1].
    - rewrite Hge0 in *.
        simpl.
        destruct Hle as [Hle0 | Hle1].
        - rewrite Hle0 in *.
            simpl.
            lia.
        - rewrite Hle1 in *.
            simpl.
            lia.
    - rewrite Hge1 in *.
        simpl.
        destruct Hle as [Hle0 | Hle1].
        - rewrite Hle0 in *.
            simpl.
            lia.
        - rewrite Hle1 in *.
            simpl.
            lia.
Qed.

Require Import ImageTableModel.
Require Import InjectivityHelper.

Definition Rel_op i :=
  if (Z.eq_dec (etable_values op_is_eq_cell i) 1) then EQ
  else if (Z.eq_dec (etable_values op_is_ne_cell i) 1) then NEQ
  else if (Z.eq_dec (etable_values op_is_gt_cell i) 1) then
     (if (Z.eq_dec (etable_values is_sign_cell i) 1) then GT_s else GT_u)
  else if (Z.eq_dec (etable_values op_is_ge_cell i) 1) then
     (if (Z.eq_dec (etable_values is_sign_cell i) 1) then GE_s else GE_u)
  else if (Z.eq_dec (etable_values op_is_lt_cell i) 1) then
     (if (Z.eq_dec (etable_values is_sign_cell i) 1) then LT_s else LT_u)
  else      
     (if (Z.eq_dec (etable_values is_sign_cell i) 1) then LE_s else LE_u).

Lemma Rel_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values ETableModel.enabled_cell i = 1 ->    
  etable_values (ops_cell Rel) i = 1 ->
  exists op,
    op = Rel_op i
    /\ program (wasm_pc st) = IRel (bool_of_Z (etable_values is_i32_cell i)) op
    /\ match op with
       | EQ    => etable_values op_is_eq_cell i = 1
       | NEQ   => etable_values op_is_ne_cell i = 1
       | GT_s  => etable_values op_is_gt_cell i = 1 /\ etable_values is_sign_cell i = 1
       | GT_u  => etable_values op_is_gt_cell i = 1 /\ etable_values is_sign_cell i = 0
       | GE_s  => etable_values op_is_ge_cell i = 1 /\ etable_values is_sign_cell i = 1
       | GE_u  => etable_values op_is_ge_cell i = 1 /\ etable_values is_sign_cell i = 0
       | LT_s  => etable_values op_is_lt_cell i = 1 /\ etable_values is_sign_cell i = 1
       | LT_u  => etable_values op_is_lt_cell i = 1 /\ etable_values is_sign_cell i = 0
       | LE_s  => etable_values op_is_le_cell i = 1 /\ etable_values is_sign_cell i = 1
       | LE_u  => etable_values op_is_le_cell i = 1 /\ etable_values is_sign_cell i = 0 end.
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i Rel Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  destruct (unique_rel_op_type i Hrange Hops) as [Hsel | [Hsel | [Hsel | [Hsel | [Hsel | Hsel]]]]].
  - exists EQ.
    split. {
      unfold Rel_op.
      destruct Hsel as [H1 _].
      rewrite H1. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpRelModel.is_i32_bit. }
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 Hsel6]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    reflexivity.
  - exists NEQ.
    split. {
      unfold Rel_op.
      destruct Hsel as [H1 [H2 _]].
      rewrite H1, H2. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpRelModel.is_i32_bit. }
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 Hsel6]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    reflexivity.
 - destruct (is_sign_bit i) as [Hsign | Hsign].
  + exists LT_u.
    split. {
      unfold Rel_op.
      destruct Hsel as [H1 [H2 [H3 [H4 [H5 H6]]]]].
      rewrite H1, H2, H4, H3, H6, Hsign. simpl.
      reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpRelModel.is_i32_bit. }
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 Hsel6]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsign.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    reflexivity.
  + exists LT_s.
    split. {
      unfold Rel_op.
      destruct Hsel as [H1 [H2 [H3 [H4 [H5 H6]]]]].
      rewrite H1, H2, H4, H3, H6, Hsign. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpRelModel.is_i32_bit. }
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 Hsel6]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsign.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    reflexivity.
 - destruct (is_sign_bit i) as [Hsign | Hsign].
  + exists GT_u.
    split. {
      unfold Rel_op.
      destruct Hsel as [H1 [H2 [H3 [H4 [H5 H6]]]]].
      rewrite H1, H2, H4, H6, Hsign. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpRelModel.is_i32_bit. }
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 Hsel6]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsign.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    reflexivity.
  + exists GT_s.
    split. {
      unfold Rel_op.
      destruct Hsel as [H1 [H2 [H3 [H4 [H5 H6]]]]].
      rewrite H1, H2, H4, H6, Hsign. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpRelModel.is_i32_bit. }
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 Hsel6]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsign.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    reflexivity.
 - destruct (is_sign_bit i) as [Hsign | Hsign].
  + exists LE_u.
    split. {
      unfold Rel_op.
      destruct Hsel as [H1 [H2 [H3 [H4 [H5 H6]]]]].
      rewrite H1, H2, H4, H3, H6, Hsign. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpRelModel.is_i32_bit. }
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 Hsel6]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsign.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    reflexivity.
  + exists LE_s.
    split. {
      unfold Rel_op.
      destruct Hsel as [H1 [H2 [H3 [H4 [H5 H6]]]]].
      rewrite H1, H2, H4, H3, H6, Hsign. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpRelModel.is_i32_bit. }
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 Hsel6]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsign.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    reflexivity.
 - destruct (is_sign_bit i) as [Hsign | Hsign].
  + exists GE_u.
    split. {
      unfold Rel_op.
      destruct Hsel as [H1 [H2 [H3 [H4 [H5 H6]]]]].
      rewrite H1, H2, H4, H6, Hsign. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpRelModel.is_i32_bit. }
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 Hsel6]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsign.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    reflexivity.
  + exists GE_s.
    split. {
      unfold Rel_op.
      destruct Hsel as [H1 [H2 [H3 [H4 [H5 H6]]]]].
      rewrite H1, H2, H4, H6, Hsign. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpRelModel.is_i32_bit. }
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 Hsel6]]]]].
    rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsign.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    reflexivity.
Qed.

Lemma eq_or_lt_or_gt: forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
        (etable_values res_is_eq_cell i = 1 /\ etable_values res_is_lt_cell i = 0 /\ etable_values res_is_gt_cell i = 0) 
    \/  (etable_values res_is_eq_cell i = 0 /\ etable_values res_is_lt_cell i = 1 /\ etable_values res_is_gt_cell i = 0) 
    \/  (etable_values res_is_eq_cell i = 0 /\ etable_values res_is_lt_cell i = 0 /\ etable_values res_is_gt_cell i = 1).
Proof.
    intros i Hrange Hops.
    pose(H := rel_compare_diff i Hrange).
    destruct H as [ _[ H _]].
    simpl in H.  
    replace (i+0) with i in * by lia.
    pose(res_is_eq_bit i).
    pose(res_is_lt_bit i).
    pose(res_is_gt_bit i).
    lia.
Qed.

  Lemma diff_u64_zero_or_positive : forall i,
  0 <= i ->
  etable_values (ops_cell Rel) i = 1 ->
  etable_values diff_u64_cell i = 0 \/ etable_values diff_u64_cell i > 0.
Proof.
  intros i Hrange Hops.
  pose(Hd := diff_is_u64 i);  simpl in Hd.
  simpl in Hd.
  lia.
Qed.


Lemma diff_u64_zero_or_nonzero : forall i,
  0 <= i ->
  etable_values (ops_cell Rel) i = 1 ->
  etable_values diff_u64_cell i = 0 \/ etable_values diff_u64_cell i <> 0.
Proof.
  intros i Hrange Hops.
  pose(Hd := diff_is_u64 i);  simpl in Hd.
  simpl in Hd.
  lia.
Qed.


Lemma relop_mops : forall i,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    etable_values (ops_cell Rel) i = 1 ->
    mops_at_correct i ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
    intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
    unfold mops_at_correct in Hops.
    replace (class_of_row i) with Rel in Hops.
    2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i Rel Hrow_enabled)); auto.
    }
    simpl in Hops.
    pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
    pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).

    assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
    {
    apply (write_cell_with_value_mops _ _ _ _ _ _ stack_write i Hrange); auto.
    - apply (eid_common i).
    - apply (is_i32_bit).
    - pose (sp_common i).
    - pose (sp_common i); lia.
    }
    lia.
Qed.


Lemma l_pos_r_pos_value : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values l_pos_r_pos_cell i = 
    (1 - etable_values lhs_flag_bit_cell i) * (1 - etable_values rhs_flag_bit_cell i).
Proof.
  intros i Hrange Hops.
  pose(H := rel_compare_op_res i Hrange).
  destruct H as [H _].
  simpl value in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.


Lemma l_pos_r_neg_value : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values l_pos_r_neg_cell i = 
    (1 - etable_values lhs_flag_bit_cell i) * (etable_values rhs_flag_bit_cell i).
Proof.
  intros i Hrange Hops.
  pose(H := rel_compare_op_res i Hrange).
  destruct H as [_ [H _]].
  simpl value in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.


Lemma l_neg_r_pos_value : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values l_neg_r_pos_cell i = 
    (etable_values lhs_flag_bit_cell i) * (1 - etable_values rhs_flag_bit_cell i).
Proof.
  intros i Hrange Hops.
  pose(H := rel_compare_op_res i Hrange).
  destruct H as [_ [_ [H _]]].
  simpl value in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.


Lemma l_neg_r_neg_value : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values l_neg_r_neg_cell i = 
    (etable_values lhs_flag_bit_cell i) * (etable_values rhs_flag_bit_cell i).
Proof.
  intros i Hrange Hops.
  pose(H := rel_compare_op_res i Hrange).
  destruct H as [_ [_ [_  [H _]]]].
  simpl value in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.


Lemma eq_res_value : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_eq_cell i = 1 ->
    etable_values res i = etable_values res_is_eq_cell i.
Proof.
  intros i Hrange Hops Heq.
  pose(H := rel_compare_op_res i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.


Lemma ne_res_value : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ne_cell i = 1 ->
    etable_values res i = 1 - etable_values res_is_eq_cell i.
Proof.
  intros i Hrange Hops Hne.
  pose(H := rel_compare_op_res i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.


Lemma lt_res_value : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_lt_cell i = 1 ->
    etable_values res i = etable_values l_neg_r_pos_cell i +
    etable_values l_pos_r_pos_cell i * etable_values res_is_lt_cell i +
    etable_values l_neg_r_neg_cell i * etable_values res_is_lt_cell i.
Proof.
  intros i Hrange Hops Hlt.
  pose(H := rel_compare_op_res i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.


Lemma le_res_value : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_le_cell i = 1 ->
    etable_values res i = etable_values l_neg_r_pos_cell i +
    etable_values l_pos_r_pos_cell i * etable_values res_is_lt_cell i +
    etable_values l_neg_r_neg_cell i * etable_values res_is_lt_cell i + etable_values res_is_eq_cell i.
Proof.
  intros i Hrange Hops Hle.
  pose(H := rel_compare_op_res i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.


Lemma gt_res_value : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_gt_cell i = 1 ->
    etable_values res i = etable_values l_pos_r_neg_cell i +
    etable_values l_pos_r_pos_cell i * etable_values res_is_gt_cell i +
    etable_values l_neg_r_neg_cell i * etable_values res_is_gt_cell i.
Proof.
  intros i Hrange Hops Hgt.
  pose(H := rel_compare_op_res i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.


Lemma ge_res_value : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ge_cell i = 1 ->
    etable_values res i = etable_values l_pos_r_neg_cell i +
    etable_values l_pos_r_pos_cell i * etable_values res_is_gt_cell i +
    etable_values l_neg_r_neg_cell i * etable_values res_is_gt_cell i + etable_values res_is_eq_cell i.
Proof.
  intros i Hrange Hops Hgt.
  pose(H := rel_compare_op_res i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.


Lemma unsigned_means_flags_zero : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values lhs_flag_bit_cell i = 0 /\
    etable_values rhs_flag_bit_cell i = 0.
Proof.
  intros i Hrange Hops Hsign.
  split.
  - pose(H := lhs_u64_flag_bit_dyn_sign i Hrange); simpl in H.
    replace(i+0) with i in * by lia.
    lia.
  - pose(H := rhs_u64_flag_bit_dyn_sign i Hrange); simpl in H.
    replace(i+0) with i in * by lia.
    lia.
Qed.


Lemma res_is_eq_criteria : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values lhs_u64_cell i = etable_values rhs_u64_cell i ->
    etable_values res_is_eq_cell i = 1.
Proof.
  intros i Hrange Hops Heq.
  pose(H := rel_compare_diff i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  pose(diff_is_u64 i).
  destruct(eq_or_lt_or_gt i Hrange Hops) as [? | [? | Hgt]]; lia.
Qed.


Lemma res_is_ne_criteria : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values lhs_u64_cell i <> etable_values rhs_u64_cell i ->
    etable_values res_is_eq_cell i = 0.
Proof.
  intros i Hrange Hops Heq.
  pose(H := rel_compare_diff i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  pose(diff_is_u64 i).
  destruct(eq_or_lt_or_gt i Hrange Hops) as [? | [? | Hgt]]; lia.
Qed.


Lemma res_is_lt_criteria : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values lhs_u64_cell i < etable_values rhs_u64_cell i ->
    etable_values res_is_lt_cell i = 1.
Proof.
  intros i Hrange Hops Hne.
  pose(H := rel_compare_diff i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  pose(diff_is_u64 i).
  destruct(eq_or_lt_or_gt i Hrange Hops) as [? | [? | Hgt]]; lia.
Qed.


Lemma res_is_le_criteria : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values lhs_u64_cell i <= etable_values rhs_u64_cell i ->
    etable_values res_is_lt_cell i = 1 \/ etable_values res_is_eq_cell i = 1.
Proof.
  intros i Hrange Hops Hne.
  pose(H := rel_compare_diff i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  pose(diff_is_u64 i).
  apply(Zle_lt_or_eq) in Hne.
  destruct(eq_or_lt_or_gt i Hrange Hops) as [? | [? | Hgt]]; lia.
Qed.


Lemma res_is_gt_criteria : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values lhs_u64_cell i > etable_values rhs_u64_cell i ->
    etable_values res_is_gt_cell i = 1.
Proof.
  intros i Hrange Hops Hne.
  pose(H := rel_compare_diff i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  pose(diff_is_u64 i).
  destruct(eq_or_lt_or_gt i Hrange Hops) as [? | [? | Hgt]]; lia.
Qed.


Lemma res_is_ge_criteria : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values lhs_u64_cell i >= etable_values rhs_u64_cell i ->
    etable_values res_is_gt_cell i = 1 \/ etable_values res_is_eq_cell i = 1.
Proof.
    intros i Hrange Hops Hne.
    pose(H := rel_compare_diff i Hrange); simpl in H.
    replace(i+0) with i in * by lia.
    pose(diff_is_u64 i).
    apply(Z.ge_le_iff) in Hne.
    apply(Zle_lt_or_eq) in Hne.
    destruct(eq_or_lt_or_gt i Hrange Hops) as [? | [? | Hgt]]; lia.
Qed.


Lemma gte_decomp : forall a b,
    a >= b ->
    a = b \/ a > b.
Proof.
  lia.
Qed.


Lemma lte_decomp : forall a b,
    a <= b ->
    a = b \/ a < b.
Proof.
  lia.
Qed.


Lemma rhs_is_bit_32 : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_i32_cell i = 1 ->
    0 <= etable_values rhs_u64_cell i < 2^32.
Proof.
  intros i Hrange Hops Hi32.
  assert(0 <= etable_values rhs_u64_cell i < 2^(64 - (etable_values is_i32_cell i) * 32)).
  - eapply read_range with (is_i32 := fun get => get is_i32_cell)
                           (loctyp := MTableModel.LocationType_Stack)
                           (sp := fun get => get sp_cell + 1)
                           (value := fun get => get rhs_u64_cell)
                           (enable := fun get => get (ops_cell Rel)); auto.
    pose (sp_common i); lia.
    apply stack_read_rhs.
  rewrite Hi32 in H.
  lia.
Qed.


Lemma lhs_is_bit_32 : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_i32_cell i = 1 ->
    0 <= etable_values lhs_u64_cell i < 2^32.
Proof.
  intros i Hrange Hops Hi32.
  assert(0 <= etable_values lhs_u64_cell i < 2^(64 - (etable_values is_i32_cell i) * 32)).
  - eapply read_range with (is_i32 := fun get => get is_i32_cell)
                           (loctyp := MTableModel.LocationType_Stack)                           
                           (sp := fun get => get sp_cell + 2)
                           (value := fun get => get lhs_u64_cell)
                           (enable := fun get => get (ops_cell Rel)); auto.
    pose (sp_common i); lia.
    apply stack_read_lhs.
  rewrite Hi32 in H.
  lia.
Qed.


Lemma sixteen_most_significant_bits_of_lhs : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values lhs_u16_cells_le3 i + etable_values is_i32_cell i
    * (etable_values lhs_u16_cells_le1 i - etable_values lhs_u16_cells_le3 i)
    = Z.shiftr (etable_values lhs_u64_cell i) (48 - etable_values is_i32_cell i * 32).
Proof.
  intros i Hrange Hops.
  pose(Hlhs := lhs_u64 i).
  pose(H0 := lhs_u16_cells_le0_u16 i).
  pose(H1 := lhs_u16_cells_le1_u16 i).
  pose(H2 := lhs_u16_cells_le2_u16 i).
  pose(H3 := lhs_u16_cells_le3_u16 i).
  rewrite Hlhs.
  pose(H := is_i32_bit i).
  rewrite Z.shiftr_div_pow2 by lia.
  destruct H as [Hbit0 | Hbit1].
  - rewrite Hbit0; simpl.
    rewrite Z.div_add by lia.
    rewrite Z.div_small by lia.
    lia.
  - rewrite Hbit1.
    replace(etable_values lhs_u16_cells_le3 i + 1 *
      (etable_values lhs_u16_cells_le1 i - etable_values lhs_u16_cells_le3 i)) with
      (etable_values lhs_u16_cells_le1 i) by lia.
    simpl.
    replace(etable_values lhs_u16_cells_le0 i +
      etable_values lhs_u16_cells_le1 i * Z.pow_pos 2 16 +
      etable_values lhs_u16_cells_le2 i * Z.pow_pos 2 32 +
      etable_values lhs_u16_cells_le3 i * Z.pow_pos 2 48) with
      (etable_values lhs_u16_cells_le0 i +
      (etable_values lhs_u16_cells_le1 i +
      etable_values lhs_u16_cells_le2 i * Z.pow_pos 2 16 +
      etable_values lhs_u16_cells_le3 i * Z.pow_pos 2 32) * Z.pow_pos 2 16) by lia.
    rewrite Z.div_add by lia.
    rewrite Z.div_small by apply H0.
    pose(lhs_is_bit_32 i Hrange Hops Hbit1).
    assert(etable_values lhs_u16_cells_le2 i = 0 /\ etable_values lhs_u16_cells_le3 i = 0).
    - lia.
    lia.
Qed.


Lemma lhs_flag_bit_cell_is_most_significant_bit_of_lhs : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values lhs_flag_bit_cell i =
    Z.shiftr (etable_values lhs_u64_cell i) (63 - (etable_values is_i32_cell i) * 32).
Proof.
  intros i Hrange Hops Hsign.
  pose(H := lhs_u64_flag_bit_dyn_sign i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [Hdecomp [Hflag_range _]].
  replace(63 - etable_values is_i32_cell i * 32) with
    (48 - etable_values is_i32_cell i * 32 + 15) by lia.
  rewrite <- Z.shiftr_shiftr by lia.
  rewrite <- sixteen_most_significant_bits_of_lhs; auto.
  replace(etable_values lhs_u16_cells_le3 i + etable_values is_i32_cell i *
    (etable_values lhs_u16_cells_le1 i - etable_values lhs_u16_cells_le3 i)) with
    (etable_values lhs_flag_bit_cell i * 2^15 + etable_values lhs_flag_rem_cell i) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small.
  lia.
  pose(lhs_flag_rem_common i).
  pose(lhs_flag_rem_diff_common i).
  lia.
Qed.


Lemma sixteen_most_significant_bits_of_rhs : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values rhs_u16_cells_le3 i + etable_values is_i32_cell i
    * (etable_values rhs_u16_cells_le1 i - etable_values rhs_u16_cells_le3 i)
    = Z.shiftr (etable_values rhs_u64_cell i) (48 - etable_values is_i32_cell i * 32).
Proof.
  intros i Hrange Hops.
  pose(Hrhs := rhs_u64 i).
  pose(H0 := rhs_u16_cells_le0_u16 i).
  pose(H1 := rhs_u16_cells_le1_u16 i).
  pose(H2 := rhs_u16_cells_le2_u16 i).
  pose(H3 := rhs_u16_cells_le3_u16 i).
  rewrite Hrhs.
  pose(H := is_i32_bit i).
  rewrite Z.shiftr_div_pow2 by lia.
  destruct H as [Hbit0 | Hbit1].
  - rewrite Hbit0; simpl.
    rewrite Z.div_add by lia.
    rewrite Z.div_small by lia.
    lia.
  - rewrite Hbit1.
    replace(etable_values rhs_u16_cells_le3 i + 1 *
      (etable_values rhs_u16_cells_le1 i - etable_values rhs_u16_cells_le3 i)) with
      (etable_values rhs_u16_cells_le1 i) by lia.
    simpl.
    replace(etable_values rhs_u16_cells_le0 i +
      etable_values rhs_u16_cells_le1 i * Z.pow_pos 2 16 +
      etable_values rhs_u16_cells_le2 i * Z.pow_pos 2 32 +
      etable_values rhs_u16_cells_le3 i * Z.pow_pos 2 48) with
      (etable_values rhs_u16_cells_le0 i +
      (etable_values rhs_u16_cells_le1 i +
      etable_values rhs_u16_cells_le2 i * Z.pow_pos 2 16 +
      etable_values rhs_u16_cells_le3 i * Z.pow_pos 2 32) * Z.pow_pos 2 16) by lia.
    rewrite Z.div_add by lia.
    rewrite Z.div_small by apply H0.
    pose(rhs_is_bit_32 i Hrange Hops Hbit1).
    assert(etable_values rhs_u16_cells_le2 i = 0 /\ etable_values rhs_u16_cells_le3 i = 0).
    - lia.
    lia.
Qed.


Lemma rhs_flag_bit_cell_is_most_significant_bit_of_rhs : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values rhs_flag_bit_cell i =
    Z.shiftr (etable_values rhs_u64_cell i) (63 - (etable_values is_i32_cell i) * 32).
Proof.
  intros i Hrange Hops Hsign.
  pose(H := rhs_u64_flag_bit_dyn_sign i Hrange); simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [Hdecomp [Hflag_range _]].
  replace(63 - etable_values is_i32_cell i * 32) with
    (48 - etable_values is_i32_cell i * 32 + 15) by lia.
  rewrite <- Z.shiftr_shiftr by lia.
  rewrite <- sixteen_most_significant_bits_of_rhs; auto.
  replace(etable_values rhs_u16_cells_le3 i + etable_values is_i32_cell i *
    (etable_values rhs_u16_cells_le1 i - etable_values rhs_u16_cells_le3 i)) with
    (etable_values rhs_flag_bit_cell i * 2^15 + etable_values rhs_flag_rem_cell i) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small.
  lia.
  pose(rhs_flag_rem_common i).
  pose(rhs_flag_rem_diff_common i).
  lia.
Qed.


Lemma lhs_range : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    0 <= etable_values lhs_u64_cell i < 2^(64 - (etable_values is_i32_cell i) * 32).
Proof.
  intros i Hrange Hops.
  eapply read_range with (is_i32 := fun get => get is_i32_cell)
                         (loctyp := MTableModel.LocationType_Stack)
                         (sp := fun get => get sp_cell + 2)
                         (value := fun get => get lhs_u64_cell)
                         (enable := fun get => get (ops_cell Rel)); auto.
    - pose (sp_common i); lia.
    - apply (is_i32_bit i).
    - apply stack_read_lhs.
Qed.


Lemma rhs_range : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    0 <= etable_values rhs_u64_cell i < 2^(64 - (etable_values is_i32_cell i) * 32).
Proof.
  intros i Hrange Hops.
  eapply read_range with (is_i32 := fun get => get is_i32_cell)
                          (loctyp := MTableModel.LocationType_Stack)
                         (sp := fun get => get sp_cell + 1)
                         (value := fun get => get rhs_u64_cell)
                         (enable := fun get => get (ops_cell Rel)); auto.
    - pose (sp_common i); lia.
    - apply (is_i32_bit i).
    - apply stack_read_rhs.
Qed.


Lemma shiftr_eq_0 : forall a n,
  0 <= a ->
  0 <= n ->
  Z.shiftr a n = 0 <->
  a < 2^n.
Proof.
  intros.
  rewrite Z.shiftr_div_pow2; auto.
  rewrite Z.div_small_iff by lia.
  lia.
Qed.


Lemma lhs_flag_bit_pos_iff_64 : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_i32_cell i = 0 ->
    etable_values is_sign_cell i = 1 ->
    etable_values lhs_flag_bit_cell i = 0 <->
    etable_values lhs_u64_cell i < Wasm_int.Int64.half_modulus.
Proof.
  intros i Hrange Hops Hi32 Hsign.
  change Wasm_int.Int64.half_modulus with (2^63).
  rewrite lhs_flag_bit_cell_is_most_significant_bit_of_lhs; auto.
  rewrite Hi32.
  rewrite shiftr_eq_0; try lia.
  apply lhs_range; auto.
Qed.


Lemma rhs_flag_bit_pos_iff_64 : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_i32_cell i = 0 ->
    etable_values is_sign_cell i = 1 ->
    etable_values rhs_flag_bit_cell i = 0 <->
    etable_values rhs_u64_cell i < Wasm_int.Int64.half_modulus.
Proof.
  intros i Hrange Hops Hi32 Hsign.
  change Wasm_int.Int64.half_modulus with (2^63).
  rewrite rhs_flag_bit_cell_is_most_significant_bit_of_rhs; auto.
  rewrite Hi32.
  rewrite shiftr_eq_0; try lia.
  apply rhs_range; auto.
Qed.


Lemma div_ineq : forall a b c,
    b > 0 ->
    a / b = c ->
    a >= b * c.
Proof.
  intros.
  apply (f_equal (fun t => t * b)) in H0.
  assert(b * (a / b)  <= a).
  - apply Z.mul_div_le; lia.
  lia.
Qed.


Lemma lhs_flag_bit_neg_iff_64 : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_i32_cell i = 0 ->
    etable_values is_sign_cell i = 1 ->
    etable_values lhs_flag_bit_cell i = 1 <->
    etable_values lhs_u64_cell i >= Wasm_int.Int64.half_modulus.
Proof.
  intros i Hrange Hops Hi32 Hsign.
  change Wasm_int.Int64.half_modulus with (2^63).
  rewrite lhs_flag_bit_cell_is_most_significant_bit_of_lhs; auto.
  pose(Hlr := lhs_range i Hrange Hops).
  rewrite Hi32 in *.
  change (63 - 0 * 32) with 63.
  change (64 - 0 * 32) with 64 in *.
  split.
  - rewrite Z.shiftr_div_pow2 by lia.
    apply div_ineq; lia.
  - intro.
    rewrite Z.shiftr_div_pow2 by lia.
    destruct Hlr.
    apply(Z_div_ge _ _ (2^63)) in H; try lia.
    assert(etable_values lhs_u64_cell i <= 2^64) by lia.
    apply(Z.div_le_mono _ _ (2^63)) in H2; try lia.
    rewrite Z_div_same in H by lia.
    rewrite <- Z.pow_sub_r in H2; try lia.
    change (2^(64-63)) with 2 in H2.
    assert(etable_values lhs_u64_cell i / 2^63 = 1 \/ etable_values lhs_u64_cell i / 2^63 = 2) by lia.
    destruct H3; auto.
    apply div_ineq in H3; lia.  
Qed.


Lemma rhs_flag_bit_neg_iff_64 : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_i32_cell i = 0 ->
    etable_values is_sign_cell i = 1 ->
    etable_values rhs_flag_bit_cell i = 1 <->
    etable_values rhs_u64_cell i >= Wasm_int.Int64.half_modulus.
Proof.
  intros i Hrange Hops Hi32 Hsign.
  change Wasm_int.Int64.half_modulus with (2^63).
  rewrite rhs_flag_bit_cell_is_most_significant_bit_of_rhs; auto.
  pose(Hrr := rhs_range i Hrange Hops).
  rewrite Hi32 in *.
  change (63 - 0 * 32) with 63.
  change (64 - 0 * 32) with 64 in *.
  split.
  - rewrite Z.shiftr_div_pow2 by lia.
    apply div_ineq; lia.
  - intro.
    rewrite Z.shiftr_div_pow2 by lia.
    destruct Hrr.
    apply(Z_div_ge _ _ (2^63)) in H; try lia.
    assert(etable_values rhs_u64_cell i <= 2^64) by lia.
    apply(Z.div_le_mono _ _ (2^63)) in H2; try lia.
    rewrite Z_div_same in H by lia.
    rewrite <- Z.pow_sub_r in H2; try lia.
    change (2^(64-63)) with 2 in H2.
    assert(etable_values rhs_u64_cell i / 2^63 = 1 \/ etable_values rhs_u64_cell i / 2^63 = 2) by lia.
    destruct H3; auto.
    apply div_ineq in H3; lia.  
Qed.


Lemma lhs_minus_64_modulus_neg : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values lhs_u64_cell i - Wasm_int.Int64.modulus < 0.
Proof.
  intros i Hrange Hops.
  pose(lhs_range i Hrange Hops).
  change Wasm_int.Int64.modulus with (2^64).
  destruct (is_i32_bit i); rewrite H in *; lia.
Qed.


Lemma rhs_minus_64_modulus_neg : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values rhs_u64_cell i - Wasm_int.Int64.modulus < 0.
Proof.
  intros i Hrange Hops.
  pose(rhs_range i Hrange Hops).
  change Wasm_int.Int64.modulus with (2^64).
  destruct (is_i32_bit i); rewrite H in *; lia.
Qed.




Lemma lhs_flag_bit_pos_iff_32 : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_i32_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values lhs_flag_bit_cell i = 0 <->
    etable_values lhs_u64_cell i < Wasm_int.Int32.half_modulus.
Proof.
  intros i Hrange Hops Hi32 Hsign.
  change Wasm_int.Int32.half_modulus with (2^31).
  rewrite lhs_flag_bit_cell_is_most_significant_bit_of_lhs; auto.
  rewrite Hi32.
  rewrite shiftr_eq_0; try lia.
  apply lhs_range; auto.
Qed.


Lemma rhs_flag_bit_pos_iff_32 : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_i32_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values rhs_flag_bit_cell i = 0 <->
    etable_values rhs_u64_cell i < Wasm_int.Int32.half_modulus.
Proof.
  intros i Hrange Hops Hi32 Hsign.
  change Wasm_int.Int32.half_modulus with (2^31).
  rewrite rhs_flag_bit_cell_is_most_significant_bit_of_rhs; auto.
  rewrite Hi32.
  rewrite shiftr_eq_0; try lia.
  apply rhs_range; auto.
Qed.


Lemma lhs_minus_32_modulus_neg : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_i32_cell i = 1 ->
    etable_values lhs_u64_cell i - Wasm_int.Int32.modulus < 0.
Proof.
  intros i Hrange Hops.
  pose(lhs_range i Hrange Hops).
  change Wasm_int.Int32.modulus with (2^32).
  destruct (is_i32_bit i); rewrite H in *; lia.
Qed.


Lemma rhs_minus_32_modulus_neg : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_i32_cell i = 1 ->
    etable_values rhs_u64_cell i - Wasm_int.Int32.modulus < 0.
Proof.
  intros i Hrange Hops.
  pose(rhs_range i Hrange Hops).
  change Wasm_int.Int32.modulus with (2^32).
  destruct (is_i32_bit i); rewrite H in *; lia.
Qed.


Lemma lhs_flag_bit_neg_iff_32 : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_i32_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values lhs_flag_bit_cell i = 1 <->
    etable_values lhs_u64_cell i >= Wasm_int.Int32.half_modulus.
Proof.
  intros i Hrange Hops Hi32 Hsign.
  change Wasm_int.Int32.half_modulus with (2^31).
  rewrite lhs_flag_bit_cell_is_most_significant_bit_of_lhs; auto.
  pose(Hlr := lhs_range i Hrange Hops).
  rewrite Hi32 in *.
  change (63 - 0 * 32) with 63.
  change (64 - 0 * 32) with 64 in *.
  split.
  - rewrite Z.shiftr_div_pow2 by lia.
    apply div_ineq; lia.
  - intro.
    rewrite Z.shiftr_div_pow2 by lia.
    destruct Hlr.
    apply(Z_div_ge _ _ (2^31)) in H; try lia.
    assert(etable_values lhs_u64_cell i <= 2^32) by lia.
    apply(Z.div_le_mono _ _ (2^31)) in H2; try lia.
    rewrite Z_div_same in H by lia.
    rewrite <- Z.pow_sub_r in H2; try lia.
    change (2^(32-31)) with 2 in H2.
    assert(etable_values lhs_u64_cell i / 2^31 = 1 \/ etable_values lhs_u64_cell i / 2^31 = 2) by lia.
    destruct H3; auto.
    apply div_ineq in H3; lia.  
Qed.


Lemma rhs_flag_bit_neg_iff_32 : forall i,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values is_i32_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values rhs_flag_bit_cell i = 1 <->
    etable_values rhs_u64_cell i >= Wasm_int.Int32.half_modulus.
Proof.
  intros i Hrange Hops Hi32 Hsign.
  change Wasm_int.Int32.half_modulus with (2^31).
  rewrite rhs_flag_bit_cell_is_most_significant_bit_of_rhs; auto.
  pose(Hrr := rhs_range i Hrange Hops).
  rewrite Hi32 in *.
  change (63 - 0 * 32) with 63.
  change (64 - 0 * 32) with 64 in *.
  split.
  - rewrite Z.shiftr_div_pow2 by lia.
    apply div_ineq; lia.
  - intro.
    rewrite Z.shiftr_div_pow2 by lia.
    destruct Hrr.
    apply(Z_div_ge _ _ (2^31)) in H; try lia.
    assert(etable_values rhs_u64_cell i <= 2^32) by lia.
    apply(Z.div_le_mono _ _ (2^31)) in H2; try lia.
    rewrite Z_div_same in H by lia.
    rewrite <- Z.pow_sub_r in H2; try lia.
    change (2^(32-31)) with 2 in H2.
    assert(etable_values rhs_u64_cell i / 2^31 = 1 \/ etable_values rhs_u64_cell i / 2^31 = 2) by lia.
    destruct H3; auto.
    apply div_ineq in H3; lia.  
Qed.


Lemma eq_64_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_eq_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_eq i64m l r).
Proof.
    intros i l r Hrange Hops Heq Hi32 Hl Hr; simpl in *.
    unfold Wasm_int.Int64.eq.
    rewrite <- Hl, <- Hr.
    rewrite eq_res_value; auto.
    repeat destruct Coqlib.zeq; simpl Z_of_bool.
    - rewrite res_is_eq_criteria; auto; try lia.
    - rewrite res_is_ne_criteria; auto; try lia.
Qed.


(* Wasm_int.int_eq *)
Theorem OpRelEq_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_eq_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_eq i64m x2 x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
          - apply Hrange.
          - apply Hop.
          - apply (is_i32_bit i).
          - eauto.
          - apply Hstk.
          - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_eq i64m x2 x1)).
          {
            apply (eq_64_correct i _ _ Hrange Hop Hop_class Hi32 Hlhs Hrhs).
          }
          rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

          eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.



Lemma eq_32_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_eq_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_eq i32m l r).
Proof.
    intros i l r Hrange Hops Heq Hi32 Hl Hr; simpl in *.
    unfold Wasm_int.Int32.eq.
    rewrite <- Hl, <- Hr.
    rewrite eq_res_value; auto.
    repeat destruct Coqlib.zeq; simpl Z_of_bool.
    - rewrite res_is_eq_criteria; auto; try lia.
    - rewrite res_is_ne_criteria; auto; try lia.
Qed.


(* Wasm_int.int_eq *)
Theorem OpRelEq_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_eq_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_eq i32m x2 x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
          - apply Hrange.
          - apply Hop.
          - apply (is_i32_bit i).
          - eauto.
          - apply Hstk.
          - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_eq i32m x2 x1)).
          {
            apply (eq_32_correct i _ _ Hrange Hop Hop_class Hi32 Hlhs Hrhs).
          }
          rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

          eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma ne_64_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ne_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m r ->
    etable_values res i = Z_of_bool_opp (Wasm_int.int_eq i64m l r).
Proof.
    intros i l r Hrange Hops Hne Hi32 Hl Hr; simpl in *.
    unfold Wasm_int.Int64.eq.
    rewrite <- Hl, <- Hr.
    rewrite ne_res_value; auto.
    repeat destruct Coqlib.zeq; simpl Z_of_bool_opp.
    - rewrite res_is_eq_criteria; auto; try lia.
    - rewrite res_is_ne_criteria; auto; try lia.
Qed.


Theorem OpRelNe_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ne_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = ( Wasm_int.Z_of_uint i64m x1 ::  Wasm_int.Z_of_uint i64m x2 :: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool_opp (Wasm_int.int_eq i64m x2 x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].

    assert (Hrhs: etable_values rhs_u64_cell i =  Wasm_int.Z_of_uint i64m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i =  Wasm_int.Z_of_uint i64m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
          - apply Hrange.
          - apply Hop.
          - apply (is_i32_bit i).
          - eauto.
          - apply Hstk.
          - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool_opp (Wasm_int.int_eq i64m x2 x1)).
          {
            apply (ne_64_correct i _ _ Hrange Hop Hop_class Hi32 Hlhs Hrhs).
          }
          rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

          eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.            
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma ne_32_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ne_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m r ->
    etable_values res i = Z_of_bool_opp (Wasm_int.int_eq i32m l r).
Proof.
    intros i l r Hrange Hops Hne Hi32 Hl Hr; simpl in *.
    unfold Wasm_int.Int32.eq.
    rewrite <- Hl, <- Hr.
    rewrite ne_res_value; auto.
    repeat destruct Coqlib.zeq; simpl Z_of_bool_opp.
    - rewrite res_is_eq_criteria; auto; try lia.
    - rewrite res_is_ne_criteria; auto; try lia.
Qed.


Theorem OpRelNe_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ne_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = ( Wasm_int.Z_of_uint i32m x1 ::  Wasm_int.Z_of_uint i32m x2 :: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool_opp (Wasm_int.int_eq i32m x2 x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].

    assert (Hrhs: etable_values rhs_u64_cell i =  Wasm_int.Z_of_uint i32m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i =  Wasm_int.Z_of_uint i32m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
          - apply Hrange.
          - apply Hop.
          - apply (is_i32_bit i).
          - eauto.
          - apply Hstk.
          - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool_opp (Wasm_int.int_eq i32m x2 x1)).
          {
            apply (ne_32_correct i _ _ Hrange Hop Hop_class Hi32 Hlhs Hrhs).
          }
          rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

          eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.            
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma lt_u_64_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_lt_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 0 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_lt_u i64m l r).
Proof.
    intros i l r Hrange Hops Hltu Hsign Hi32 Hl Hr.
    simpl in *.
    unfold Wasm_int.Int64.ltu.
    rewrite <- Hl, <- Hr.
    rewrite lt_res_value; auto.
    rewrite l_neg_r_pos_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
    destruct(unsigned_means_flags_zero i Hrange Hops Hsign) as [Hlf Hrf].
    destruct (Coqlib.zlt (etable_values lhs_u64_cell i) 
        (etable_values rhs_u64_cell i)) as [Hlt | Hge].
    - simpl Z_of_bool.
        rewrite res_is_lt_criteria; auto.
        lia.
    - simpl Z_of_bool.
        apply gte_decomp in Hge.
        destruct Hge as [Heq | Hgt].
        - pose(res_is_eq_criteria i Hrange Hops Heq).
        pose(eq_or_lt_or_gt i Hrange Hops).
        assert(etable_values res_is_lt_cell i = 0) by lia.
        lia.
        - pose(res_is_gt_criteria i Hrange Hops Hgt).
        pose(eq_or_lt_or_gt i Hrange Hops).
        assert(etable_values res_is_lt_cell i = 0) by lia.
        lia.
Qed.


(* Wasm_int.int_lt_u *)
Theorem OpRelLt_u_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_lt_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_lt_u i64m x2  x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_lt_u i64m x2  x1)).
        {
            apply (lt_u_64_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.

    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma lt_u_32_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_lt_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 1 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_lt_u i32m l r).
Proof.
    intros i l r Hrange Hops Hltu Hsign Hi32 Hl Hr.
    simpl in *.
    unfold Wasm_int.Int32.ltu.
    rewrite <- Hl, <- Hr.
    rewrite lt_res_value; auto.
    rewrite l_neg_r_pos_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
    destruct(unsigned_means_flags_zero i Hrange Hops Hsign) as [Hlf Hrf].
    destruct (Coqlib.zlt (etable_values lhs_u64_cell i) 
      (etable_values rhs_u64_cell i)) as [Hlt | Hge].
    - simpl Z_of_bool.
      rewrite res_is_lt_criteria; auto.
      lia.
    - simpl Z_of_bool.
      apply gte_decomp in Hge.
      destruct Hge as [Heq | Hgt].
      - pose(res_is_eq_criteria i Hrange Hops Heq).
        pose(eq_or_lt_or_gt i Hrange Hops).
        assert(etable_values res_is_lt_cell i = 0) by lia.
        lia.
      - pose(res_is_gt_criteria i Hrange Hops Hgt).
        pose(eq_or_lt_or_gt i Hrange Hops).
        assert(etable_values res_is_lt_cell i = 0) by lia.
        lia.
Qed.

(* Wasm_int.int_lt_u *)
Theorem OpRelLt_u_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_lt_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_lt_u i32m x2  x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_lt_u i32m x2  x1)).
        {
            apply (lt_u_32_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.

Lemma lt_s_64_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_lt_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_lt_s i64m l r).
Proof.
  intros i l r Hrange Hops Hlt Hsign Hi32 Hl Hr.
  simpl in *.
  unfold Wasm_int.Int64.lt.
  unfold Wasm_int.Int64.signed.
  rewrite <- Hl, <- Hr.
  rewrite lt_res_value; auto.
  rewrite l_neg_r_pos_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
  repeat destruct Coqlib.zlt; simpl Z_of_bool.
  rewrite <- lhs_flag_bit_pos_iff_64, <- rhs_flag_bit_pos_iff_64 in *; auto.
  - rewrite res_is_lt_criteria; auto; lia.
  - pose(lhs_range i Hrange Hops).
    pose(rhs_minus_64_modulus_neg i Hrange Hops); lia.
  - rewrite <- lhs_flag_bit_neg_iff_64, <- rhs_flag_bit_pos_iff_64 in *; auto; lia.
  - rewrite <- Z.sub_lt_mono_r in *.
    rewrite <- lhs_flag_bit_neg_iff_64, <- rhs_flag_bit_neg_iff_64 in *; auto.
    rewrite res_is_lt_criteria; auto; lia.
  - rewrite <- lhs_flag_bit_pos_iff_64, <- rhs_flag_bit_pos_iff_64 in *; auto.
    assert(etable_values res_is_lt_cell i = 0).
    - apply gte_decomp in g.
      destruct g.
      pose(res_is_eq_criteria i Hrange Hops H).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(res_is_gt_criteria i Hrange Hops H).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
    lia.
  - rewrite <- lhs_flag_bit_pos_iff_64, <- rhs_flag_bit_neg_iff_64 in *; auto; lia.
  - pose(lhs_minus_64_modulus_neg i Hrange Hops).
    pose(rhs_range i Hrange Hops); lia.
  - rewrite <- lhs_flag_bit_neg_iff_64, <- rhs_flag_bit_neg_iff_64 in *; auto.
    assert(etable_values lhs_u64_cell i >= etable_values rhs_u64_cell i) by lia.
    assert(etable_values res_is_lt_cell i = 0).
    - apply gte_decomp in H.
      destruct H.
      pose(res_is_eq_criteria i Hrange Hops H).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(res_is_gt_criteria i Hrange Hops H).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
    lia.
Qed.


(* Wasm_int.int_lt_s *)
Theorem OpRelLt_s_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_lt_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_lt_s i64m x2  x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_lt_s i64m x2  x1)).
        {
            apply (lt_s_64_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma lt_s_32_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_lt_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_lt_s i32m l r).
Proof.
  intros i l r Hrange Hops Hlt Hsign Hi32 Hl Hr.
  simpl in *.
  unfold Wasm_int.Int32.lt.
  unfold Wasm_int.Int32.signed.
  rewrite <- Hl, <- Hr.
  rewrite lt_res_value; auto.
  rewrite l_neg_r_pos_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
  repeat destruct Coqlib.zlt; simpl Z_of_bool.
  rewrite <- lhs_flag_bit_pos_iff_32, <- rhs_flag_bit_pos_iff_32 in *; auto.
  - rewrite res_is_lt_criteria; auto; lia.
  - pose(lhs_range i Hrange Hops).
    pose(rhs_minus_32_modulus_neg i Hrange Hops); lia.
  - rewrite <- lhs_flag_bit_neg_iff_32, <- rhs_flag_bit_pos_iff_32 in *; auto; lia.
  - rewrite <- Z.sub_lt_mono_r in *. 
    rewrite <- lhs_flag_bit_neg_iff_32, <- rhs_flag_bit_neg_iff_32 in *; auto. 
    rewrite res_is_lt_criteria; auto; lia.
  - rewrite <- lhs_flag_bit_pos_iff_32, <- rhs_flag_bit_pos_iff_32 in *; auto.
    assert(etable_values res_is_lt_cell i = 0).
    - apply gte_decomp in g.
      destruct g.
      pose(res_is_eq_criteria i Hrange Hops H).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(res_is_gt_criteria i Hrange Hops H).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
    lia.
  - rewrite <- lhs_flag_bit_pos_iff_32, <- rhs_flag_bit_neg_iff_32 in *; auto; lia.
  - pose(lhs_minus_32_modulus_neg i Hrange Hops).
    pose(rhs_range i Hrange Hops); lia.
  - rewrite <- lhs_flag_bit_neg_iff_32, <- rhs_flag_bit_neg_iff_32 in *; auto.
    assert(etable_values lhs_u64_cell i >= etable_values rhs_u64_cell i) by lia.
    assert(etable_values res_is_lt_cell i = 0).
    - apply gte_decomp in H.
      destruct H.
      pose(res_is_eq_criteria i Hrange Hops H).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(res_is_gt_criteria i Hrange Hops H).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
    lia.
Qed.


(* Wasm_int.int_lt_u *)
Theorem OpRelLt_s_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_lt_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_lt_s i32m x2  x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_lt_s i32m x2  x1)).
        {
            apply (lt_s_32_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.

        assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
        = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
      - rewrite fid_change with (idx := Rel); auto.
        rewrite iid_change with (idx := Rel); auto.
        simpl.
        pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
        rewrite pc_update_stack in H.
        rewrite incr_iid_update_stack in *.
        destruct Hrel.
        rewrite pc_update_stack_incr_iid.
        rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma gt_u_64_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_gt_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 0 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_gt_u i64m l r).
Proof.
  intros i l r Hrange Hops Hlt Hsign Hi32 Hl Hr.
  simpl in *.
  unfold Wasm_int.Int64.ltu.
  rewrite <- Hl, <- Hr.
  rewrite gt_res_value; auto.
  rewrite l_pos_r_neg_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
  pose(Hunsign := unsigned_means_flags_zero i Hrange Hops Hsign).
  destruct Hunsign as [Hunsignl Hunsignr].
  rewrite Hunsignl, Hunsignr; auto; simpl.
  rewrite Z.add_0_r in *.

  repeat destruct Coqlib.zlt; simpl Z_of_bool.
  - rewrite res_is_gt_criteria; auto; try lia.
    assert(etable_values res_is_gt_cell i = 0).
    - apply gte_decomp in g.
      destruct g.
      symmetry in H.
      pose(res_is_eq_criteria i Hrange Hops H).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      apply(Z.gt_lt_iff) in H.
      pose(res_is_lt_criteria i Hrange Hops H).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.

    rewrite H in *.
    lia.
Qed.


(* Wasm_int.int_gt_u *)
Theorem OpRelGt_u_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_gt_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_gt_u i64m x2 x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_gt_u i64m x2 x1)).
        {
            apply (gt_u_64_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.
        
        assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
        = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
      - rewrite fid_change with (idx := Rel); auto.
        rewrite iid_change with (idx := Rel); auto.
        simpl.
        pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
        rewrite pc_update_stack in H.
        rewrite incr_iid_update_stack in *.
        destruct Hrel.
        rewrite pc_update_stack_incr_iid.
        rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma gt_u_32_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_gt_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 1 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_gt_u i32m l r).
Proof.
  intros i l r Hrange Hops Hlt Hsign Hi32 Hl Hr.
  simpl in *.
  unfold Wasm_int.Int32.ltu.
  rewrite <- Hl, <- Hr.
  rewrite gt_res_value; auto.
  rewrite l_pos_r_neg_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
  pose(Hunsign := unsigned_means_flags_zero i Hrange Hops Hsign).
  destruct Hunsign as [Hunsignl Hunsignr].
  rewrite Hunsignl, Hunsignr; auto; simpl.
  rewrite Z.add_0_r in *.

  repeat destruct Coqlib.zlt; simpl Z_of_bool.
  - rewrite res_is_gt_criteria; auto; try lia.
    assert(etable_values res_is_gt_cell i = 0).
    - apply gte_decomp in g.
      destruct g.
      symmetry in H.
      pose(res_is_eq_criteria i Hrange Hops H).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      apply(Z.gt_lt_iff) in H.
      pose(res_is_lt_criteria i Hrange Hops H).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.

    rewrite H in *.
    lia.
Qed.


(* Wasm_int.int_gt_u *)
Theorem OpRelGt_u_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_gt_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_gt_u i32m x2 x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_gt_u i32m x2 x1)).
        {
            apply (gt_u_32_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma gt_s_64_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_gt_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_gt_s i64m l r).
Proof.
    intros i l r Hrange Hops Hlt Hsign Hi32 Hl Hr.
    simpl in *.
    unfold Wasm_int.Int64.lt.
    unfold Wasm_int.Int64.signed.
    rewrite <- Hl, <- Hr.
    rewrite gt_res_value; auto.
    rewrite l_pos_r_neg_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
    repeat destruct Coqlib.zlt; simpl Z_of_bool.
    rewrite <- lhs_flag_bit_pos_iff_64, <- rhs_flag_bit_pos_iff_64 in *; auto.
    - rewrite res_is_gt_criteria; auto; lia.
    - pose(rhs_range i Hrange Hops).
      pose(lhs_minus_64_modulus_neg i Hrange Hops); lia.
    - rewrite <- rhs_flag_bit_neg_iff_64, <- lhs_flag_bit_pos_iff_64 in *; auto; lia.
    - rewrite <- Z.sub_lt_mono_r in *.
      rewrite <- lhs_flag_bit_neg_iff_64, <- rhs_flag_bit_neg_iff_64 in *; auto.
      rewrite res_is_gt_criteria; auto; lia.
    - rewrite <- lhs_flag_bit_pos_iff_64, <- rhs_flag_bit_pos_iff_64 in *; auto.
      assert(etable_values res_is_gt_cell i = 0).
      - apply gte_decomp in g.
        destruct g.
        symmetry in H.
        pose(res_is_eq_criteria i Hrange Hops H).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        apply(Z.gt_lt_iff) in H. 
        pose(res_is_lt_criteria i Hrange Hops H).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
      lia.
    - rewrite <- rhs_flag_bit_pos_iff_64, <- lhs_flag_bit_neg_iff_64 in *; auto; lia.
    - pose(rhs_minus_64_modulus_neg i Hrange Hops).
      pose(lhs_range i Hrange Hops); lia.
    - rewrite <- rhs_flag_bit_neg_iff_64, <- lhs_flag_bit_neg_iff_64 in *; auto.
      assert(etable_values rhs_u64_cell i >= etable_values lhs_u64_cell i) by lia.
      assert(etable_values res_is_gt_cell i = 0).
      - apply gte_decomp in H.
        destruct H.
        symmetry in H.
        pose(res_is_eq_criteria i Hrange Hops H).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        apply(Z.gt_lt_iff) in H. 
        pose(res_is_lt_criteria i Hrange Hops H).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
      lia.
Qed.


(* Wasm_int.int_gt_s *)
Theorem OpRelGt_s_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_gt_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_gt_s i64m x2  x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_gt_s i64m x2  x1)).
        {
            apply (gt_s_64_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma gt_s_32_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_gt_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_gt_s i32m l r).
Proof.
    intros i l r Hrange Hops Hlt Hsign Hi32 Hl Hr.
    simpl in *.
    unfold Wasm_int.Int32.lt.
    unfold Wasm_int.Int32.signed.
    rewrite <- Hl, <- Hr.
    rewrite gt_res_value; auto.
    rewrite l_pos_r_neg_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
    repeat destruct Coqlib.zlt; simpl Z_of_bool.
    rewrite <- lhs_flag_bit_pos_iff_32, <- rhs_flag_bit_pos_iff_32 in *; auto.
    - rewrite res_is_gt_criteria; auto; lia.
    - pose(rhs_range i Hrange Hops).
      pose(lhs_minus_32_modulus_neg i Hrange Hops); lia.
    - rewrite <- rhs_flag_bit_neg_iff_32, <- lhs_flag_bit_pos_iff_32 in *; auto; lia.
    - rewrite <- Z.sub_lt_mono_r in *.
      rewrite <- lhs_flag_bit_neg_iff_32, <- rhs_flag_bit_neg_iff_32 in *; auto.
      rewrite res_is_gt_criteria; auto; lia.
    - rewrite <- lhs_flag_bit_pos_iff_32, <- rhs_flag_bit_pos_iff_32 in *; auto.
      assert(etable_values res_is_gt_cell i = 0).
      - apply gte_decomp in g.
        destruct g.
        symmetry in H.
        pose(res_is_eq_criteria i Hrange Hops H).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        apply(Z.gt_lt_iff) in H. 
        pose(res_is_lt_criteria i Hrange Hops H).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
      lia.
    - rewrite <- rhs_flag_bit_pos_iff_32, <- lhs_flag_bit_neg_iff_32 in *; auto; lia.
    - pose(rhs_minus_32_modulus_neg i Hrange Hops).
      pose(lhs_range i Hrange Hops); lia.
    - rewrite <- rhs_flag_bit_neg_iff_32, <- lhs_flag_bit_neg_iff_32 in *; auto.
      assert(etable_values rhs_u64_cell i >= etable_values lhs_u64_cell i) by lia.
      assert(etable_values res_is_gt_cell i = 0).
      - apply gte_decomp in H.
        destruct H.
        symmetry in H.
        pose(res_is_eq_criteria i Hrange Hops H).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        apply(Z.gt_lt_iff) in H. 
        pose(res_is_lt_criteria i Hrange Hops H).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
      lia.
Qed.


(* Wasm_int.int_gt_s *)
Theorem OpRelGt_s_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_gt_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_gt_s i32m x2  x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_gt_s i32m x2  x1)).
        {
            apply (gt_s_32_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma le_u_64_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_le_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 0 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_le_u i64m l r).
Proof.
  intros i l r Hrange Hops Hle Hsign Hi32 Hl Hr.
  simpl in *.
  unfold Wasm_int.Int64.ltu.
  rewrite <- Hl, <- Hr.
  rewrite le_res_value; auto.
  rewrite l_neg_r_pos_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
  destruct(unsigned_means_flags_zero i Hrange Hops Hsign) as [Hlf Hrf].
  destruct (Coqlib.zlt (etable_values rhs_u64_cell i) 
      (etable_values lhs_u64_cell i)) as [Hlt | Hge].
  - simpl Z_of_bool.
      assert(etable_values res_is_gt_cell i = 1).
      apply(Z.gt_lt_iff) in Hlt.
      rewrite res_is_gt_criteria; auto.
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
  - simpl Z_of_bool.
      apply gte_decomp in Hge.
      destruct Hge as [Heq | Hgt].
      - symmetry in Heq.
        pose(res_is_eq_criteria i Hrange Hops Heq).
        pose(eq_or_lt_or_gt i Hrange Hops).
        assert(etable_values res_is_lt_cell i = 0) by lia.
        lia.
      - apply(Z.gt_lt_iff) in Hgt.
        pose(res_is_lt_criteria i Hrange Hops Hgt).
        pose(eq_or_lt_or_gt i Hrange Hops).
        assert(etable_values res_is_eq_cell i = 0) by lia.
        lia.
Qed.


(* Wasm_int.int_le_u *)
Theorem OpRelLe_u_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_le_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_le_u i64m x2 x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_le_u i64m x2 x1)).
        {
            apply (le_u_64_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma le_u_32_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_le_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 1 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_le_u i32m l r).
Proof.
  intros i l r Hrange Hops Hle Hsign Hi32 Hl Hr.
  simpl in *.
  unfold Wasm_int.Int32.ltu.
  rewrite <- Hl, <- Hr.
  rewrite le_res_value; auto.
  rewrite l_neg_r_pos_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
  destruct(unsigned_means_flags_zero i Hrange Hops Hsign) as [Hlf Hrf].
  destruct (Coqlib.zlt (etable_values rhs_u64_cell i) 
      (etable_values lhs_u64_cell i)) as [Hlt | Hge].
  - simpl Z_of_bool.
      assert(etable_values res_is_gt_cell i = 1).
      apply(Z.gt_lt_iff) in Hlt.
      rewrite res_is_gt_criteria; auto.
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
  - simpl Z_of_bool.
      apply gte_decomp in Hge.
      destruct Hge as [Heq | Hgt].
      - symmetry in Heq.
        pose(res_is_eq_criteria i Hrange Hops Heq).
        pose(eq_or_lt_or_gt i Hrange Hops).
        assert(etable_values res_is_lt_cell i = 0) by lia.
        lia.
      - apply(Z.gt_lt_iff) in Hgt.
        pose(res_is_lt_criteria i Hrange Hops Hgt).
        pose(eq_or_lt_or_gt i Hrange Hops).
        assert(etable_values res_is_eq_cell i = 0) by lia.
        lia.
Qed.


(* Wasm_int.int_le_u *)
Theorem OpRelLe_u_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_le_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_le_u i32m x2 x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_le_u i32m x2 x1)).
        {
            apply (le_u_32_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma le_s_64_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_le_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_le_s i64m l r).
Proof.
    intros i l r Hrange Hops Hle Hsign H64 Hl Hr.
    simpl in *.
    unfold Wasm_int.Int64.lt.
    unfold Wasm_int.Int64.signed.
    rewrite <- Hl, <- Hr.
    rewrite le_res_value; auto.
    rewrite l_neg_r_pos_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
    repeat destruct Coqlib.zlt; simpl Z_of_bool.
    rewrite <- lhs_flag_bit_pos_iff_64, <- rhs_flag_bit_pos_iff_64 in *; auto.
    - assert(etable_values res_is_gt_cell i = 1).
      rewrite res_is_gt_criteria; auto; lia.
      assert(etable_values res_is_lt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(rhs_range i Hrange Hops).
      pose(lhs_minus_64_modulus_neg i Hrange Hops); lia.

    - assert(etable_values res_is_gt_cell i = 1).
      rewrite res_is_gt_criteria; auto; lia.
      assert(etable_values res_is_lt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(rhs_range i Hrange Hops).
      pose(lhs_minus_64_modulus_neg i Hrange Hops); lia.

    - assert(etable_values res_is_lt_cell i = 1).
      rewrite res_is_lt_criteria; auto; lia.
      assert(etable_values res_is_gt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      rewrite <- rhs_flag_bit_neg_iff_64, <- lhs_flag_bit_pos_iff_64 in *; auto; lia.
      rewrite <- Z.sub_lt_mono_r in *.

    - rewrite <- lhs_flag_bit_neg_iff_64, <- rhs_flag_bit_neg_iff_64 in *; auto.
      assert(etable_values res_is_gt_cell i = 1).
      rewrite res_is_gt_criteria; auto; lia.
      assert(etable_values res_is_lt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(rhs_range i Hrange Hops).
      pose(lhs_minus_64_modulus_neg i Hrange Hops); lia.

    - rewrite <- lhs_flag_bit_pos_iff_64, <- rhs_flag_bit_pos_iff_64 in *; auto.
      apply(Z.ge_le_iff) in g. 
      apply lte_decomp in g.
      - destruct g.
        assert(etable_values res_is_eq_cell i = 1).
        pose(res_is_eq_criteria i Hrange Hops H); lia.
        pose(eq_or_lt_or_gt i Hrange Hops); lia.

      - assert(etable_values res_is_lt_cell i = 1).
        pose(res_is_lt_criteria i Hrange Hops H); lia.
        assert(etable_values res_is_eq_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); auto; lia.
        lia.
    
      - assert(etable_values lhs_u64_cell i > etable_values rhs_u64_cell i) by lia.
        pose(res_is_gt_criteria i Hrange Hops H).
        assert(etable_values res_is_eq_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        rewrite <- rhs_flag_bit_pos_iff_64, <- lhs_flag_bit_neg_iff_64 in *; auto; lia.
                
      - pose(rhs_minus_64_modulus_neg i Hrange Hops).
        pose(lhs_range i Hrange Hops); lia.
        apply(Z.ge_le_iff) in g. 
        rewrite <- Z.sub_le_mono_r in *.        
        
      - apply lte_decomp in g.
        destruct g.
        assert(etable_values res_is_eq_cell i = 1).
        pose(res_is_eq_criteria i Hrange Hops H); lia.
        assert(etable_values res_is_lt_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        rewrite <- rhs_flag_bit_neg_iff_64, <- lhs_flag_bit_neg_iff_64 in *; auto; lia.
                
      - assert(etable_values res_is_lt_cell i = 1).
        pose(res_is_lt_criteria i Hrange Hops H); lia.
        assert(etable_values res_is_eq_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        rewrite <- rhs_flag_bit_neg_iff_64, <- lhs_flag_bit_neg_iff_64 in *; auto; lia.
Qed.


(* Wasm_int.int_le_s *)
Theorem OpRelLe_s_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_le_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_le_s i64m x2 x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_le_s i64m x2 x1)).
        {
            apply (le_s_64_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma le_s_32_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_le_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_le_s i32m l r).
Proof.
    intros i l r Hrange Hops Hle Hsign Hi32 Hl Hr.
    simpl in *.
    unfold Wasm_int.Int32.lt.
    unfold Wasm_int.Int32.signed.
    rewrite <- Hl, <- Hr.
    rewrite le_res_value; auto.
    rewrite l_neg_r_pos_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
    repeat destruct Coqlib.zlt; simpl Z_of_bool.
    rewrite <- lhs_flag_bit_pos_iff_32, <- rhs_flag_bit_pos_iff_32 in *; auto.
    - assert(etable_values res_is_gt_cell i = 1).
      rewrite res_is_gt_criteria; auto; lia.
      assert(etable_values res_is_lt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(rhs_range i Hrange Hops).
      pose(lhs_minus_32_modulus_neg i Hrange Hops); lia.

    - assert(etable_values res_is_gt_cell i = 1).
      rewrite res_is_gt_criteria; auto; lia.
      assert(etable_values res_is_lt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(rhs_range i Hrange Hops).
      pose(lhs_minus_32_modulus_neg i Hrange Hops); lia.

    - assert(etable_values res_is_lt_cell i = 1).
      rewrite res_is_lt_criteria; auto; lia.
      assert(etable_values res_is_gt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      rewrite <- rhs_flag_bit_neg_iff_32, <- lhs_flag_bit_pos_iff_32 in *; auto; lia.
      rewrite <- Z.sub_lt_mono_r in *.

    - rewrite <- lhs_flag_bit_neg_iff_32, <- rhs_flag_bit_neg_iff_32 in *; auto.
      assert(etable_values res_is_gt_cell i = 1).
      rewrite res_is_gt_criteria; auto; lia.
      assert(etable_values res_is_lt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(rhs_range i Hrange Hops).
      pose(lhs_minus_32_modulus_neg i Hrange Hops); lia.

    - rewrite <- lhs_flag_bit_pos_iff_32, <- rhs_flag_bit_pos_iff_32 in *; auto.
      apply(Z.ge_le_iff) in g. 
      apply lte_decomp in g.
      - destruct g.
        assert(etable_values res_is_eq_cell i = 1).
        pose(res_is_eq_criteria i Hrange Hops H); lia.
        pose(eq_or_lt_or_gt i Hrange Hops); lia.

      - assert(etable_values res_is_lt_cell i = 1).
        pose(res_is_lt_criteria i Hrange Hops H); lia.
        assert(etable_values res_is_eq_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); auto; lia.
        lia.
    
      - assert(etable_values lhs_u64_cell i > etable_values rhs_u64_cell i) by lia.
        pose(res_is_gt_criteria i Hrange Hops H).
        assert(etable_values res_is_eq_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        rewrite <- rhs_flag_bit_pos_iff_32, <- lhs_flag_bit_neg_iff_32 in *; auto; lia.
                
      - pose(rhs_minus_32_modulus_neg i Hrange Hops).
        pose(lhs_range i Hrange Hops); lia.
        apply(Z.ge_le_iff) in g. 
        rewrite <- Z.sub_le_mono_r in *.        
        
      - apply lte_decomp in g.
        destruct g.
        assert(etable_values res_is_eq_cell i = 1).
        pose(res_is_eq_criteria i Hrange Hops H); lia.
        assert(etable_values res_is_lt_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        rewrite <- rhs_flag_bit_neg_iff_32, <- lhs_flag_bit_neg_iff_32 in *; auto; lia.
                
      - assert(etable_values res_is_lt_cell i = 1).
        pose(res_is_lt_criteria i Hrange Hops H); lia.
        assert(etable_values res_is_eq_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        rewrite <- rhs_flag_bit_neg_iff_32, <- lhs_flag_bit_neg_iff_32 in *; auto; lia.
Qed.


(* Wasm_int.int_le_s *)
Theorem OpRelLe_s_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_le_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_le_s i32m x2 x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_le_s i32m x2 x1)).
        {
            apply (le_s_32_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma ge_u_64_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ge_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 0 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_ge_u i64m l r).
Proof.
intros i l r Hrange Hops Hle Hsign Hi32 Hl Hr.
simpl in *.
unfold Wasm_int.Int64.ltu.
rewrite <- Hl, <- Hr.
rewrite ge_res_value; auto.
rewrite l_pos_r_neg_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
destruct(unsigned_means_flags_zero i Hrange Hops Hsign) as [Hlf Hrf].
destruct (Coqlib.zlt (etable_values lhs_u64_cell i) (etable_values rhs_u64_cell i)) as [Hlt | Hge].
- simpl Z_of_bool.
    assert(etable_values res_is_lt_cell i = 1).
    rewrite res_is_lt_criteria; auto.
    assert(etable_values res_is_eq_cell i = 0 /\ etable_values res_is_gt_cell i = 0).
    pose(eq_or_lt_or_gt i Hrange Hops); auto; lia.
    lia.
- simpl Z_of_bool.
    apply gte_decomp in Hge.
    destruct Hge as [Heq | Hgt].
    - pose(res_is_eq_criteria i Hrange Hops Heq).
      pose(eq_or_lt_or_gt i Hrange Hops).
      assert(etable_values res_is_lt_cell i = 0) by lia.
      lia.
    - pose(res_is_gt_criteria i Hrange Hops Hgt).
      pose(eq_or_lt_or_gt i Hrange Hops).
      assert(etable_values res_is_eq_cell i = 0) by lia.
      lia.
Qed.


(* Wasm_int.int_ge_u *)
Theorem OpRelGe_u_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ge_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_ge_u i64m x2 x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_ge_u i64m x2 x1)).
        {
            apply (ge_u_64_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma ge_u_32_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ge_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 1 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_ge_u i32m l r).
Proof.
    intros i l r Hrange Hops Hle Hsign Hi32 Hl Hr.
    simpl in *.
    unfold Wasm_int.Int32.ltu.
    rewrite <- Hl, <- Hr.
    rewrite ge_res_value; auto.
    rewrite l_pos_r_neg_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
    destruct(unsigned_means_flags_zero i Hrange Hops Hsign) as [Hlf Hrf].
    destruct (Coqlib.zlt (etable_values lhs_u64_cell i) (etable_values rhs_u64_cell i)) as [Hlt | Hge].
    - simpl Z_of_bool.
        assert(etable_values res_is_lt_cell i = 1).
        rewrite res_is_lt_criteria; auto.
        assert(etable_values res_is_eq_cell i = 0 /\ etable_values res_is_gt_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); auto; lia.
        lia.
    - simpl Z_of_bool.
        apply gte_decomp in Hge.
        destruct Hge as [Heq | Hgt].
        - pose(res_is_eq_criteria i Hrange Hops Heq).
        pose(eq_or_lt_or_gt i Hrange Hops).
        assert(etable_values res_is_lt_cell i = 0) by lia.
        lia.
        - pose(res_is_gt_criteria i Hrange Hops Hgt).
        pose(eq_or_lt_or_gt i Hrange Hops).
        assert(etable_values res_is_eq_cell i = 0) by lia.
        lia.
Qed.


(* Wasm_int.int_ge_u *)
Theorem OpRelGe_u_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ge_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_ge_u i32m x2 x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_ge_u i32m x2 x1)).
        {
            apply (ge_u_32_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma ge_s_64_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ge_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_ge_s i64m l r).
Proof.
    intros i l r Hrange Hops Hle Hsign Hi32 Hl Hr.
    simpl in *.
    unfold Wasm_int.Int64.lt.
    unfold Wasm_int.Int64.signed.
    rewrite <- Hl, <- Hr.
    rewrite ge_res_value; auto.
    rewrite l_pos_r_neg_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
    repeat destruct Coqlib.zlt; simpl Z_of_bool.
    rewrite <- lhs_flag_bit_pos_iff_64, <- rhs_flag_bit_pos_iff_64 in *; auto.
    - assert(etable_values res_is_lt_cell i = 1).
      rewrite res_is_lt_criteria; auto; lia.
      assert(etable_values res_is_gt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(rhs_range i Hrange Hops).
      pose(lhs_minus_64_modulus_neg i Hrange Hops); lia.

    - assert(etable_values res_is_lt_cell i = 1).
      rewrite res_is_lt_criteria; auto; lia.
      assert(etable_values res_is_gt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(lhs_range i Hrange Hops).
      pose(rhs_minus_64_modulus_neg i Hrange Hops); lia.

    - assert(etable_values res_is_gt_cell i = 1).
      rewrite res_is_gt_criteria; auto; lia.
      assert(etable_values res_is_lt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      rewrite <- rhs_flag_bit_pos_iff_64, <- lhs_flag_bit_neg_iff_64 in *; auto; lia.
      rewrite <- Z.sub_lt_mono_r in *.

    - rewrite <- lhs_flag_bit_neg_iff_64, <- rhs_flag_bit_neg_iff_64 in *; auto.
      assert(etable_values res_is_lt_cell i = 1).
      rewrite res_is_lt_criteria; auto; lia.
      assert(etable_values res_is_gt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(rhs_range i Hrange Hops).
      pose(lhs_minus_64_modulus_neg i Hrange Hops); lia.

    - rewrite <- lhs_flag_bit_pos_iff_64, <- rhs_flag_bit_pos_iff_64 in *; auto.
      apply gte_decomp in g.
      - destruct g.
        assert(etable_values res_is_eq_cell i = 1).
        pose(res_is_eq_criteria i Hrange Hops H); lia.
        pose(eq_or_lt_or_gt i Hrange Hops); lia.

      - assert(etable_values res_is_gt_cell i = 1).
        pose(res_is_gt_criteria i Hrange Hops H); lia.
        assert(etable_values res_is_eq_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); auto; lia.
        lia.
    
      - assert(etable_values lhs_u64_cell i < etable_values rhs_u64_cell i) by lia.
        pose(res_is_lt_criteria i Hrange Hops H).
        assert(etable_values res_is_eq_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        rewrite <- rhs_flag_bit_neg_iff_64, <- lhs_flag_bit_pos_iff_64 in *; auto; lia.
                
      - pose(lhs_minus_64_modulus_neg i Hrange Hops).
        pose(rhs_range i Hrange Hops); lia.
        apply(Z.ge_le_iff) in g. 
        rewrite <- Z.sub_le_mono_r in *.        
        
      - apply lte_decomp in g.
        destruct g.
        assert(etable_values res_is_eq_cell i = 1).
        symmetry in H.
        pose(res_is_eq_criteria i Hrange Hops H); lia.
        assert(etable_values res_is_gt_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        rewrite <- rhs_flag_bit_neg_iff_64, <- lhs_flag_bit_neg_iff_64 in *; auto; lia.
                
      - assert(etable_values res_is_gt_cell i = 1).
        apply(Z.gt_lt_iff) in H. 
        pose(res_is_gt_criteria i Hrange Hops H); lia.
        assert(etable_values res_is_eq_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        rewrite <- rhs_flag_bit_neg_iff_64, <- lhs_flag_bit_neg_iff_64 in *; auto; lia.
Qed.


(* Wasm_int.int_ge_s *)
Theorem OpRelGe_s_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ge_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_ge_s i64m x2 x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i64m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i64m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_ge_s i64m x2 x1)).
        {
            apply (ge_s_64_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.

        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.


Lemma ge_s_32_correct : forall i l r,
    0 <= i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ge_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m l ->
    etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m r ->
    etable_values res i = Z_of_bool (Wasm_int.int_ge_s i32m l r).
Proof.
    intros i l r Hrange Hops Hle Hsign Hi32 Hl Hr.
    simpl in *.
    unfold Wasm_int.Int32.lt.
    unfold Wasm_int.Int32.signed.
    rewrite <- Hl, <- Hr.
    rewrite ge_res_value; auto.
    rewrite l_pos_r_neg_value, l_pos_r_pos_value, l_neg_r_neg_value; auto.
    repeat destruct Coqlib.zlt; simpl Z_of_bool.
    rewrite <- lhs_flag_bit_pos_iff_32, <- rhs_flag_bit_pos_iff_32 in *; auto.
    - assert(etable_values res_is_lt_cell i = 1).
      rewrite res_is_lt_criteria; auto; lia.
      assert(etable_values res_is_gt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(rhs_range i Hrange Hops).
      pose(lhs_minus_32_modulus_neg i Hrange Hops); lia.

    - assert(etable_values res_is_lt_cell i = 1).
      rewrite res_is_lt_criteria; auto; lia.
      assert(etable_values res_is_gt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(lhs_range i Hrange Hops).
      pose(rhs_minus_32_modulus_neg i Hrange Hops); lia.

    - assert(etable_values res_is_gt_cell i = 1).
      rewrite res_is_gt_criteria; auto; lia.
      assert(etable_values res_is_lt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      rewrite <- rhs_flag_bit_pos_iff_32, <- lhs_flag_bit_neg_iff_32 in *; auto; lia.
      rewrite <- Z.sub_lt_mono_r in *.

    - rewrite <- lhs_flag_bit_neg_iff_32, <- rhs_flag_bit_neg_iff_32 in *; auto.
      assert(etable_values res_is_lt_cell i = 1).
      rewrite res_is_lt_criteria; auto; lia.
      assert(etable_values res_is_gt_cell i = 0 /\ etable_values res_is_eq_cell i = 0).
      pose(eq_or_lt_or_gt i Hrange Hops); lia.
      pose(rhs_range i Hrange Hops).
      pose(lhs_minus_32_modulus_neg i Hrange Hops); lia.

    - rewrite <- lhs_flag_bit_pos_iff_32, <- rhs_flag_bit_pos_iff_32 in *; auto.
      apply gte_decomp in g.
      - destruct g.
        assert(etable_values res_is_eq_cell i = 1).
        pose(res_is_eq_criteria i Hrange Hops H); lia.
        pose(eq_or_lt_or_gt i Hrange Hops); lia.

      - assert(etable_values res_is_gt_cell i = 1).
        pose(res_is_gt_criteria i Hrange Hops H); lia.
        assert(etable_values res_is_eq_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); auto; lia.
        lia.
    
      - assert(etable_values lhs_u64_cell i < etable_values rhs_u64_cell i) by lia.
        pose(res_is_lt_criteria i Hrange Hops H).
        assert(etable_values res_is_eq_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        rewrite <- rhs_flag_bit_neg_iff_32, <- lhs_flag_bit_pos_iff_32 in *; auto; lia.
                
      - pose(lhs_minus_32_modulus_neg i Hrange Hops).
        pose(rhs_range i Hrange Hops); lia.
        apply(Z.ge_le_iff) in g. 
        rewrite <- Z.sub_le_mono_r in *.        
        
      - apply lte_decomp in g.
        destruct g.
        assert(etable_values res_is_eq_cell i = 1).
        symmetry in H.
        pose(res_is_eq_criteria i Hrange Hops H); lia.
        assert(etable_values res_is_gt_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        rewrite <- rhs_flag_bit_neg_iff_32, <- lhs_flag_bit_neg_iff_32 in *; auto; lia.
                
      - assert(etable_values res_is_gt_cell i = 1).
        apply(Z.gt_lt_iff) in H. 
        pose(res_is_gt_criteria i Hrange Hops H); lia.
        assert(etable_values res_is_eq_cell i = 0).
        pose(eq_or_lt_or_gt i Hrange Hops); lia.
        rewrite <- rhs_flag_bit_neg_iff_32, <- lhs_flag_bit_neg_iff_32 in *; auto; lia.
Qed.


(* Wasm_int.int_ge_s *)
Theorem OpRelGe_s_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ge_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_ge_s i32m x2 x1) :: xs)).
Proof.
    intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hsign Hi32 Hrel Hstk.
    assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
    apply (relop_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].

    assert (Hrhs: etable_values rhs_u64_cell i = Wasm_int.Z_of_uint i32m x1).
    {
    eapply stack_rel_read_1_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get rhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_rhs. }

    assert (Hlhs: etable_values lhs_u64_cell i = Wasm_int.Z_of_uint i32m x2).
        {
    eapply stack_rel_read_2_without_value with  (is_i32 := fun get => get is_i32_cell)
                                                (value := fun get => get lhs_u64_cell)
                                                (enable := fun get => get (ops_cell Rel)).
        - apply Hrange.
        - apply Hop.
        - apply (is_i32_bit i).
        - eauto.
        - apply Hstk.
        - apply stack_read_lhs. }
    assert (Hres: etable_values res i = Z_of_bool (Wasm_int.int_ge_s i32m x2 x1)).
        {
            apply (ge_s_32_correct i _ _ Hrange Hop Hop_class Hsign Hi32 Hlhs Hrhs).
        }
        rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <- Hres. clear Hop_class Hsign Hi32 Hrhs Hlhs Hres.
        
    assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
      = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
    - rewrite fid_change with (idx := Rel); auto.
      rewrite iid_change with (idx := Rel); auto.
      simpl.
      pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
      rewrite pc_update_stack in H.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite pc_update_stack_incr_iid.
      rewrite state_pc_rel in H; auto.
      
        eapply stack_rel_write_2 with (col := memory_table_lookup_stack_write)
                                        (is_i32 := fun get => get is_i32_cell)
                                        (enable := fun get => get (ops_cell Rel)); auto; try lia.
          - apply (is_i32_bit i).
          - apply Hstk.
          - apply (sp_change i Rel); auto.
          - pose (mpages_change i Rel); simpl in *; lia.
          - rewrite (frame_id_change i Rel); auto; reflexivity.
          - rewrite (fid_change i Rel); auto.
          - apply stack_write.
Qed.
