(* Copyright (C) CertiK 2024-2026 *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import FunctionalExtensionality.
Require Import Shared.
Require Import OpSelectModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_select : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Select i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config Select i)) with 1.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  - apply MTable.mtable_write_mops with
      (offset := etable_values sp_cell i + 3)
      (is_i32 := etable_values is_i32 i)
      (value := etable_values res i); auto.
    apply (alloc_memory_table_lookup_write_cell_correct _ _ _ _ _ _ _ 
      stack_write i Hrange); auto.
    - apply eid_common.
    - apply is_i32_bit.
    - pose(sp_common i); lia.
  lia.
Qed.

Require Import ImageTableModel.
Require Import InjectivityHelper.

Lemma Select_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->    
  etable_values (ops_cell Select) i = 1 ->
  program (wasm_pc st) = ISelect.
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i Select Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  apply opcode_of_instruction_inj.
  rewrite <- Hopcode.
  reflexivity.
Qed.

Lemma result_is_val2_when_cond_is_zero : forall i,
    0 <= i ->
    etable_values (ops_cell Select) i = 1 ->
    etable_values cond i = 0 ->
    etable_values res i = etable_values val2 i.
Proof.
  intros i Hrange Hops Hcond.
  pose(H := select_cond_is_zero i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  rewrite Hcond in H.
  simpl in H.
  lia.
Qed.

Lemma result_is_val1_when_cond_is_not_zero : forall i,
    0 <= i ->
    etable_values (ops_cell Select) i = 1 ->
    etable_values cond i <> 0 ->
    etable_values res i = etable_values val1 i.
Proof.
  intros i Hrange Hops Hcond.
  pose(H := select_cond_is_not_zero i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  rewrite Hops in H.
  rewrite(Z.mul_1_l _) in H.
  destruct H as [H _].
  assert(etable_values res i - etable_values val1 i = 0).
  - apply(Zmult_integral_l (etable_values cond i) _ Hcond).
    lia.
  lia.
Qed.

Lemma select_mops : forall i,
    0 <= i ->
    etable_values eid_cell i > 0 ->
    etable_values enabled_cell i = 1 ->
    etable_values (ops_cell Select) i = 1 ->
    mops_at_correct i ->
        mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with Select in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i Select Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).

  assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  {
    apply (write_cell_mops _ _ _ _ _ _ _ stack_write i Hrange); auto.
    - apply (eid_common i).
    - apply (is_i32_bit).
    - pose (sp_common i).
    - pose (sp_common i); lia.
  }
  lia.
Qed.

Theorem SelectOp_correct : forall i st xcond x2 x1 xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Select) i = 1 ->
  state_rel i st ->
  wasm_stack st = xcond:: x2 :: x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) ((select xcond x2 x1):: xs)).
Proof.
  intros i st xcond x2 x1 xs Hrange Hrow_enabled Hmops Hop Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (select_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hcond: etable_values cond i = xcond).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => 1)
                                 (enable := fun get => get (ops_cell Select))
                                 (value := fun get => get cond).
    - apply Hrange.
    - apply Hop.
    - auto.
    - eauto.
    - eauto.
    - apply stack_read_cond.
  }
  assert (Hval2: etable_values val2 i = x2).
  {
    eapply stack_rel_read_without_value with (n:=1%nat) (is_i32 := fun get => get is_i32)
                                 (enable := fun get => get (ops_cell Select))
                                 (value := fun get => get val2).
    - apply Hrange.
    - lia.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - eauto.
    - eauto.
    - replace(fun get : etable_cols -> Z => get sp_cell + 1 + Z.of_nat 1) with 
      (fun get : etable_cols -> Z => get sp_cell + 2).
      apply stack_read_val2.
      extensionality get. lia.
  }
  assert (Hval1: etable_values val1 i = x1).
  {
    eapply stack_rel_read_without_value with (n:=2%nat) (is_i32 := fun get => get is_i32)
                                 (enable := fun get => get (ops_cell Select))
                                 (value := fun get => get val1).
    - apply Hrange.
    - lia.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - eauto.
    - eauto.
    - replace(fun get : etable_cols -> Z => get sp_cell + 1 + Z.of_nat 2) with 
      (fun get : etable_cols -> Z => get sp_cell + 3).
      apply stack_read_val1.
      extensionality get. lia.
  }
  assert (Hres: etable_values res i = select xcond x2 x1).
  {
    unfold select.
    destruct xcond.
    - rewrite <- Hval2.
      apply(result_is_val2_when_cond_is_zero i Hrange Hop Hcond).
    - rewrite <- Hval1.
      assert(etable_values cond i <> 0).
      - lia.
      apply(result_is_val1_when_cond_is_not_zero i Hrange Hop H).
    - pose(cond_U64 i).
      lia. 
  }
  rewrite <- Hcond in Hstk.
  rewrite <- Hval2 in Hstk.
  rewrite <- Hval1 in Hstk.  
  rewrite <- Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Select); auto.
    rewrite iid_change with (idx := Select); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_3_without_value with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get is_i32)
                                (value := fun get => get res)
                                (enable := fun get => get (ops_cell Select)); auto; try lia.
  - apply (is_i32_bit i).
  - apply Hstk.
  - pose(Hsp := sp_change i Select Hrange Hrow_enabled Hop).
    replace(config_sp_diff (opcode_config Select i)) with 2 in Hsp by constructor.
    lia.
  - pose (mpages_change i Select); simpl in *; lia.    
  - rewrite (frame_id_change i Select); auto; reflexivity.
  - rewrite (fid_change i Select); auto.
  - apply stack_write.
Qed.
