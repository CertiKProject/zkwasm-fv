(* Copyright (C) CertiK 2024-2026 *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpBrModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_br : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Br i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config Br i)) with (etable_values keep_cell i).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= etable_values keep_cell i).
  destruct (keep_cell_bit i) as [Hk | Hk]; rewrite Hk.
  - pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack); lia.
  - apply MTable.mtable_write_mops with
      (offset := etable_values sp_cell i + etable_values drop_cell i + 1)
      (is_i32 := etable_values is_i32_cell i)
      (value := etable_values value_cell i); auto.
    apply (alloc_memory_table_lookup_write_cell_correct _ _ _ _ _ _ _ 
      stack_write i Hrange); auto.
    - apply eid_common.
    - apply is_i32_cell_bit.
    - pose(sp_common i).
      pose(drop_cell_common i); lia.
    - lia.
  lia.
Qed.

Require Import ImageTableModel.
Require Import InjectivityHelper.
  
Lemma config_opcode_inj_Br : forall i instr,
    config_opcode (opcode_config Br i) =
            opcode_of_instruction instr ->
    instr =
      IBr (bool_of_Z (etable_values keep_cell i))
          (Wasm_int.Int32.repr (etable_values drop_cell i))
          (Wasm_int.Int64.repr (etable_values dst_pc_cell i)).
Proof.
  intros.
  apply opcode_of_instruction_inj.
  rewrite <- H. clear H.
  unfold opcode_config, config_opcode, opcode_of_instruction.
  rewrite <- !Zplus_assoc.
  f_equal.
  rewrite bool_of_Z_simpl.
  2: { apply keep_cell_bit. }
  rewrite CommonData.shiftl_1_n.
  2: { cbv - [ Z.le ] ; lia. }
  f_equal.
  rewrite Wasm_int.Int32.unsigned_repr.
  2: { apply iscommon_is32.
      apply drop_cell_common. }
  reflexivity.
  rewrite CommonData.shiftl_1_n.
  2: { cbv - [ Z.le ] ; lia. }
  f_equal.
  rewrite Wasm_int.Int64.unsigned_repr.
  2: {
    apply iscommon_is64.
    apply dst_pc_cell_common.
  }
  reflexivity.
Qed.

Lemma Br_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->    
  etable_values (ops_cell Br) i = 1 ->
  program (wasm_pc st) =
      IBr (bool_of_Z (etable_values keep_cell i))
          (Wasm_int.Int32.repr (etable_values drop_cell i))
          (Wasm_int.Int64.repr (etable_values dst_pc_cell i)).
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i Br Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  apply (config_opcode_inj_Br _ _ Hopcode).
Qed.

Lemma br_mops : forall i,
    0 <= i ->
    etable_values enabled_cell i = 1 ->
    etable_values (ops_cell Br) i = 1 ->
    mops_at_correct i ->
    (etable_values keep_cell i = 1 ->
        mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0) /\
    (etable_values keep_cell i = 0 ->
        mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 0
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0).
Proof.
  intros i Hrange Hrow_enabled Hop_class Hops.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with Br in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i Br Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  split.
  - intros Hkc.
    assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
    {
      apply (write_cell_mops _ _ _ _ _ _ _ stack_write i Hrange); auto.
      - apply (eid_common i).
      - apply (is_i32_cell_bit).
      - pose (sp_common i).
        pose (drop_cell_common i).
        lia.
      - lia.
    }
  lia.
  - intros Hkc.
    lia.
Qed.

Theorem Br_no_keep_correct : forall i st xd xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Br) i = 1 ->
  state_rel i st ->
  wasm_stack st = xd ++ xs ->
  length xd = Z.to_nat (etable_values drop_cell i) ->
  etable_values keep_cell i = 0 ->
  state_rel (i+1) (update_stack (move_to_iid st (etable_values dst_pc_cell i)) xs).
Proof.
  intros i st xd xs Hrange Henabled Hmops Hops Hrel Hstk Hdrop Hkeep.
  assert (Heid := eid_nonzero i Hrange Henabled).
  apply (br_mops) in Hmops; auto.
  destruct Hmops as [_ Hmops].
  destruct Hmops as [Hmops [Hmops' Hmops'']]; auto.

  constructor.
  - rewrite iid_change with (idx := Br); auto.
    rewrite fid_change with (idx := Br); auto.
    simpl.
    pose(H := pc_move_iid (update_stack st xs) (etable_values dst_pc_cell i)).
    rewrite pc_update_stack in H.
    destruct Hrel.
    rewrite state_pc_rel in H.
    rewrite pc_update_stack.
    rewrite move_iid_update_stack in H; auto.
  - rewrite eid_change by auto.
    rewrite sp_change with (idx := Br); auto.
    change (config_sp_diff (opcode_config Br i)) with
      (etable_values drop_cell i).
    apply state_stack_rel in Hrel.
    rewrite Hstk in Hrel.
    replace(etable_values sp_cell i + 1) with 
      (etable_values sp_cell i + 0 + 1) in Hrel by lia.
    eapply stack_rel_drop with 
      (i:= i) 
      (n:= Z.to_nat (etable_values drop_cell i)) in Hrel; auto.
    rewrite Z2Nat.id in Hrel.
    rewrite stack_update_stack.
    replace (etable_values sp_cell i + 0 + 1 + etable_values drop_cell i)
      with (etable_values sp_cell i + etable_values drop_cell i + 1) in Hrel by lia.
    assumption.
    apply drop_cell_common.
  - rewrite globals_update_stack.
    rewrite globals_move_iid.
    rewrite eid_change by auto.
    rewrite globals_no_write; auto.
    destruct Hrel; auto.
  - rewrite eid_change by auto.
    rewrite memory_no_write; auto.
    rewrite (mpages_change i Br) by auto. simpl. rewrite Z.add_0_r.
    rewrite memory_update_stack.
    rewrite memory_move_iid.
    destruct st. simpl.
    destruct Hrel. auto.
    rewrite maximal_memory_pages_change; auto.
  - rewrite callstack_update_stack, callstack_move_iid.
    rewrite (frame_id_change i Br); simpl; auto.
    rewrite (fid_change i Br); simpl; auto.
    destruct Hrel. auto.
Qed.

Theorem Br_keep_correct : forall i st xv xd xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Br) i = 1 ->
  state_rel i st ->
  wasm_stack st = xv :: xd ++ xs ->
  length xd = Z.to_nat (etable_values drop_cell i) ->
  etable_values keep_cell i = 1 ->
  state_rel (i+1) (update_stack (move_to_iid st (etable_values dst_pc_cell i)) (xv :: xs)).
Proof.
  intros i st xv xd xs Hrange Henabled Hmops Hops Hrel Hstk Hdrop Hkeep.
  assert (Heid := eid_nonzero i Hrange Henabled).
  apply (br_mops) in Hmops; auto.
  destruct Hmops as [Hmops _].
  destruct Hmops as [Hmops [Hmops' Hmops'']]; auto.

  assert (Hv: etable_values value_cell i = xv).
  {
    eapply stack_rel_read_1_without_value with 
      (is_i32 := fun get => get is_i32_cell)
      (enable := fun get => get (ops_cell Br) * get keep_cell)
      (value := fun get => get value_cell); auto.
    - lia.
    - apply(is_i32_cell_bit i).
    - eauto.
    - eauto.
    - apply stack_read.
  }
  rewrite <- Hv.

  constructor.
  - rewrite iid_change with (idx := Br); auto.
    rewrite fid_change with (idx := Br); auto.
    simpl.
    pose(H := pc_move_iid (update_stack st xs) (etable_values dst_pc_cell i)).
    rewrite pc_update_stack in H.
    destruct Hrel.
    rewrite state_pc_rel in H.
    rewrite pc_update_stack.
    rewrite move_iid_update_stack in H; auto.
  - rewrite eid_change by auto.
    rewrite sp_change with (idx := Br); auto.
    change (config_sp_diff (opcode_config Br i)) with
      (etable_values drop_cell i).
    apply state_stack_rel in Hrel.
    rewrite Hstk in Hrel.
    simpl in Hrel.
    destruct Hrel as [_ Hrel'].
    replace(etable_values sp_cell i + etable_values drop_cell i + 1) with
      (etable_values sp_cell i + 1 + etable_values drop_cell i) by lia.
    rewrite stack_update_stack.
    pose(drop_cell_common i).
    rewrite <- (Z2Nat.id (etable_values drop_cell i)) by lia.
    eapply stack_rel_write_without_value_large_drop with
      (value:= (fun get => get (value_cell)))
      (enable:= (fun get => get (ops_cell Br) * (get keep_cell)))
      (is_i32:= (fun get => get is_i32_cell))
      (offset:= (fun get => get sp_cell + get drop_cell + 1)); eauto; try lia.
    - apply(is_i32_cell_bit).
    - apply stack_write.
  - rewrite globals_update_stack.
    rewrite globals_move_iid.
    rewrite eid_change by auto.
    rewrite globals_no_write; auto.
    destruct Hrel; auto.
  - rewrite eid_change by auto.
    rewrite memory_no_write; auto.
    rewrite (mpages_change i Br) by auto. simpl. rewrite Z.add_0_r.
    rewrite memory_update_stack.
    rewrite memory_move_iid.
    destruct st. simpl.
    destruct Hrel. auto.
    rewrite maximal_memory_pages_change; auto.
  - rewrite callstack_update_stack, callstack_move_iid.
    rewrite (frame_id_change i Br); simpl; auto.
    rewrite (fid_change i Br); simpl; auto.
    destruct Hrel. auto.
Qed.
