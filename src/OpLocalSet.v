(* Copyright (C) CertiK 2024-2026 *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpLocalSetModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_local_set : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct LocalSet i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config LocalSet i)) with 1.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  - apply MTable.mtable_write_mops with
      (offset := etable_values sp_cell i + 1 + etable_values offset_cell i)
      (is_i32 := etable_values is_i32_cell i)
      (value := etable_values value_cell i); auto.
    apply (alloc_memory_table_lookup_write_cell_correct _ _ _ _ _ _ _ 
      stack_write i Hrange); auto.
    - apply eid_common.
    - apply is_i32_bit.
    - pose(sp_common i).
      pose(offset_common i); lia.
  lia.
Qed.

Lemma localset_mops : forall i,
    0 <= i ->
    etable_values eid_cell i > 0 ->
    etable_values enabled_cell i = 1 ->
    etable_values (ops_cell LocalSet) i = 1 ->
    mops_at_correct i ->
        mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with LocalSet in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i LocalSet Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).

  assert (mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  {
    apply (write_cell_mops _ _ _ _ _ _ _ stack_write i Hrange); auto.
    - apply (eid_common i).
    - apply (is_i32_bit).
    - pose (sp_common i).
    - pose (sp_common i).
      pose (offset_common i).
      lia.
  }
  lia.
Qed.

Require Import ImageTableModel.
Require Import InjectivityHelper.
  
Lemma config_opcode_inj_LocalSet : forall i instr,
    config_opcode (opcode_config LocalSet i) =
            opcode_of_instruction instr ->
    instr =
    ILocalSet (bool_of_Z (etable_values is_i32_cell i)) (Wasm_int.Int32.repr (etable_values offset_cell i)).
Proof.
  intros.
  apply opcode_of_instruction_inj.
  rewrite <- H. clear H.
  unfold opcode_config, config_opcode, opcode_of_instruction.
  rewrite <- !Zplus_assoc.
  f_equal.
  rewrite bool_of_Z_simpl.
  2: { apply is_i32_bit. }
  rewrite CommonData.shiftl_1_n.
  2: { cbv - [ Z.le ] ; lia. }
  f_equal.
  rewrite Wasm_int.Int32.unsigned_repr.
  2: { apply iscommon_is32.
      apply offset_common. }
  reflexivity.
Qed.

Lemma LocalSet_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->    
  etable_values (ops_cell LocalSet) i = 1 ->
    program (wasm_pc st) = ILocalSet (bool_of_Z (etable_values is_i32_cell i)) (Wasm_int.Int32.repr (etable_values offset_cell i)).
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i LocalSet Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  apply (config_opcode_inj_LocalSet _ _ Hopcode).
Qed.

Theorem LocalSetOp_correct : forall i st y ys x xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell LocalSet) i = 1 ->
  state_rel i st ->
  wasm_stack st = y :: ys ++ x :: xs ->
  (etable_values offset_cell i) > 1 ->
  length ys =  (Z.to_nat (etable_values offset_cell i) - 1)%nat ->
  state_rel (i+1) (update_stack (incr_iid st) (ys ++ y :: xs)).
Proof.
  intros i st y ys x xs Hrange Hrow_enabled Hmops Hop_class Hrel Hstk Hgt1 Hnth.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (localset_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hy : etable_values value_cell i = y).
  {
    apply stack_rel_read_1_without_value with
      (st := st)
      (stk := ys ++ x :: xs)
      (col := memory_table_lookup_stack_read)
      (is_i32 :=  (fun get => get is_i32_cell))
      (value :=     (fun get => get value_cell))
      (enable := (fun get => get (ops_cell LocalSet))); auto.
    - pose (is_i32_bit i). auto.
    - apply stack_read.
  }
  assert (Hstack_rel': stack_rel (stk_map (etable_values eid_cell i + 1))
                                 (etable_values sp_cell i + 1)
                                 (y :: ys ++ y :: xs)).
  {
    replace (y::xs) with  (etable_values value_cell i ::xs) by congruence.
    eapply stack_rel_write_without_value_large with 
      (value := (fun get => get value_cell))
      (v := x)
      (stk1 := y::ys) (stk2 := xs)
      (is_i32 :=  (fun get => get is_i32_cell))
      (offset :=  (fun get => get sp_cell + 1 + get offset_cell))
      (enable := (fun get => get (ops_cell LocalSet)))
    ; auto.
    - simpl. rewrite Hnth.
      pose (offset_common i).
      lia.
    - pose (is_i32_bit i); lia.
    - destruct Hrel.
      rewrite Hstk in state_stack_rel.
      exact state_stack_rel.
    - replace (length (y::ys)) with (length ys + 1)%nat by (simpl;lia).
      rewrite Hnth.
      lia.
    - apply stack_write.
  }
      
  constructor.
  - rewrite fid_change with (idx := LocalSet); auto.
    rewrite iid_change with (idx := LocalSet); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (ys ++ y :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.
  - replace (etable_values eid_cell (i + 1)) with (etable_values eid_cell i + 1) by (rewrite eid_change; auto).
    replace (etable_values sp_cell (i + 1)) with (etable_values sp_cell i + 1) by (rewrite (sp_change i LocalSet); simpl; lia).
    destruct Hstack_rel' as [_ Hstack_rel'].
    rewrite stack_update_stack.
    exact Hstack_rel'.
  - rewrite globals_update_stack.
    replace (etable_values eid_cell (i + 1)) with (etable_values eid_cell i + 1) by (rewrite eid_change; auto).
    rewrite globals_no_write by auto.
    rewrite globals_incr_iid.
    destruct Hrel; auto.
  - rewrite memory_update_stack.
    replace (etable_values eid_cell (i + 1)) with (etable_values eid_cell i + 1) by (rewrite eid_change; auto).
    rewrite memory_no_write by auto.
    rewrite (mpages_change i LocalSet) by auto.
    simpl.
    rewrite Z.add_0_r.
    rewrite memory_incr_iid.
    destruct Hrel; auto.
    rewrite maximal_memory_pages_change; auto.
  - rewrite callstack_update_stack, callstack_incr_iid.
    rewrite (frame_id_change i LocalSet); simpl; auto.
    rewrite (fid_change i LocalSet); simpl; auto.
    destruct Hrel; auto.
Qed.    
