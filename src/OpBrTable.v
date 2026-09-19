(* Copyright (C) CertiK 2024-2026 *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import ImageTableModel.
Require Import OpBrTableModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_br_table : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct BrTable i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config BrTable i)) with (etable_values keep i).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 
    etable_values keep i).
  destruct (keep_bit i) as [Hk | Hk]; rewrite Hk.
  - lia.
  - apply MTable.mtable_write_mops with
      (offset := etable_values sp_cell i + etable_values drop i + 2)
      (is_i32 := etable_values keep_is_i32 i)
      (value := etable_values keep_value i); auto.
    apply (alloc_memory_table_lookup_write_cell_correct _ _ _ _ _ _ _ 
      stack_write_return_value i Hrange); auto.
    - apply eid_common.
    - apply keep_is_i32_bit.
    - pose(sp_common i).
      pose(drop_common i); lia.
    - lia.
  lia.
Qed.

Lemma oob_or_not : forall i,
    0 <= i ->
    etable_values (ops_cell BrTable) i = 1 ->
    (etable_values is_out_of_bound i = 1 /\ etable_values is_not_out_of_bound i = 0) \/
    (etable_values is_out_of_bound i = 0 /\ etable_values is_not_out_of_bound i = 1).
Proof.
  intros i Hrange Hops.
  pose(H := op_br_table_oob i Hrange); simpl in H.
  replace(i+0) with i in H by lia.
  pose(is_out_of_bound_bit i).
  pose(is_not_out_of_bound_bit i).
  lia.
Qed.

Lemma oob_means_expected_index_oob : forall i,
    0 <= i ->
    etable_values (ops_cell BrTable) i = 1 ->
    etable_values is_out_of_bound i = 1 ->
    etable_values expected_index i >= etable_values targets_len i.
Proof.
  intros i Hrange Hops Hoob.
  pose(H := op_br_table_oob i Hrange); simpl in H.
  replace(i+0) with i in H by lia.
  pose(diff_U64 i).
  lia.
Qed.

Lemma not_oob_means_expected_index_not_oob : forall i,
    0 <= i ->
    etable_values (ops_cell BrTable) i = 1 ->
    etable_values is_not_out_of_bound i = 1 ->
    etable_values expected_index i < etable_values targets_len i.
Proof.
  intros i Hrange Hops Hnoob.
  pose(H := op_br_table_oob i Hrange); simpl in H.
  replace(i+0) with i in H by lia.
  pose(diff_U64 i).
  lia.
Qed.

Lemma effective_index_value_oob : forall i,
    0 <= i ->
    etable_values (ops_cell BrTable) i = 1 ->
    etable_values is_out_of_bound i = 1 ->
    etable_values effective_index i = etable_values targets_len i - 1.
Proof.
  intros i Hrange Hops Hoob.
  pose(H := op_br_table_effective_index_gate i Hrange); simpl in H.
  replace(i+0) with i in H by lia.
  lia.
Qed.

Lemma effective_index_value_noob : forall i,
    0 <= i ->
    etable_values (ops_cell BrTable) i = 1 ->
    etable_values is_not_out_of_bound i = 1 ->
    etable_values effective_index i = etable_values expected_index i.
Proof.
  intros i Hrange Hops Hnoob.
  pose(H := op_br_table_effective_index_gate i Hrange); simpl in H.
  replace(i+0) with i in H by lia.
  lia.
Qed.

Lemma br_table_lookup_argument : forall i,
    0 <= i ->
    etable_values (ops_cell BrTable) i = 1 ->
    etable_values br_table_lookup i = encode_br_table_entry
      (etable_values fid_cell i)
      (etable_values iid_cell i)
      (etable_values effective_index i)
      (etable_values drop i)
      (etable_values keep i)
      (etable_values dst_iid i).
Proof.
  intros i Hrange Hops.
  pose(H := op_br_table_br_table_lookup i Hrange); simpl in H.
  replace(i+0) with i in H by lia.
  lia.
Qed.


Require Import ImageTableModel.
Require Import InjectivityHelper.


Lemma Br_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->    
  etable_values (ops_cell BrTable) i = 1 ->
  program (wasm_pc st) = IBrTable (Wasm_int.Int32.repr (etable_values targets_len i))
  /\ exists entries e,
      br_tables (wasm_pc st) = Some entries 
      /\  Z.of_nat (List.length entries) = (etable_values targets_len i)
      /\  ((etable_values expected_index i < etable_values targets_len i /\(etable_values effective_index i) = (etable_values expected_index i)
                                                                                                                  \/ (etable_values expected_index i >= etable_values targets_len i /\ (etable_values effective_index i) = (etable_values targets_len i - 1))))
      /\  List.nth_error entries (Z.to_nat (etable_values effective_index i)) = Some e
      /\  Wasm_int.Int32.unsigned (br_table_drop e) = etable_values drop i 
      /\  Z_of_bool (br_table_keep e) = etable_values keep i 
      /\  Wasm_int.Int32.unsigned (br_table_dst_pc e) = etable_values dst_iid i 
.
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  assert (Hinstruction : program (etable_values fid_cell i, etable_values iid_cell i) =
  IBrTable (Wasm_int.Int32.repr (etable_values targets_len i)) ).
  {  
     destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
                as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
     rewrite (itable_lookup_encode i BrTable Hrange Henabled Hops) in Hencode.
     apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
     destruct Hencode as [Hfid [Hid Hopcode]].
     subst.
     apply opcode_of_instruction_inj.
     rewrite <- Hopcode.
     unfold opcode_of_instruction.
     unfold config_opcode, opcode_config.
     f_equal.
     rewrite  common_unsigned_repr by (apply targets_len_common).
     reflexivity.
  }

  assert (Hindex : ((etable_values expected_index i < etable_values targets_len i /\(etable_values effective_index i) = (etable_values expected_index i)
                                                                                                                  \/ (etable_values expected_index i >= etable_values targets_len i /\(etable_values effective_index i) = (etable_values targets_len i - 1))))).
  {
    destruct (oob_or_not i Hrange Hops) as [[Hoob Hnot_oob] | [Hoob Hnot_oob]].
    - right. split.
      + apply oob_means_expected_index_oob; eauto.
      + apply effective_index_value_oob; eauto.        
    - left. split.
      + apply not_oob_means_expected_index_not_oob; eauto.
      + apply effective_index_value_noob; eauto.
  }
  
  split; [apply Hinstruction|].

  destruct (br_table_encoding _ _ _ Hinstruction) as [entries [Hentries [Hlen Hentry]]].
  rewrite common_unsigned_repr in Hlen by (apply targets_len_common).


  assert (effective_index_bound :  0 <= etable_values effective_index i <
           Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (etable_values targets_len i))).
  {
    pose (effective_index_common i).
    split; [lia|].
    destruct Hindex as [[Hindex1 Hindex2] | [Hindex1 Hindex2]].
    - rewrite  common_unsigned_repr by (apply targets_len_common).
      lia.
    - rewrite  common_unsigned_repr by (apply targets_len_common).
      lia.
  }      
  specialize (Hentry (etable_values effective_index i) effective_index_bound).
  destruct Hentry as [e [Hentry1 Hentry2]].
  exists entries. exists e.
  split; [assumption|].
  split; [assumption|].
  split; [assumption|].
  split; [assumption|].

  assert (Hlookup_cell := op_br_table_br_table_lookup i Hrange).
  simpl in Hlookup_cell.
  replace (i+0) with i in Hlookup_cell by lia.
  rewrite Hops in Hlookup_cell.

  assert (Hlookup := brtable_lookup_in_brtable i Hrange Henabled).
  replace ( etable_values br_table_lookup i)
            with ( encode_br_table_entry (etable_values fid_cell i) (etable_values iid_cell i)
                    (etable_values effective_index i) (etable_values drop i) 
                    (etable_values keep i) (etable_values dst_iid i))
    in Hlookup by lia.
  clear Hlookup_cell.
  assert (Hentry3: encode_br_table_entry (etable_values fid_cell i) (etable_values iid_cell i) (etable_values effective_index i) (etable_values drop i) (etable_values keep i) (etable_values dst_iid i)
         = (encode_BrTableEntry e (etable_values fid_cell i ) (etable_values  iid_cell i) (etable_values effective_index i))).
  {
    unfold in_brtable, encode_BrTableEntry in Hentry2.
    destruct Hentry2 as [j Hentry2]. symmetry in Hentry2.
    destruct Hlookup as [j' Hlookup]. symmetry in Hlookup.
    assert (Hunique:= br_table_unique j j' _ _ _ _ _ _ _ _ _ Hentry2 Hlookup).
    subst j'.
    unfold encode_BrTableEntry.
    congruence.
  }
  apply encode_BrTableEntry_inj in Hentry3; auto using iscommon_is_2_32, fid_common, iid_common, effective_index_common, drop_common, dst_iid_common, isbit_iscommon, keep_bit.
  lia.
Qed.

Lemma br_table_mops : forall i,
    0 <= i ->
    etable_values eid_cell i > 0 ->
    etable_values enabled_cell i = 1 ->
    etable_values (ops_cell BrTable) i = 1 ->
    mops_at_correct i ->
    (etable_values keep i = 1 ->
        mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0) /\
    (etable_values keep i = 0 ->
        mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 0
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0).
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with BrTable in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i BrTable Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  split.
  - intros Hkc.
    assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
    {
      apply (write_cell_mops _ _ _ _ _ _ _ stack_write_return_value i Hrange); auto.
      - apply (eid_common i).
      - apply (keep_is_i32_bit i).
      - pose (sp_common i).
        pose (drop_common i).
        lia.
      - lia.
    }
  lia.
  - intros Hkc.
    lia.
Qed.

Theorem BrTable_branch_no_keep_correct : forall i st xid xd xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell BrTable) i = 1 ->
  state_rel i st ->
  wasm_stack st = xid :: xd ++ xs ->
  length xd = Z.to_nat (etable_values drop i) ->
  etable_values keep i = 0 ->
  etable_values expected_index i = xid /\ state_rel (i+1) (update_stack (move_to_iid st (etable_values dst_iid i)) xs).
Proof.
  intros i st xid xd xs Hrange Henabled Hmops Hops Hrel Hstk Hdrop Hkeep.
  assert (Heid := eid_nonzero i Hrange Henabled).
  apply (br_table_mops) in Hmops; auto.
  destruct Hmops as [_ Hmops].

  assert (Hc: etable_values expected_index i = xid).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => 1)
                                 (enable := fun get => get (ops_cell BrTable))
                                 (value := fun get => get expected_index); auto.
    - eauto.
    - eauto.
    - apply stack_read_index.
  }

  split; [exact Hc|].
  
  destruct Hmops as [Hmops [Hmops' Hmops'']]; auto.

  constructor.
  - rewrite iid_change with (idx := BrTable); auto.
    rewrite fid_change with (idx := BrTable); auto.
    simpl.
    pose(H := pc_move_iid (update_stack st xs) (etable_values dst_iid i)).
    rewrite pc_update_stack in H.
    destruct Hrel.
    rewrite state_pc_rel in H.
    rewrite pc_update_stack.
    rewrite move_iid_update_stack in H; auto.
  - rewrite eid_change by auto.
    rewrite sp_change with (idx := BrTable); auto.
    change (config_sp_diff (opcode_config BrTable i)) with
      (1 + etable_values drop i).
    apply state_stack_rel in Hrel.
    rewrite Hstk in Hrel.
    simpl in Hrel.
    destruct Hrel as [_ Hrel'].
    eapply stack_rel_drop with 
      (i:= i) 
      (n:= Z.to_nat (etable_values drop i)) in Hrel'; auto.
    rewrite Z2Nat.id in Hrel'.
    rewrite stack_update_stack.
    replace (etable_values sp_cell i + (1 + etable_values drop i) + 1)
      with (etable_values sp_cell i + 1 + 1 + etable_values drop i) by lia.
    assumption.
    apply drop_common.
  - rewrite globals_update_stack.
    rewrite globals_move_iid.
    rewrite eid_change by auto.
    rewrite globals_no_write; auto.
    destruct Hrel; auto.
  - rewrite eid_change by auto.
    rewrite memory_no_write; auto.
    rewrite (mpages_change i BrTable) by auto. simpl. rewrite Z.add_0_r.
    rewrite memory_update_stack.
    rewrite memory_move_iid.
    destruct st. simpl.
    destruct Hrel. auto.
    rewrite maximal_memory_pages_change; auto.
  - rewrite callstack_update_stack, callstack_move_iid.
    rewrite (frame_id_change i BrTable); simpl; auto.
    rewrite (fid_change i BrTable); simpl; auto.
    destruct Hrel. auto.
Qed.

Theorem BrTable_branch_and_keep_correct : forall i st xid xv xd xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell BrTable) i = 1 ->
  state_rel i st ->
  wasm_stack st = xid :: xv :: xd ++ xs ->
  length xd = Z.to_nat (etable_values drop i) ->
  etable_values keep i = 1 ->
  etable_values expected_index i = xid /\ state_rel (i+1) (update_stack (move_to_iid st (etable_values dst_iid i)) (xv :: xs)).
Proof.
  intros i st xid xv xd xs Hrange Henabled Hmops Hops Hrel Hstk Hdrop Hkeep.
  assert (Heid := eid_nonzero i Hrange Henabled).
  apply (br_table_mops) in Hmops; auto.
  destruct Hmops as [Hmops _].

  assert (Hc: etable_values expected_index i = xid).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => 1)
                                 (enable := fun get => get (ops_cell BrTable))
                                 (value := fun get => get expected_index); auto.
    - eauto.
    - eauto.
    - apply stack_read_index.
  }

  split; [exact Hc|].
  
  destruct Hmops as [Hmops [Hmops' Hmops'']]; auto.

  assert (Hv: etable_values keep_value i = xv).
  {
    eapply stack_rel_read_2_without_value with (is_i32 := fun get => get keep_is_i32)
                                 (enable := fun get => 
                                  get (ops_cell BrTable) * get keep)
                                 (value := fun get => get keep_value); auto.
    - lia.
    - apply(keep_is_i32_bit i).
    - eauto.
    - eauto.
    - apply stack_read_return_value.
  }
  rewrite <- Hv.

  constructor.
  - rewrite iid_change with (idx := BrTable); auto.
    rewrite fid_change with (idx := BrTable); auto.
    simpl.
    pose(H := pc_move_iid (update_stack st xs) (etable_values dst_iid i)).
    rewrite pc_update_stack in H.
    destruct Hrel.
    rewrite state_pc_rel in H.
    rewrite pc_update_stack.
    rewrite move_iid_update_stack in H; auto.
  - rewrite eid_change by auto.
    rewrite sp_change with (idx := BrTable); auto.
    change (config_sp_diff (opcode_config BrTable i)) with
      (1 + etable_values drop i).
    apply state_stack_rel in Hrel.
    rewrite Hstk in Hrel.
    simpl in Hrel.
    destruct Hrel as [_ [_ Hrel']].
    replace(etable_values sp_cell i + 1 + 1 + 1) with
      (etable_values sp_cell i + 2 + 1) in Hrel' by lia.
    replace(etable_values sp_cell i + (1 + etable_values drop i) + 1) with
      (etable_values sp_cell i + 2 + etable_values drop i) by lia.
    rewrite stack_update_stack.
    pose(drop_common i).
    rewrite <- (Z2Nat.id (etable_values drop i)) by lia.
    eapply stack_rel_write_without_value_large_drop with
      (value:= (fun get => get (keep_value)))
      (enable:= (fun get => get (ops_cell BrTable) * (get keep)))
      (is_i32:= (fun get => get keep_is_i32))
      (offset:= (fun get => get sp_cell + get drop + 2)); eauto; try lia.
    - apply(keep_is_i32_bit).
    - apply stack_write_return_value.
  - rewrite globals_update_stack.
    rewrite globals_move_iid.
    rewrite eid_change by auto.
    rewrite globals_no_write; auto.
    destruct Hrel; auto.
  - rewrite eid_change by auto.
    rewrite memory_no_write; auto.
    rewrite (mpages_change i BrTable) by auto. simpl. rewrite Z.add_0_r.
    rewrite memory_update_stack.
    rewrite memory_move_iid.
    destruct st. simpl.
    destruct Hrel. auto.
    rewrite maximal_memory_pages_change; auto.
  - rewrite callstack_update_stack, callstack_move_iid.
    rewrite (frame_id_change i BrTable); simpl; auto.
    rewrite (fid_change i BrTable); simpl; auto.
    destruct Hrel. auto.    
Qed.
