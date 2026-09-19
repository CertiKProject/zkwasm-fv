(* Copyright (C) CertiK 2024-2026 *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import Relation RelationHelper.
Require Import JTableModel JTable.
Require Import ETable.

Require Import OpCallIndirectModel.

(* Proofs about op_call_indirect.rs. *)

Require Import Wasm.numerics.
Require Import Lia.
Require Import MTable.

Lemma table_index_value : forall i,
    0 <= i ->
    etable_values (ops_cell CallIndirect) i = 1 ->
    etable_values table_index i = 0.
Proof.
  intros i Hrange Hops.
  pose(H := table_index_gate i Hrange); simpl in H.
  replace(i+0) with i in H by lia.
  lia.
Qed.

Theorem opcode_mops_correct_callindirect : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct CallIndirect i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config CallIndirect i)) with 0.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  lia.
Qed.

Lemma call_mops : forall i,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    etable_values (ops_cell CallIndirect) i = 1 ->
    mops_at_correct i ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with CallIndirect in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i CallIndirect Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).
  lia.
Qed.

Require Import ImageTableModel.
Require Import InjectivityHelper.

Lemma CallIndirect_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->    
  etable_values (ops_cell CallIndirect) i = 1 ->
  program (wasm_pc st) = ICallIndirect (Wasm_int.Int32.repr (etable_values type_index i))
  /\ exists e,
    module_table_entries e
    /\ entry_table_idx e = Wasm_int.Int32.repr 0
    /\ entry_type_id e = (Wasm_int.Int32.repr (etable_values type_index i))
    /\ entry_offset e =  (Wasm_int.Int32.repr (etable_values offset i))
    /\ entry_func_idx e =  (Wasm_int.Int32.repr (etable_values func_index i)).
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  assert (Hinstruction : program (etable_values fid_cell i, etable_values iid_cell i) =
                           ICallIndirect (Wasm_int.Int32.repr (etable_values op_call_indirect_type_index i))).
  {  
     destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
                as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
     rewrite (itable_lookup_encode i CallIndirect Hrange Henabled Hops) in Hencode.
     apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
     destruct Hencode as [Hfid [Hid Hopcode]].
     subst.
     apply opcode_of_instruction_inj.
     rewrite <- Hopcode.
     unfold opcode_of_instruction.
     unfold config_opcode, opcode_config.
     f_equal.
     rewrite  common_unsigned_repr by (apply type_index_common).
     rewrite !Z.shiftl_mul_pow2 by (change OPCODE_ARG0_SHIFT with 96; lia).
     lia.
  }

  split; [assumption|].

  assert (Hlookup := op_call_indirect_elem_table_lookup  i Hrange).
  simpl in Hlookup.
  replace (i+0) with i in Hlookup by lia.
  rewrite Hops in Hlookup.
  assert (Hin_brtable := brtable_lookup_in_brtable i Hrange Henabled).
  replace ( etable_values elem_lookup i ) with
    (encode_elem_entry (etable_values table_index i) (etable_values type_index i)
       (etable_values offset i) (etable_values func_index i))
    in Hin_brtable by lia.
  clear Hlookup.
  apply module_table_encoding in Hin_brtable.

  eexists.
  split; [exact Hin_brtable|].
  simpl.
  split.
  {
    rewrite table_index_value by auto.
    reflexivity.
  }
  { repeat split; reflexivity. }
Qed.

Theorem CallIndirect_correct : forall i st x xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell CallIndirect) i = 1 ->
  state_rel i st ->
  wasm_stack st = (x::xs) ->
  etable_values offset i = x /\
  state_rel (i+1) (update_callstack (move_to_label (update_stack st xs) (etable_values func_index i, 0))
                                    ((etable_values fid_cell i, etable_values iid_cell i + 1) :: (wasm_callstack st))).
Proof.
  intros i st x xs Hrange Hrow_enabled Hmops Hop Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (call_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].

  assert (Hc: etable_values offset i = x).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => 1)
                                 (enable := fun get => get (ops_cell CallIndirect))
                                 (value := fun get => get offset); auto.
    - eauto.
    - eauto.
    - apply stack_read.
  }

  split; [exact Hc|].
  
  constructor.
  - rewrite iid_change with (idx := CallIndirect); auto.
    rewrite fid_change with (idx := CallIndirect); auto.
    simpl.
    rewrite pc_update_callstack, pc_move_label.
    reflexivity.
  - rewrite eid_change by auto.
    rewrite sp_change with (idx := CallIndirect); auto.
    change (config_sp_diff (opcode_config CallIndirect i)) with 1.
    rewrite stack_update_callstack, stack_move_label.
    rewrite stack_no_write; auto.
    destruct Hrel.
    rewrite Hstk in state_stack_rel.
    rewrite stack_update_stack.
    destruct state_stack_rel as [_ ?]; auto.
  - rewrite globals_update_callstack, globals_move_label.
    rewrite eid_change by auto.
    rewrite globals_no_write; auto.
    rewrite globals_update_stack.
    destruct Hrel; auto.
  - rewrite eid_change by auto.
    rewrite memory_no_write; auto.
    rewrite (mpages_change i CallIndirect) by auto. simpl. rewrite Z.add_0_r.
    rewrite memory_update_callstack, memory_move_label.
    rewrite maximal_memory_pages_change; auto.
    rewrite memory_update_stack.
    destruct Hrel. auto.
  - rewrite callstack_update_callstack.
    simpl.
    rewrite (frame_id_change i CallIndirect); simpl; auto.
    rewrite (fid_change i CallIndirect); simpl; auto.

    split.
    { pose (eid_common i); lia. }
    exists (etable_values frame_id_cell i).
    split.
    { pose (frame_id_common i); lia. }
    split.
    { pose (fid_common i); lia. }
    split.
    {
        assert (Hlookup : ImageTableModel.in_itable  (etable_values itable_lookup_cell i)).
        {
          unfold in_itable.
          apply itable_lookup_in_itable; auto.
        }
        rewrite itable_lookup_encode with (idx:=CallIndirect) in Hlookup; try lia; auto.
        refine (call_iid_small _ _ _ _ _ _ Hlookup _).
        pose (fid_common i); lia.
        pose (iid_common i); lia.
        right. reflexivity.
    }
    split.
    + replace (encode_frame_table_entry
                  (etable_values eid_cell i)
                  (etable_values frame_id_cell i)
                  (etable_values func_index i)
                  (etable_values fid_cell i) (etable_values iid_cell i + 1))
        with (etable_values frame_table_lookup i).
      2: {
        destruct (return_frame_table_lookup i Hrange) as [Hgate _].
        replace (i+0) with i in * by lia.
        simpl in Hgate.
        lia.
      }
      apply c8c; auto.
      destruct Hrel; auto.
Qed.
