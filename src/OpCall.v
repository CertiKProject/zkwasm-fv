(* Copyright (C) CertiK 2024-2026 *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import Relation RelationHelper.
Require Import JTableModel JTable.
Require Import ETable.

Require Import OpCallModel.

(* Proofs about op_call.rs. *)

Require Import Wasm.numerics.
Require Import Lia.
Require Import MTable.

Theorem opcode_mops_correct_call : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Call i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config Call i)) with 0.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  lia.
Qed.

Lemma call_mops : forall i,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    etable_values (ops_cell Call) i = 1 ->
    mops_at_correct i ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with Call in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i Call Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).
  lia.
Qed.



Require Import ImageTableModel.
Require Import InjectivityHelper.
  
Lemma config_opcode_inj_Call : forall i instr,
    config_opcode (opcode_config Call i) =
            opcode_of_instruction instr ->
    instr =
    ICall (Wasm_int.Int32.repr (etable_values index_cell i)).
Proof.
  intros.
  apply opcode_of_instruction_inj.
  rewrite <- H. clear H.
  unfold opcode_config, config_opcode, opcode_of_instruction.
  f_equal.
  rewrite CommonData.shiftl_1_n.
  2: { cbv - [ Z.le ] ; lia. }
  f_equal.
  rewrite Wasm_int.Int32.unsigned_repr.
  2: { apply iscommon_is32.
      apply index_common. }
  reflexivity.
Qed.

Lemma Call_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->    
  etable_values (ops_cell Call) i = 1 ->
    program (wasm_pc st) = ICall (Wasm_int.Int32.repr (etable_values index_cell i)).
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i Call Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  apply (config_opcode_inj_Call _ _ Hopcode).
Qed.

Theorem Call_correct : forall i st,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Call) i = 1 ->
  state_rel i st ->
  state_rel (i+1) (update_callstack (move_to_label st (etable_values index_cell i, 0))
                     ((fst (wasm_pc st), snd (wasm_pc st) + 1) :: wasm_callstack st)).
Proof.
  intros i st Hrange Hrow_enabled Hmops Hop Hrel.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (call_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  replace (fst (wasm_pc st), snd (wasm_pc st) + 1)
    with (etable_values fid_cell i, etable_values iid_cell i + 1).
  2: {
    destruct Hrel.
    rewrite state_pc_rel.
    reflexivity. }
  constructor.
  - rewrite iid_change with (idx := Call); auto.
    rewrite fid_change with (idx := Call); auto.
    simpl.
    rewrite pc_update_callstack, pc_move_label.
    reflexivity.
  - rewrite eid_change by auto.
    rewrite sp_change with (idx := Call); auto.
    change (config_sp_diff (opcode_config Call i)) with 0.
    replace (etable_values sp_cell i + 0 + 1) with (etable_values sp_cell i + 1) by lia.
    rewrite stack_update_callstack, stack_move_label.
    rewrite stack_no_write; auto.
    destruct Hrel; auto.
  - rewrite globals_update_callstack, globals_move_label.
    rewrite eid_change by auto.
    rewrite globals_no_write; auto.
    destruct Hrel; auto.
  - rewrite eid_change by auto.
    rewrite memory_no_write; auto.
    rewrite (mpages_change i Call) by auto. simpl. rewrite Z.add_0_r.
    rewrite memory_update_callstack, memory_move_label.
    rewrite maximal_memory_pages_change; auto.
    destruct Hrel. auto.
  - rewrite callstack_update_callstack.
    rewrite (frame_id_change i Call); simpl; auto.
    rewrite (fid_change i Call); simpl; auto.
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
        rewrite itable_lookup_encode with (idx:=Call) in Hlookup; try lia; auto.
        refine (call_iid_small _ _ _ _ _ _ Hlookup _).
        pose (fid_common i); lia.
        pose (iid_common i); lia.
        left. reflexivity.
    }
    split.
    + replace (encode_frame_table_entry
                  (etable_values eid_cell i)
                  (etable_values frame_id_cell i)
                  (etable_values index_cell i)
                  (etable_values fid_cell i) (etable_values iid_cell i + 1))
        with (etable_values frame_table_lookup i).
      2: {
        destruct (return_frame_table_lookup i Hrange) as [Hgate _].
        replace (i+0) with i in * by lia.
        simpl in Hgate.
        lia.
      }
      apply c8c; auto.
    + destruct Hrel; auto.
Qed.
