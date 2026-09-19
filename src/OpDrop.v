(* Copyright (C) CertiK 2024-2026 *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_drop : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Drop i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config Drop i)) with 0.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).
  lia.
Qed.

Lemma drop_mops : forall i,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    etable_values (ops_cell Drop) i = 1 ->
    mops_at_correct i ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with Drop in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i Drop Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  lia.
Qed.

Require Import ImageTableModel.
Require Import InjectivityHelper.

Lemma config_opcode_inj_Drop : forall i instr,
    config_opcode (opcode_config Drop i) = opcode_of_instruction instr ->
    instr = IDrop.
Proof.
  intros.
  apply opcode_of_instruction_inj.
  rewrite <- H. clear H.
  reflexivity.
Qed.

Lemma drop_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->    
  etable_values (ops_cell Drop) i = 1 ->
  program (wasm_pc st) = IDrop.
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i Drop Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  rewrite (config_opcode_inj_Drop _ _ Hopcode).
  reflexivity.
Qed.  
  
Theorem DropOp_correct : forall i st x1 xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Drop) i = 1 ->
  state_rel i st ->
  wasm_stack st = x1::xs ->
  state_rel (i+1) (update_stack (incr_iid st) xs).
Proof.
  intros i st x1 xs Hrange Hrow_enabled Hmops Hop Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (drop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  eapply stack_rel_drop_1; auto; try lia.
  - apply Hstk.
  - pose(Hsp := sp_change i Drop Hrange Hrow_enabled Hop).
    replace(config_sp_diff (opcode_config Drop i)) with 1 in Hsp by constructor.
    auto.
  - pose (mpages_change i Drop); simpl in *; lia.
  - apply frame_id_change with (idx := Drop); auto.
  - apply fid_change with (idx := Drop); auto.
  - rewrite fid_change with (idx := Drop); auto.
    rewrite iid_change with (idx := Drop); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st xs)).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.
Qed.
