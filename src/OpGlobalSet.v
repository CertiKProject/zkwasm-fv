(* Copyright (C) CertiK 2024-2026 *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETable.
Require MTable.
Require Import Relation RelationHelper.

Require Import OpGlobalSetModel.

(* Proofs about op_global_set.rs. *)

Require Import Wasm.numerics.
Require Import Lia.
Require Import MTable.

Theorem opcode_mops_correct_global_set : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct GlobalSet i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config GlobalSet i)) with 1.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Global >= 1).
  - apply MTable.mtable_write_mops with
      (offset := etable_values idx_cell i)
      (is_i32 := etable_values is_i32_cell i)
      (value := etable_values value_u64_cell i); auto.
    apply (alloc_memory_table_lookup_write_cell_correct _ _ _ _ _ _ _ 
      global_write i Hrange); auto.
    - apply eid_common.
    - apply is_i32_bit.
    - pose(idx_common i); lia.
  lia.
Qed.

Lemma globalset_mops : forall i,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    etable_values (ops_cell GlobalSet) i = 1 ->
    mops_at_correct i ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 1
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with GlobalSet in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i GlobalSet Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).

  assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Global >= 1).
  {
    apply (write_cell_mops _ _ _ _ _ _ _ global_write i Hrange); auto.
    - apply (eid_common i).
    - apply (is_i32_bit).
    - pose (sp_common i).
    - pose (idx_common i); lia.
  }
  lia.
Qed.


Require Import ImageTableModel.
Require Import InjectivityHelper.

Lemma config_opcode_inj_GlobalSet : forall i instr,
    config_opcode (opcode_config GlobalSet i) =
            opcode_of_instruction instr ->
    instr =
    IGlobalSet (Wasm_int.Int32.repr (etable_values idx_cell i)).
Proof.
  intros.
  apply opcode_of_instruction_inj.
  rewrite <- H. clear H.
  unfold opcode_config, config_opcode, opcode_of_instruction.
  f_equal.
  rewrite Wasm_int.Int32.unsigned_repr.
  2: { apply iscommon_is32.
      apply idx_common. }
  reflexivity.
Qed.

Lemma GlobalSet_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->    
  etable_values (ops_cell GlobalSet) i = 1 ->
    program (wasm_pc st) = IGlobalSet (Wasm_int.Int32.repr (etable_values idx_cell i)).
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i GlobalSet Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  apply (config_opcode_inj_GlobalSet _ _ Hopcode).
Qed.

Opaque set_glob.

Lemma value_rel_64 : forall x,
    0 <= x < Wasm_int.Int64.modulus ->
    value_rel x (datatypes.VAL_int64 (Wasm_int.int_of_Z i64m x)).
Proof.
  intros.
  simpl.
  rewrite Wasm_int.Int64.Z_mod_modulus_id.
  auto.
  lia.
Qed.  

Theorem GlobalSet_correct : forall i st idx glbs x v xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell GlobalSet) i = 1 ->
  etable_values idx_cell i = Z.of_nat idx ->
  state_rel i st ->
  value_rel x v ->
  wasm_stack st = (x::xs) ->
  wasm_globals st = glbs ->
  exists glbs',
  (set_glob glbs idx v) = Some glbs'
  /\ state_rel (i+1) (update_globals (update_stack (incr_iid st) xs) glbs').
Proof.
  intros i st idx glbs x v xs Hrange Hrow_enabled Hmops Hop Hidx Hrel Hvalue_rel Hstk Hglbs.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (globalset_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].

  assert (etable_values value_u64_cell i = x).
  {
    eapply stack_rel_read_1_without_value with
      (is_i32 :=(fun get => get is_i32_cell))
      (value := (fun get => get (value_u64_cell)))
      (enable := (fun get => get (ops_cell GlobalSet))); eauto.
    - pose (is_i32_bit i); auto.
    - apply stack_read.
  }
    
  destruct (globals_rel_write  memory_table_lookup_global_write i idx (fun get => get is_i32_cell) (fun get => get (value_u64_cell))  (fun get => get (ops_cell GlobalSet)) (etable_values eid_cell i) x v glbs)
   as [glbs' [Hlbs' Hglbs_rel']]
  ; auto; try lia.
  - pose (is_i32_bit i); auto.
  - rewrite <- Hglbs.  destruct Hrel. auto.
  - apply global_write.
  - { destruct (domain_correct MTableModel.LocationType_Global
                  (etable_values eid_cell i)
                  (Z.of_nat idx)
                  (etable_values is_i32_cell i)
                  (etable_values value_u64_cell i)).
      rewrite <- Hidx.
      apply (alloc_memory_table_lookup_write_cell_correct
                 memory_table_lookup_global_write
                 (fun get => get eid_cell)
                 (fun get => MTableModel.LocationType_Global)
                 (fun get => get idx_cell)
                 (fun get => get is_i32_cell)
                 (fun get => get (value_u64_cell))
                 (fun get => get (ops_cell GlobalSet))
                 global_write
                 i); auto.
      - pose (eid_common i) ; lia.
      - pose (is_i32_bit i); auto.
      - pose (idx_common i); lia.
      - lia.
    }
    - apply (idx_common i).
    exists glbs'.
    split; [assumption |].
    constructor.
    + rewrite pc_update_globals.
      rewrite pc_update_stack_incr_iid.
      rewrite fid_change with (idx := GlobalSet); auto.
      rewrite iid_change with (idx := GlobalSet); auto.
      simpl.
      pose(Hi := pc_incr_iid (update_stack st (etable_values value_u64_cell i :: xs))).
      rewrite pc_update_stack in Hi.
      rewrite incr_iid_update_stack in *.
      destruct Hrel.
      rewrite state_pc_rel in Hi; auto.
    + rewrite eid_change by auto.
      rewrite (sp_change i _ Hrange Hrow_enabled Hop).
      simpl.
      apply state_stack_rel in Hrel.
      rewrite Hstk in Hrel.
      simpl in Hrel.
      destruct Hrel as [_ Hrel'].
      rewrite stack_no_write by auto.
      rewrite stack_update_globals.
      rewrite stack_update_stack_incr_iid.
      destruct st; simpl.
      assumption.
    + rewrite globals_update_globals.
      destruct st; simpl.
      rewrite eid_change by auto.
      assumption.
    + rewrite eid_change by auto.
      rewrite memory_no_write; auto.
      rewrite (mpages_change i GlobalSet) by auto. simpl. rewrite Z.add_0_r.
      rewrite memory_update_globals.
      rewrite memory_update_stack_incr_iid.
      destruct st. simpl.
      destruct Hrel. auto.
      rewrite maximal_memory_pages_change; auto.    
    + rewrite callstack_update_globals, callstack_update_stack, callstack_incr_iid.
      rewrite (frame_id_change i GlobalSet); simpl; auto.
      rewrite (fid_change i GlobalSet); simpl; auto.
      destruct Hrel. auto.
Qed.
