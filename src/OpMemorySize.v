(* Copyright (C) CertiK 2024-2026 *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpMemorySizeModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_memory_size : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct MemorySize i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config MemorySize i)) with 1.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  - apply MTable.mtable_write_mops with
      (offset := etable_values sp_cell i)
      (is_i32 := 1)
      (value := etable_values allocated_memory_pages i); auto.
    apply (alloc_memory_table_lookup_write_cell_correct _ _ _ _ _ _ _ 
      stack_write i Hrange); auto.
    - apply eid_common.
    - pose(sp_common i); lia.
  lia.
Qed.

Require Import ImageTableModel.
Require Import InjectivityHelper.

Lemma MemorySize_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->    
  etable_values (ops_cell MemorySize) i = 1 ->
  program (wasm_pc st) = IMemorySize.
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i MemorySize Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  apply opcode_of_instruction_inj.
  rewrite <- Hopcode.
  reflexivity.
Qed.

Lemma memory_size_mops : forall i,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    etable_values (ops_cell MemorySize) i = 1 ->
    mops_at_correct i ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with MemorySize in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i MemorySize Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).

  assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  {
    apply (write_cell_mops _ _ _ _ _ _ _ stack_write i Hrange); auto.
    - apply (eid_common i).
    - pose (sp_common i); lia.
  }
  lia.
Qed.

Require Import Wasm.operations.

Theorem MemorySizeOp_correct : forall i st xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell MemorySize) i = 1 ->
  state_rel i st ->
  wasm_stack st = xs ->
  state_rel (i+1) (update_stack (incr_iid st) (Z.of_N (mem_size (wasm_memory st)) :: xs)).
Proof.
  intros i st xs Hrange Hrow_enabled Hmops Hop Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (memory_size_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].
  replace (Z.of_N (mem_size (wasm_memory st)))
     with (etable_values mpages_cell i).
  2: {
    eapply heap_size.
    apply state_heap_rel.
    assumption.
  }

  assert (wasm_pc (update_stack (incr_iid st) (etable_values allocated_memory_pages i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := MemorySize); auto.
    rewrite iid_change with (idx := MemorySize); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values allocated_memory_pages i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_negative with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => 1)
                                (value := fun get => get allocated_memory_pages)
                                (enable := fun get => get (ops_cell MemorySize)); auto; try lia.
  - pose(Hsp := sp_change i MemorySize Hrange Hrow_enabled Hop).
    replace(config_sp_diff (opcode_config MemorySize i)) with (-1) in Hsp by constructor.
    lia.
  - pose (mpages_change i MemorySize); simpl in *; lia.        
  - rewrite (frame_id_change i MemorySize); auto; reflexivity.
  - rewrite (fid_change i MemorySize); auto.
  - apply stack_write.
Qed.
