(* Copyright (C) CertiK 2024-2026 *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETable.
Require MTable.
Require Import Relation RelationHelper.

Require Import OpGlobalGetModel.

(* Proofs about op_global_get.rs. *)

Require Import Wasm.numerics.
Require Import Lia.
Require Import MTable.

Theorem opcode_mops_correct_global_get : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct GlobalGet i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config GlobalGet i)) with 1.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  - apply MTable.mtable_write_mops with
      (offset := etable_values sp_cell i)
      (is_i32 := etable_values is_i32_cell i)
      (value := etable_values value_u64_cell i); auto.
    apply (alloc_memory_table_lookup_write_cell_correct _ _ _ _ _ _ _ 
      stack_write i Hrange); auto.
    - apply eid_common.
    - apply is_i32_bit.
    - pose(sp_common i); lia.
  lia.
Qed.

Lemma globalget_mops : forall i,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    etable_values (ops_cell GlobalGet) i = 1 ->
    mops_at_correct i ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with GlobalGet in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i GlobalGet Hrow_enabled)); auto.
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

Require Import ImageTableModel.
Require Import InjectivityHelper.

Lemma config_opcode_inj_GlobalGet : forall i instr,
    config_opcode (opcode_config GlobalGet i) =
            opcode_of_instruction instr ->
    instr =
    IGlobalGet (Wasm_int.Int32.repr (etable_values idx_cell i)).
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

Lemma GlobalGet_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->    
  etable_values (ops_cell GlobalGet) i = 1 ->
    program (wasm_pc st) = IGlobalGet (Wasm_int.Int32.repr (etable_values idx_cell i)).
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i GlobalGet Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  apply (config_opcode_inj_GlobalGet _ _ Hopcode).
Qed.

Theorem GlobalGet_correct : forall i st idx xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell GlobalGet) i = 1 ->
  etable_values idx_cell i = Z.of_nat idx ->
  state_rel i st ->
  wasm_stack st = xs ->
  exists x v,
    glob_val (wasm_globals st) idx = Some v
  /\ value_rel x v
  /\ x = etable_values value_u64_cell i
  /\ state_rel (i+1) (update_stack (incr_iid st) (x :: xs)).
Proof.
  intros i st idx xs Hrange Hrow_enabled Hmops Hop Hidx Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (globalget_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hvalue_rel : exists v,
      glob_val (wasm_globals st) (Z.to_nat (etable_values idx_cell i)) = Some v
      /\ value_rel (etable_values value_u64_cell i) v).
  {
    apply (globals_rel_read  memory_table_lookup_global_read
             _
             (fun get => get idx_cell)
             (fun get => get is_i32_cell)
             (fun get => get (value_u64_cell))
             (fun get => get (ops_cell GlobalGet))); simpl; auto.
    - pose (idx_common i); lia.
    - pose (is_i32_bit i); lia.
    - apply global_read.
  }
  destruct Hvalue_rel as [v Hvalue_rel].
  exists  (etable_values value_u64_cell i).
  exists v.
  rewrite Hidx, Nat2Z.id in Hvalue_rel.
  destruct Hvalue_rel.
  split; [|split; [|split]]; auto.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values value_u64_cell i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := GlobalGet); auto.
    rewrite iid_change with (idx := GlobalGet); auto.
    simpl.
    pose(Hi := pc_incr_iid (update_stack st (etable_values value_u64_cell i :: xs))).
    rewrite pc_update_stack in Hi.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in Hi; auto.

  apply stack_rel_write_negative with
    (col := memory_table_lookup_stack_write)
    (is_i32 := fun get => get is_i32_cell)
    (value := fun get => get value_u64_cell)
    (enable := fun get => get (ops_cell GlobalGet)); simpl; auto.
  - pose (is_i32_bit i); lia.
  - apply (sp_change i GlobalGet); auto.
  - pose (mpages_change i GlobalGet); simpl in *; lia.
  - rewrite (frame_id_change i GlobalGet); auto; reflexivity.
  - rewrite (fid_change i GlobalGet); auto.
  - apply stack_write.
Qed.
