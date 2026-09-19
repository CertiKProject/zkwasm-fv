(* Copyright (C) CertiK 2024-2026 *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpTestModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_test : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Test i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config Test i)) with 1.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  - apply MTable.mtable_write_mops with
      (offset := etable_values sp_cell i + 1)
      (is_i32 := 1)
      (value := etable_values res_cell i); auto.
    apply (alloc_memory_table_lookup_write_cell_correct _ _ _ _ _ _ _ 
      stack_write i Hrange); auto.
    - apply eid_common.
    - pose(sp_common i); lia.
  lia.
Qed.

Require Import ImageTableModel.
Require Import InjectivityHelper.

Lemma Test_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->    
  etable_values (ops_cell Test) i = 1 ->
    program (wasm_pc st) = ITest (bool_of_Z (etable_values is_i32_cell i)).
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i Test Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  apply opcode_of_instruction_inj.
  rewrite <- Hopcode. 
  unfold opcode_config, config_opcode, opcode_of_instruction.
  rewrite <- !Zplus_assoc.
  f_equal.
  rewrite bool_of_Z_simpl.
  2: { apply is_i32_cell_bit. }

  rewrite Z.mul_0_l, Z.add_0_l.
  
  rewrite CommonData.shiftl_1_n.
  2: { cbv - [ Z.le ] ; lia. }
  reflexivity.
Qed.

Lemma result_one_for_value_zero : forall i,
    0 <= i ->
    etable_values (ops_cell Test) i = 1 ->
    etable_values value_cell i = 0 ->
    etable_values res_cell i = 1.
Proof.
  intros i Hrange Hops Hval.
  pose(H:= op_test_res_not_value i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Lemma result_zero_for_value_nonzero : forall i,
    0 <= i ->
    etable_values (ops_cell Test) i = 1 ->
    etable_values value_cell i <> 0 ->
    etable_values res_cell i = 0.
Proof.
  intros i Hrange Hops Hval.
  pose(H:= op_test_res_not_value i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  destruct H as [H _].
  apply(Zmult_integral_l (etable_values value_cell i) _ Hval).
  lia.
Qed.

Lemma test_mops : forall i,
    0 <= i ->
    etable_values eid_cell i > 0 ->
    etable_values enabled_cell i = 1 ->
    etable_values (ops_cell Test) i = 1 ->
    mops_at_correct i ->
        mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with Test in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i Test Hrow_enabled)); auto.
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

Theorem TestOp_correct : forall i st x1 xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Test) i = 1 ->
  state_rel i st ->
  wasm_stack st = x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) ((test x1)::xs)).
Proof.
  intros i st x1 xs Hrange Hrow_enabled Hmops Hop Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (test_mops) in Hmops; auto. destruct Hmops as [Hmops Hmops'].
  assert (Hval: etable_values value_cell i = x1).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get is_i32_cell)
                                 (value := fun get => get value_cell)
                                 (enable := fun get => get (ops_cell Test)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_cell_bit i).
    - eauto.
    - eauto.
    - apply stack_read.
  }
  assert (Hres: etable_values res_cell i = test x1).
  {
    unfold test.
    destruct x1.
    - apply(result_one_for_value_zero i Hrange Hop Hval).
    - assert(etable_values value_cell i <> 0). lia.
      apply(result_zero_for_value_nonzero i Hrange Hop H).
    - pose(value_cell_U64 i).
      lia.
  }
  rewrite <-Hval in Hstk.  rewrite <-Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res_cell i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Test); auto.
    rewrite iid_change with (idx := Test); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res_cell i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_1_without_value with (col:=memory_table_lookup_stack_write)
                                (value := fun get => get res_cell)
                                (is_i32 := fun get => 1)
                                (enable := fun get => get (ops_cell Test)); auto; try lia.
  - apply Hstk.
  - pose(Hsp := sp_change i Test Hrange Hrow_enabled Hop).
    replace(config_sp_diff (opcode_config Test i)) with 0 in Hsp by constructor.
    lia.
  - pose (mpages_change i Test); simpl in *; lia.        
  - rewrite (frame_id_change i Test); auto; reflexivity.
  - rewrite (fid_change i Test); auto.
  - apply stack_write.
Qed.
