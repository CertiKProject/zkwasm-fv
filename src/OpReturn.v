(* Copyright (C) CertiK 2024-2026 *)

Require Import FunctionalExtensionality.
Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import JTableModel JTable.
Require Import ETable.
Require Import Relation RelationHelper.

Require Import OpReturnModel.

(* Proofs about op_return.rs. *)

Require Import Wasm.numerics.
Require Import Lia.
Require Import MTable.

Theorem opcode_mops_correct_return : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Return i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config Return i)) with (etable_values op_return_keep i).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  destruct (op_return_keep_cell_bit i) as [Hkeep | Hnokeep].
  - rewrite Hkeep in *. lia.
  - rewrite Hnokeep in *.
    assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  {
    apply (write_cell_mops _ _ _ _ _ _ _ stack_write i Hrange); auto.
    - apply (eid_common i).
    - apply (OpReturnModel.is_i32_bit).
    - pose (drop_common i).
      pose (sp_common i); lia.
      lia.
  }
  lia.
Qed.

Lemma return_mops : forall i,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    etable_values (ops_cell Return) i = 1 ->
    mops_at_correct i ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = etable_values op_return_keep i
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with Return in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i Return Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Stack).

  destruct (op_return_keep_cell_bit i) as [Hkeep | Hnokeep].
  - rewrite Hkeep in *. lia.
  - rewrite Hnokeep in *.
    assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  {
    apply (write_cell_mops _ _ _ _ _ _ _ stack_write i Hrange); auto.
    - apply (eid_common i).
    - apply (OpReturnModel.is_i32_bit).
    - pose (drop_common i).
      pose (sp_common i); lia.
      lia.
  }
  lia.
Qed.

Lemma stack_rel_drop : forall xs ys stk_map sp,
    stack_rel stk_map sp (xs++ys) ->
    stack_rel stk_map (sp + Z.of_nat (length xs)) ys.
Proof.
  induction xs.
  - simpl.
    intros ys stk_map sp Hrel.
    replace (sp + 0) with sp by lia; auto.
  - simpl.
    intros ys stk_map sp [_ Hrel].
    specialize (IHxs _ _ _ Hrel). clear Hrel.
    replace (sp + Z.pos (Pos.of_succ_nat (length xs)))
      with  (sp + 1 + (Z.of_nat (length xs))) by lia.
    auto.
Qed.

Lemma stack_rel_write_negative'' : forall col i is_i32 enable eid offset sp value stk2,
    0 <= i ->
    eid > 0 ->
    mops_at eid MTableModel.LocationType_Stack = 1 ->    
    enable (fun c : etable_cols => etable_values c i) = 1 ->    
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    stack_rel (stk_map eid) (sp+1) (stk2) ->
    etable_values eid_cell i = eid ->
    offset (fun c  => etable_values c i)   = sp ->
    0 <= offset (fun c : etable_cols => etable_values c i) < 2 * common + 10 ->    
  alloc_memory_table_lookup_write_cell
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    offset
    is_i32
    value
    enable ->
  stack_rel (stk_map (eid+1)) (sp) ((value (fun c => etable_values c i))::stk2).
Proof.
  intros col i is_i32 enable eid offset sp value stk2.
  intros Hrange Heid_nonzero Hmops Henable His32_bit Hrel Heid Hsp Hoffset_range Hwrite.
  apply alloc_memory_table_lookup_write_cell_correct 
    with (i := i)
    in Hwrite; auto; try lia.
  { apply mtable_write with (init:=empty) in Hwrite.
    - rewrite Heid in *.
      change (gather_entries (eid + 1) MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
        with (stk_map (eid+1)) in Hwrite.
      change (gather_entries eid MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
        with (stk_map eid) in Hwrite.
      rewrite Hwrite.
      rewrite Hsp in *.
      remember (etable_values (col AMTLWC_value_cell) i) as u.
      eapply stack_rel_write_negative'; eauto.
    - rewrite Heid; lia.
    - rewrite Heid; lia.
  }
  - pose (eid_common i); lia.
Qed.

Lemma callstack_rel_uncons : forall x y cs,
    x > 0 ->
    callstack_rel x y cs ->
    exists l cs', cs = l::cs'.
Proof.
  intros.
  destruct cs.
  - simpl in *. lia.
  - eauto.
Qed.


Require Import ImageTableModel.
Require Import InjectivityHelper.
  
Lemma config_opcode_inj_Return : forall i instr,
    config_opcode (opcode_config Return i) =
            opcode_of_instruction instr ->
    instr =
    IReturn (bool_of_Z (etable_values keep i)) (Wasm_int.Int32.repr (etable_values drop i)).
Proof.
  intros.
  apply opcode_of_instruction_inj.
  rewrite <- H. clear H.
  unfold opcode_config, config_opcode, opcode_of_instruction.
  rewrite <- !Zplus_assoc.
  f_equal.
  rewrite bool_of_Z_simpl.
  2: { apply op_return_keep_cell_bit. }
  rewrite !CommonData.shiftl_1_n.
  2: { cbv - [ Z.le ] ; lia. }
  2: { cbv - [ Z.le ] ; lia. }
  f_equal.
  rewrite Wasm_int.Int32.unsigned_repr.
  2: { apply iscommon_is32.
      apply drop_common. }
  reflexivity.
Qed.

Lemma Return_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->    
  etable_values (ops_cell Return) i = 1 ->
    program (wasm_pc st) = IReturn (bool_of_Z (etable_values keep i)) (Wasm_int.Int32.repr (etable_values drop i)).
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i Return Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  apply (config_opcode_inj_Return _ _ Hopcode).
Qed.

(* Two cases, for keep=1 and keep=0 *)

Theorem Return_correct_nokeep : forall i st xs ys,
  0 <= i ->
  i + 1 < ETableModel.etable_numRow ->
  etable_values frame_id_cell i > 0 ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Return) i = 1 ->
  etable_values keep i = 0 ->
  state_rel i st ->
  wasm_stack st = xs++ys ->
  etable_values drop i = Z.of_nat (length xs)  ->
  exists lbl cs',
    (wasm_callstack st) = lbl::cs'
    /\ state_rel (i+1) (update_callstack (update_stack (move_to_label st lbl) ys) cs').
Proof.
  intros i st xs ys Hrange Hmore_range Hframe_nonzero Hrow_enabled Hmops Hop Hnokeep Hrel Hstk Hlen.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).  
  apply return_mops in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].

  assert (Hjops_bound :  JTable.jops_at (etable_values frame_id_cell i) <= 1).
  {
    apply ETable.jops_at_bounded; auto; try lia.
  }
  
  assert (Hlookup := c8c i Hrange).
  replace (etable_values frame_table_lookup i) 
    with (encode_frame_table_entry
            (etable_values frame_id_cell i)
            (etable_values frame_id_cell (i+1))
            (etable_values fid_cell i)
            (etable_values fid_cell (i+1))
            (etable_values iid_cell (i+1)))
    in Hlookup.
  2: {
    destruct (return_frame_table_lookup i Hrange) as [Hgate _].
    replace (i+0) with i in * by lia.
    simpl in Hgate.
    lia.
  }
  exists (etable_values fid_cell (i+1), etable_values iid_cell (i+1)).
  destruct (callstack_rel_uncons _ _ _ Hframe_nonzero (state_callstack_rel _ _ Hrel)) as [lbl [cs' Hcs']].
  exists cs'.
  assert (Hcs_rel := state_callstack_rel _ _ Hrel).
  rewrite Hcs' in Hcs_rel. 
  simpl in Hcs_rel.
  destruct Hcs_rel as [Hrel_nonzero [next_id [Hrel_next_common [Hrel_fst_common [Hrel_snd_common [Hrel_lookup Hrel_cs']]]]]].
  destruct (in_jtable_unique Hjops_bound Hrel_lookup Hlookup) as [? [? [? ?]]]; try lia.
  { pose (frame_id_common (i+1)); lia. }
  { pose (fid_common i) ; lia. }
  { pose (fid_common i) ; lia. }
  { pose (fid_common (i+1)); lia. }
  { pose (iid_common (i+1)); lia. }
  destruct lbl as [next_fid next_iid]. simpl in *.
  subst.
  split; [congruence|].
  constructor.
  - rewrite iid_change with (idx := Return); auto.
    rewrite fid_change with (idx := Return); auto.
    simpl.
    rewrite pc_update_callstack, pc_update_stack, pc_move_label.
    reflexivity.
  - rewrite eid_change by auto.
    rewrite sp_change with (idx := Return); auto.
    simpl.
    rewrite stack_update_callstack, stack_update_stack.
    replace (etable_values sp_cell i + etable_values drop i + 1)
      with  (etable_values sp_cell i +1 + Z.of_nat (length xs)) by lia. 
    apply stack_rel_drop.
    rewrite <- Hstk.
    rewrite stack_no_write; auto.
    * destruct Hrel; auto.
    * rewrite Hnokeep in Hmops.
      apply Hmops.
  - rewrite globals_update_callstack, globals_update_stack, globals_move_label.
    rewrite eid_change by auto.
    rewrite globals_no_write; auto.
    destruct Hrel; auto.
  - rewrite eid_change by auto.
    rewrite memory_no_write; auto.
    rewrite (mpages_change i Return) by auto. simpl. rewrite Z.add_0_r.
    rewrite memory_update_callstack, memory_update_stack, memory_move_label.
    rewrite maximal_memory_pages_change; auto.
    destruct Hrel.
    apply state_heap_rel.
  - rewrite callstack_update_callstack.
    apply Hrel_cs'.
Qed.

Theorem Return_correct_keep : forall i st x xs ys,
  0 <= i ->
  i + 1 < ETableModel.etable_numRow ->
  etable_values frame_id_cell i > 0 ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Return) i = 1 ->
  etable_values keep i = 1 ->
  state_rel i st ->
  wasm_stack st = x::xs++ys ->
  etable_values drop i = Z.of_nat (length xs)  ->
  exists lbl cs',
    (wasm_callstack st) = lbl::cs'
    /\ state_rel (i+1) (update_callstack (update_stack (move_to_label st lbl) (x::ys)) cs').
Proof.
  intros i st x xs ys Hrange Hmore_range Hframe_nonzero Hrow_enabled Hmops Hop Hnokeep Hrel Hstk Hlen.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).  
  apply return_mops in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].

  assert (Hjops_bound :  JTable.jops_at (etable_values frame_id_cell i) <= 1).
  {
    apply ETable.jops_at_bounded; auto. lia.
  }
  
  assert (Hlookup := c8c i Hrange).
  replace (etable_values frame_table_lookup i) 
    with (encode_frame_table_entry
            (etable_values frame_id_cell i)
            (etable_values frame_id_cell (i+1))
            (etable_values fid_cell i)
            (etable_values fid_cell (i+1))
            (etable_values iid_cell (i+1)))
    in Hlookup.
  2: {
    destruct (return_frame_table_lookup i Hrange) as [Hgate _].
    replace (i+0) with i in * by lia.
    simpl in Hgate.
    lia.
  }
  assert (Hx: etable_values value_u64_cell i = x).
  {
    eapply stack_rel_read_without_value with
      (col := memory_table_lookup_stack_read)
      (n := 0%nat)
      (is_i32 := (fun get => get is_i32))
      (enable := (fun get => get keep * get (ops_cell Return)))
      (value :=     (fun get => get value_u64_cell)); eauto.
    - lia.
    - lia.
    - pose (is_i32_bit i); auto.
    - replace  (fun get : etable_cols -> Z => get sp_cell + 1 + Z.of_nat 0)
        with   (fun get : etable_cols -> Z => get sp_cell + 1)
        by (extensionality get; lia).
      apply stack_read.
  } 

  assert (Hcs_rel := state_callstack_rel _ _ Hrel).
  destruct (callstack_rel_uncons _ _ _ Hframe_nonzero Hcs_rel) as [lbl [cs' Hcs']].
  rewrite Hcs' in Hcs_rel. 
  simpl in Hcs_rel.
  destruct Hcs_rel as [Hrel_nonzero [next_id [Hrel_next_common [Hrel_fst_common [Hrel_snd_common [Hrel_lookup Hrel_cs']]]]]].
  destruct (in_jtable_unique Hjops_bound Hrel_lookup Hlookup) as [? [? [? ?]]]; try lia.
  { pose (frame_id_common (i+1)); lia. }
  { pose (fid_common i) ; lia. }
  { pose (fid_common i) ; lia. }
  { pose (fid_common (i+1)); lia. }
  { pose (iid_common (i+1)); lia. }
  destruct lbl as [next_fid next_iid]. simpl in *.
  exists (etable_values fid_cell (i+1), etable_values iid_cell (i+1)). exists cs'.
  subst.
  split; [congruence|].
  constructor.
  - rewrite iid_change with (idx := Return); auto.
    rewrite fid_change with (idx := Return); auto.
    simpl.
    rewrite pc_update_callstack, pc_update_stack, pc_move_label.
    reflexivity.
  - { rewrite eid_change by auto.
      rewrite sp_change with (idx := Return); auto.
      simpl.
      rewrite stack_update_callstack, stack_update_stack.
      replace (etable_values sp_cell i + etable_values drop i + 1)
        with  (etable_values sp_cell i +1 + Z.of_nat (length xs)) by lia.
      apply (stack_rel_write_negative''
               memory_table_lookup_stack_write
               i 
               (fun get => get is_i32)
               (fun get => get keep * get (ops_cell Return))
               (etable_values eid_cell i)
               (fun get => get sp_cell + get drop + 1)
               (etable_values sp_cell i + 1 + Z.of_nat (length xs))
               (fun get => get value_u64_cell)
               ys); auto.
      - rewrite Hnokeep in Hmops.
        apply Hmops.
      - lia.
      - pose (is_i32_bit i); auto.
      - replace (etable_values sp_cell i + 1 + Z.of_nat (length xs) + 1)
           with (etable_values sp_cell i + 1 + 1 + Z.of_nat (length xs)) by lia.
        apply stack_rel_drop.
        destruct Hrel as [_ state_stack_rel _ _].
        rewrite Hstk in state_stack_rel.
        destruct state_stack_rel as [_ state_stack_rel].
        exact state_stack_rel.
      - rewrite Hlen. lia.
      - pose (sp_common i).
        pose (drop_common i).
        lia.
      - apply stack_write.
    }
  - rewrite globals_update_callstack, globals_update_stack, globals_move_label.
    rewrite eid_change by auto.
    rewrite globals_no_write; auto.
    destruct Hrel; auto.
  - rewrite eid_change by auto.
    rewrite memory_no_write; auto.
    rewrite (mpages_change i Return) by auto. simpl. rewrite Z.add_0_r.
    rewrite memory_update_callstack, memory_update_stack, memory_move_label.
    rewrite maximal_memory_pages_change; auto.
    destruct Hrel.
    apply state_heap_rel.
  - rewrite callstack_update_callstack.
    apply Hrel_cs'.
Qed.
