(* Copyright (C) CertiK 2024-2026 *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETable.
Require Import Relation RelationHelper.
Require MTable.

Require Import OpBinBitModel.

(* Proofs about op_bin_bit.rs. *)

Require Import Wasm.numerics.
Require Import RTableModel.
Require Import BitTableModel.
Require BitTable.
Require Import Lia.
Require Import MTable.

Theorem opcode_mops_correct_bin_bit : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct BinBit i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config BinBit i)) with 1.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  - apply MTable.mtable_write_mops with
      (offset := etable_values sp_cell i + 2)
      (is_i32 := etable_values is_i32 i)
      (value := etable_values res i); auto.
    apply (alloc_memory_table_lookup_write_cell_with_value_correct _ _ _ _ _ _ 
      stack_write i Hrange); auto.
    - apply eid_common.
    - apply is_i32_bit.
    - pose(sp_common i); lia.
  lia.
Qed.

Lemma lookup_val : forall i,
    0 <= i ->
    etable_values (ops_cell BinBit) i = 1 ->
    exists j,
       0 <= j
       /\ value bit_table block_sel (j + 1) = 1
       /\ value bit_table op j              = etable_values op_class i
       /\ value bit_table val_l j           = etable_values lhs      i
       /\ value bit_table val_r j           = etable_values rhs      i
       /\ value bit_table val_res j         = etable_values res      i.  
Proof.
  intros i Hrange Hop.
  destruct (c8f i Hrange) as [j Hc8f].
  exists j.
  assert (Hlookup := op_bin_bit_lookup i Hrange).
  simpl in Hlookup.
  replace (i+0) with i in * by lia.
  lia.
Qed.

Lemma single_selector : forall i,
    0 <= i ->
    etable_values (ops_cell BinBit) i = 1 ->
    (    etable_values op_class i = BitOp_And
     \/  etable_values op_class i = BitOp_Or
     \/  etable_values op_class i = BitOp_Xor
     \/  etable_values op_class i = Popcnt_index).
Proof.
  intros i Hrange Hops.
  destruct (lookup_val i Hrange Hops) as [j [Hjrange [Hsel [Hop _]]]].
  assert (Hcases := BitTable.OP_cases j Hjrange Hsel).
  simpl in Hop.
  unfold BitTable.OP in Hcases.
  rewrite Hop in *.
  eauto.
Qed.


Require Import ImageTableModel.
Require Import InjectivityHelper.

Definition BinBit_op i :=
  if (Z.eq_dec (etable_values op_class i) BitOp_And) then AND
  else if (Z.eq_dec (etable_values op_class i) BitOp_Or) then OR
  else XOR.

Lemma BinBit_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->
  etable_values (ops_cell BinBit) i = 1 ->
  exists op,
    op = BinBit_op i
    /\ program (wasm_pc st) = IBinBit (bool_of_Z (etable_values is_i32 i)) op
    /\ match op with
         AND => etable_values op_class i = BitOp_And
       | OR => etable_values op_class i = BitOp_Or
       | XOR => etable_values op_class i = BitOp_Xor  end.
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i BinBit Hrange Henabled Hops) in Hencode.
  destruct (single_selector i Hrange Hops) as [Hsel | [Hsel | [Hsel | Hsel]]].
  - exists AND.
    apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
    destruct Hencode as [Hfid [Hid Hopcode]].
    subst.
    split. {
      unfold BinBit_op. rewrite Hsel. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpBinBitModel.is_i32_bit. }
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    rewrite Hsel.
    reflexivity.
  - exists OR.
    apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
    destruct Hencode as [Hfid [Hid Hopcode]].
    subst.
    split. {
      unfold BinBit_op. rewrite Hsel. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpBinBitModel.is_i32_bit. }
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    rewrite Hsel.
    reflexivity.
  - exists XOR.
    apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
    destruct Hencode as [Hfid [Hid Hopcode]].
    subst.
    split. {
      unfold BinBit_op. rewrite Hsel. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl.
    2: { apply OpBinBitModel.is_i32_bit. }
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    rewrite Hsel.
    reflexivity.
  - cut False; [tauto|].
    apply encode_instruction_table_entry_inj in Hencode; auto.
    2: { apply ETableModel.fid_common. }
    2: { apply ETableModel.iid_common. }
    2: { apply InjectivityHelper.config_opcode_range. }
    2: { apply InjectivityHelper.opcode_of_instruction_range. }
    destruct Hencode as [_ [_ Hencode]].
    unfold config_opcode, opcode_config in Hencode.
    symmetry in Hencode.
    rewrite Hsel in Hencode.
    apply opcode_of_instruction_weird_extra_case in Hencode.
    + exact Hencode.
    + apply is_i32_bit.
Qed.
  
Lemma bitop_mops : forall i,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    etable_values (ops_cell BinBit) i = 1 ->
    mops_at_correct i ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Hrow_enabled Hop_class Hops.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with BinBit in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i BinBit Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).

  assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  {
    apply (write_cell_with_value_mops _ _ _ _ _ _ stack_write i Hrange); auto.
    - apply (eid_common i).
    - apply (is_i32_bit).
    - pose (sp_common i).
    - pose (sp_common i); lia.
  }
  lia.
Qed.
  
Theorem BitOp_And_correct : forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinBit) i = 1 ->
    etable_values op_class i = RTableModel.BitOp_And ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1:: Wasm_int.Z_of_uint i64m x2::xs) ->
    state_rel (i+1) ((update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_and i64m x2 x1) :: xs))).
Proof.
  intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (bitop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hrhs: etable_values rhs i = Wasm_int.Z_of_uint i64m x1).
  {
    eapply stack_rel_read_1 with (is_i32 := fun get => get is_i32)
                                 (enable := fun get => get (ops_cell BinBit)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs i = Wasm_int.Z_of_uint i64m x2).
  {
    eapply stack_rel_read_2 with (is_i32 := fun get => get is_i32)
                                 (enable := fun get => get (ops_cell BinBit)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = Wasm_int.Z_of_uint i64m (Wasm_int.int_and i64m x2 x1)).
  {
    destruct (lookup_val i Hrange Hop) as [j [Hbit1 [Hbit2 [Hbit3 [Hbit4 [Hbit5 Hbit6]]]]]].
    rewrite Hop_class, Hrhs, Hlhs in *.
    rewrite <-  Hbit6.
    pose (BitTable.in_bit_table_and _ _ _ Hbit1 Hbit2 Hbit3 Hbit4 Hbit5).
    congruence.
  }

  assert (wasm_pc (update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_and i64m x2 x1) :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := BinBit); auto.
    rewrite iid_change with (idx := BinBit); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (Wasm_int.Z_of_uint i64m (Wasm_int.int_and i64m x2 x1) :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  rewrite <- Hrhs, <-Hlhs in *.  rewrite <-Hres in *. clear Hop_class Hrhs Hlhs Hres.

  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get op_bin_bit_is_i32)
                                (enable := fun get => get (ops_cell BinBit)); auto; try lia.
  - apply (is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i BinBit); auto.
  - pose (mpages_change i BinBit); simpl in *; lia.
  - rewrite (frame_id_change i BinBit); auto; reflexivity.
  - rewrite (fid_change i BinBit); auto.
  - apply stack_write.
Qed.

Theorem BitOp_Or_correct : forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinBit) i = 1 ->
    etable_values op_class i = RTableModel.BitOp_Or ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1:: Wasm_int.Z_of_uint i64m x2::xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_or i64m x2 x1) :: xs)).
Proof.
  intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (bitop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hrhs: etable_values rhs i = Wasm_int.Z_of_uint i64m x1).
  {
    eapply stack_rel_read_1 with (is_i32 := fun get => get is_i32)
                                 (enable := fun get => get (ops_cell BinBit)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs i = Wasm_int.Z_of_uint i64m x2).
  {
    eapply stack_rel_read_2 with (is_i32 := fun get => get is_i32)
                                 (enable := fun get => get (ops_cell BinBit)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = Wasm_int.Z_of_uint i64m (Wasm_int.int_or i64m x2 x1)).
  {
    destruct (lookup_val i Hrange Hop) as [j [Hbit1 [Hbit2 [Hbit3 [Hbit4 [Hbit5 Hbit6]]]]]].
    rewrite Hop_class, Hrhs, Hlhs in *.
    rewrite <-  Hbit6.
    pose (BitTable.in_bit_table_or _ _ _ Hbit1 Hbit2 Hbit3 Hbit4 Hbit5).
    congruence.
  }
  rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hrhs Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := BinBit); auto.
    rewrite iid_change with (idx := BinBit); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get op_bin_bit_is_i32)
                                (enable := fun get => get (ops_cell BinBit)); auto; try lia.
  - apply (is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i BinBit); auto.
  - pose (mpages_change i BinBit); simpl in *; lia.    
  - rewrite (frame_id_change i BinBit); auto; reflexivity.
  - rewrite (fid_change i BinBit); auto.
  - apply stack_write.
Qed.

Theorem BitOp_Xor_correct : forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell BinBit) i = 1 ->
    etable_values op_class i = RTableModel.BitOp_Xor ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1:: Wasm_int.Z_of_uint i64m x2::xs) ->
    state_rel (i+1)
      (update_stack (incr_iid st)
         (Wasm_int.Z_of_uint i64m (Wasm_int.int_xor i64m x2 x1) :: xs)).
Proof.
  intros i st x1 x2 xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (bitop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hrhs: etable_values rhs i = Wasm_int.Z_of_uint i64m x1).
  {
    eapply stack_rel_read_1 with (is_i32 := fun get => get is_i32)
                                 (enable := fun get => get (ops_cell BinBit)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_rhs. }
  assert (Hlhs: etable_values lhs i = Wasm_int.Z_of_uint i64m x2).
  {
    eapply stack_rel_read_2 with (is_i32 := fun get => get is_i32)
                                 (enable := fun get => get (ops_cell BinBit)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - apply Hstk.
    - apply stack_read_lhs. }
  assert (Hres: etable_values res i = Wasm_int.Z_of_uint i64m (Wasm_int.int_xor i64m x2 x1)).
  {
    destruct (lookup_val i Hrange Hop) as [j [Hbit1 [Hbit2 [Hbit3 [Hbit4 [Hbit5 Hbit6]]]]]].
    rewrite Hop_class, Hrhs, Hlhs in *.
    rewrite <-  Hbit6.
    pose (BitTable.in_bit_table_xor _ _ _ Hbit1 Hbit2 Hbit3 Hbit4 Hbit5).
    congruence.
  }
  rewrite <- Hrhs, <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hrhs Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := BinBit); auto.
    rewrite iid_change with (idx := BinBit); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_2 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get op_bin_bit_is_i32)
                                (enable := fun get => get (ops_cell BinBit)); auto; try lia.
  - apply (is_i32_bit i).
  - apply Hstk.
  - apply (sp_change i BinBit); auto.
  - pose (mpages_change i BinBit); simpl in *; lia.    
  - rewrite (frame_id_change i BinBit); auto; reflexivity.
  - rewrite (fid_change i BinBit); auto.
  - apply stack_write.
Qed.

