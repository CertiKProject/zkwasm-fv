(* Copyright (C) CertiK 2024-2026 *)

Require Import Wasm.numerics.
Require Import Wasm.operations.

From mathcomp.ssreflect Require Import seq ssrfun.
From mathcomp.ssreflect Require ssrnat.

From compcert.lib Require Import Integers.
From compcert.common Require Import Memdata.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import OpLoadModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.
Require Import OpLoadHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_load : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Load i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config Load i)) with 1.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  - apply MTable.mtable_write_mops with
      (offset := etable_values sp_cell i + 1)
      (is_i32 := etable_values is_i32 i)
      (value := etable_values res i); auto.
    apply (alloc_memory_table_lookup_write_cell_correct _ _ _ _ _ _ _ 
      stack_write i Hrange); auto.
    - apply eid_common.
    - apply is_i32_bit.
    - pose(sp_common i); lia.
  lia.
Qed.

Lemma load_mops : forall i,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    etable_values (ops_cell Load) i = 1 ->
    mops_at_correct i ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with Load in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i Load Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).

  assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  {
    apply (write_cell_mops _ _ _ _ _ _ _ stack_write i Hrange); auto.
    - apply (eid_common i).
    - apply (is_i32_bit i).
    - pose (sp_common i); lia.
  }
  lia.
Qed.

Require Import ImageTableModel.
Require Import InjectivityHelper.

Lemma Load_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values ETableModel.enabled_cell i = 1 ->    
  etable_values (ops_cell Load) i = 1 ->
  exists lz off,
    program (wasm_pc st) = ILoad (bool_of_Z (etable_values is_i32 i)) lz (bool_of_Z (etable_values is_sign i)) off
    /\ etable_values len i = len_of_LoadSize lz
    /\ etable_values opcode_load_offset i = Wasm_int.Int64.unsigned off.
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i Load Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  destruct  (load_one_number_of_bytes_len i Hrange Hops) as [Hsel | [Hsel | [Hsel | Hsel]]].
  - exists VAL8. exists (Wasm_int.Int64.repr (etable_values opcode_load_offset i)).
    split; [|split]; [| simpl; tauto | symmetry;  apply (common_unsigned_repr64 _ opcode_load_offset_common)].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction, encode_load_access, Z_of_ConvOpSrc.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl by (apply OpLoadModel.is_i32_bit).
    rewrite bool_of_Z_simpl by (apply OpLoadModel.is_sign_bit).
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    f_equal.
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 Hsel5]]]]. 
    rewrite !Hsel2, !Hsel3, !Hsel4.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    f_equal.
    rewrite (common_unsigned_repr64 _ opcode_load_offset_common).
    reflexivity.
  - exists VAL16. exists (Wasm_int.Int64.repr (etable_values opcode_load_offset i)).
    split; [|split]; [| simpl; tauto | symmetry;  apply (common_unsigned_repr64 _ opcode_load_offset_common)].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction, encode_load_access, Z_of_ConvOpSrc.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl by (apply OpLoadModel.is_i32_bit).
    rewrite bool_of_Z_simpl by (apply OpLoadModel.is_sign_bit).
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    f_equal.
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 Hsel5]]]]. 
    rewrite !Hsel2, !Hsel3, !Hsel4.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    f_equal.
    rewrite (common_unsigned_repr64 _ opcode_load_offset_common).
    reflexivity.
  - exists VAL32. exists (Wasm_int.Int64.repr (etable_values opcode_load_offset i)).
    split; [|split]; [| simpl; tauto | symmetry;  apply (common_unsigned_repr64 _ opcode_load_offset_common)].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction, encode_load_access, Z_of_ConvOpSrc.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl by (apply OpLoadModel.is_i32_bit).
    rewrite bool_of_Z_simpl by (apply OpLoadModel.is_sign_bit).
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    f_equal.
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 Hsel5]]]]. 
    rewrite !Hsel2, !Hsel3, !Hsel4.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    f_equal.
    rewrite (common_unsigned_repr64 _ opcode_load_offset_common).
    reflexivity.
  - exists VAL64. exists (Wasm_int.Int64.repr (etable_values opcode_load_offset i)).
    split; [|split]; [| simpl; tauto | symmetry;  apply (common_unsigned_repr64 _ opcode_load_offset_common)].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction, encode_load_access, Z_of_ConvOpSrc.
    rewrite <- !Zplus_assoc.
    f_equal.
    rewrite bool_of_Z_simpl by (apply OpLoadModel.is_i32_bit).
    rewrite bool_of_Z_simpl by (apply OpLoadModel.is_sign_bit).
    rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
    f_equal.
    destruct Hsel as [Hsel1 [Hsel2 [Hsel3 [Hsel4 Hsel5]]]]. 
    rewrite !Hsel2, !Hsel3, !Hsel4.
    rewrite !Z.mul_0_l, !Z.add_0_l.
    f_equal.
    rewrite (common_unsigned_repr64 _ opcode_load_offset_common).
    reflexivity.
Qed.

Require Import FunctionalExtensionality.

Theorem load_correct : forall i st base xs (signed : bool) (srctype: ConvOpSrc) (restype: ConvOpRes),
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Load) i = 1 ->
  etable_values is_sign i = (Z_of_bool signed) ->
  etable_values len i = len_of_LoadSize srctype ->
  etable_values is_i32 i = (match restype with RES64 => 0 | RES32 => 1 end) ->  
  state_rel i st ->
  wasm_stack st =  (base :: xs) ->
  exists bs,
    load (wasm_memory st)
         (Z.to_N base)
         (Z.to_N (etable_values opcode_load_offset i))
         (Z.to_nat (etable_values len i)) = Some bs
    /\ sign_extend signed srctype restype (decode_int bs) = etable_values res i
    /\ state_rel (i+1) (update_stack (incr_iid st)
                           (sign_extend signed srctype restype (decode_int bs) ::xs)).
Proof.
  intros i st base xs signed srctype restype Hrange Hrow_enabled Hmops Hop Hsigned Hlen Hi32 Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (load_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].

  replace base with (etable_values load_base i).
  2: {
    apply stack_rel_read with
      (i := i)
      (n := 0%nat)
      (col := memory_table_lookup_stack_read)
      (is_i32 := (fun get => 1))
      (enable := (fun get => get (ops_cell Load)))
      (st := st)
      (stk := base::xs); auto.
    - lia.
    - replace  (fun get : etable_cols -> Z => get sp_cell + 1 + Z.of_nat 0)
         with  (fun get : etable_cols -> Z => get sp_cell + 1)
               by (extensionality get; lia).
      apply stack_read.
  }

  destruct (load_load_picked i (wasm_memory st)) as [bs [Hload_bs Hload_picked]]; auto.
  { destruct Hrel.
    assumption. }
  exists bs.
  split; [auto|].
  assert (Hres_eq : sign_extend signed srctype restype (decode_int bs) = etable_values res i).
  { rewrite <- Hload_picked.
    rewrite <- sign_extension_correct by auto.
    symmetry. apply loaded_result_is_correct; auto. }
  split; [exact Hres_eq|].
  rewrite Hres_eq.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Load); auto.
    rewrite iid_change with (idx := Load); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_1_without_value
    with (col:=memory_table_lookup_stack_write)
         (is_i32 := fun get => get is_i32)
         (value := fun get => get res)
         (enable := fun get => get (ops_cell Load)); eauto; try lia.
  - pose (is_i32_bit i); lia.
  - pose(Hsp := sp_change i Load Hrange Hrow_enabled Hop).
    replace (config_sp_diff (opcode_config Load i)) with (0) in Hsp by constructor.
    lia.
  - pose (mpages_change i Load); simpl in *; lia.
  - rewrite (frame_id_change i Load); auto; reflexivity.
  - rewrite (fid_change i Load); auto.    
  - apply stack_write.
Qed.
