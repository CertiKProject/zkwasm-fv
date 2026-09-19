(* Copyright (C) CertiK 2024-2026 *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import ImageTableModel.
Require Import OpConversionModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_conversion : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Conversion i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config Conversion i)) with 1.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  - apply MTable.mtable_write_mops with
      (offset := etable_values sp_cell i + 1)
      (is_i32 := etable_values res_is_i32 i)
      (value := etable_values res i); auto.
    apply (alloc_memory_table_lookup_write_cell_with_value_correct _ _ _ _ _ _ 
      stack_write i Hrange); auto.
    - apply eid_common.
    - apply res_is_i32_bit.
    - pose(sp_common i); lia.
  lia.
Qed.

Lemma mod_defn : forall a b n,
    n <> 0 ->
    a mod n = b ->
    exists c, a = n * c + b.
Proof.
  intros.
  pose(Hdiv := Z.div_eucl_eq a n H).
  rewrite Zaux.Zdiv_eucl_unique in Hdiv.
  rewrite H0 in Hdiv.
  exists (a / n); auto.
Qed.

Lemma mod_cancel_l : forall a b c n,
    n <> 0 ->
    (a + b) mod n = (a + c) mod n ->
    b mod n = c mod n.
Proof.
  intros.
  remember ((a + b) mod n) as u.
  remember ((a + c) mod n) as v.
  symmetry in Hequ, Heqv.
  apply mod_defn in Hequ, Heqv; auto.
  destruct Hequ as [cu Hequ].
  destruct Heqv as [cv Heqv].
  symmetry in Hequ, Heqv.
  apply Z.add_move_l in Hequ, Heqv.
  rewrite Hequ, Heqv in H0.
  repeat rewrite <- Z.add_sub_assoc in H0.
  rewrite Z.add_cancel_l in H0.
  rewrite <- Z.add_move_l in H0.
  rewrite Z.add_sub_assoc in H0.
  symmetry in H0.
  rewrite <- Z.add_move_l in H0.
  repeat rewrite (Z.mul_comm n) in H0.
  rewrite Z.add_comm in H0.
  rewrite (Z.add_comm _ b) in H0.
  apply (f_equal (fun t => t mod n)) in H0.
  repeat rewrite Z_mod_plus_full in H0.
  auto.
Qed.

Lemma mod_cancel_r : forall a b c n,
    n <> 0 ->
    (a + b) mod n = (c + b) mod n ->
    a mod n = c mod n.
Proof.
  intros.
  repeat rewrite (Z.add_comm _ b) in H0.
  apply mod_cancel_l in H0; auto.
Qed.

Lemma only_one_value_type : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    (etable_values value_is_i8 i = 1 /\ etable_values value_is_i16 i = 0 /\ etable_values value_is_i32 i = 0 /\ etable_values value_is_i64 i = 0 /\ etable_values value_type_is_i32 i = 1)
 \/ (etable_values value_is_i8 i = 0 /\ etable_values value_is_i16 i = 1 /\ etable_values value_is_i32 i = 0 /\ etable_values value_is_i64 i = 0  /\ etable_values value_type_is_i32 i = 1)
 \/ (etable_values value_is_i8 i = 0 /\ etable_values value_is_i16 i = 0 /\ etable_values value_is_i32 i = 1 /\ etable_values value_is_i64 i = 0  /\ etable_values value_type_is_i32 i = 1 /\ etable_values res_is_i64 i = 1)
 \/ (etable_values value_is_i8 i = 0 /\ etable_values value_is_i16 i = 0 /\ etable_values value_is_i32 i = 0 /\ etable_values value_is_i64 i = 1  /\ etable_values value_type_is_i32 i = 0).
Proof.
  intros i Hrange Hops Henabled.
  destruct(itable_lookup_in_itable i Hrange Henabled) as [j H].
  rewrite itable_lookup_encode with (idx:= Conversion) in H; auto.
  symmetry in H.
  pose proof H as H'.
  pose proof H as H_allowed1.
  apply allowed_opcodes_val in H.
  assert (H_allowed2 := allowed_opcodes_val32 _ _ _ _ _ _ _ _ _ _ _ H').
  apply allowed_opcodes_val_type_is_i32 in H_allowed1.
  change (config_opcode (opcode_config Conversion i)) with
    (Z.shiftl (OpcodeClass_u64 Conversion) OPCODE_CLASS_SHIFT
    + (encode_conversion
        (etable_values sign_op i)
        (etable_values value_type_is_i32 i)
        (etable_values value_is_i8 i)
        (etable_values value_is_i16 i)
        (etable_values value_is_i32 i)
        (etable_values value_is_i64 i)
        (etable_values res_is_i32 i)
        (etable_values res_is_i64 i))) in H'.
  rewrite H' in H. clear H'.
  unfold encode_instruction_table_entry in H.
  pose(value_is_i8_bit i).
  pose(value_is_i16_bit i).
  pose(value_is_i32_bit i).
  pose(value_is_i64_bit i).
  pose(CommonModel.int_lt_order).
  assert(field_order <> 0) by lia.
  destruct H as [H | [H | [H | H]]];
    repeat rewrite Z.add_assoc in H;
    apply mod_cancel_l in H; auto;
    unfold encode_conversion in H;
    repeat rewrite <- Z.add_assoc in H;
    apply mod_cancel_l in H; auto;
    apply mod_cancel_l in H; auto;
    repeat rewrite Z.add_assoc in H;
    apply mod_cancel_r in H; auto;
    apply mod_cancel_r in H; auto;
    simpl Z.shiftl in H;
    rewrite Z.mod_small in H by lia;
    rewrite Z.mod_small in H by lia.
  - left; lia.
  - right. left; lia.
  - right. right. left; lia.
  - assert (etable_values value_type_is_i32 i = 0).
    {
      destruct (value_type_is_i32_bit i).
      - auto.
      - lia.
    }    
    right. right. right; lia.
Qed.

Lemma only_one_result_type : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    (etable_values res_is_i32 i = 1 /\ etable_values res_is_i64 i = 0)
 \/ (etable_values res_is_i32 i = 0 /\ etable_values res_is_i64 i = 1 /\ etable_values value_is_i64 i = 0).
Proof.
  intros i Hrange Hops Henabled.
  destruct(itable_lookup_in_itable i Hrange Henabled) as [j H].
  rewrite itable_lookup_encode with (idx:= Conversion) in H; auto.
  symmetry in H.
  pose proof H as H'.
  apply allowed_opcodes_res in H.
  assert (H_allowed2 := allowed_opcodes_res64 _ _ _ _ _ _ _ _ _ _ _ H').
  change (config_opcode (opcode_config Conversion i)) with
    (Z.shiftl (OpcodeClass_u64 Conversion) OPCODE_CLASS_SHIFT
    + (encode_conversion
        (etable_values sign_op i)
        (etable_values value_type_is_i32 i)
        (etable_values value_is_i8 i)
        (etable_values value_is_i16 i)
        (etable_values value_is_i32 i)
        (etable_values value_is_i64 i)
        (etable_values res_is_i32 i)
        (etable_values res_is_i64 i))) in H'.
  rewrite H' in H. clear H'.
  unfold encode_instruction_table_entry in H.
  pose(res_is_i32_bit i).
  pose(res_is_i64_bit i).
  pose(CommonModel.int_lt_order).
  assert(field_order <> 0) by lia.
  destruct H as [H | H];
    repeat rewrite Z.add_assoc in H;
    apply mod_cancel_l in H; auto;
    unfold encode_conversion in H;
    repeat rewrite <- Z.add_assoc in H;
    apply mod_cancel_l in H; auto;
    apply mod_cancel_l in H; auto;
    apply mod_cancel_l in H; auto;
    apply mod_cancel_l in H; auto;
    apply mod_cancel_l in H; auto;
    apply mod_cancel_l in H; auto;
    simpl Z.shiftl in H;
    rewrite Z.mod_small in H by lia;
    rewrite Z.mod_small in H by lia.
  - left; lia.
  - right; lia.
Qed.

Definition value_type_spec (srctyp : ConvOpSrc) i :=
  match srctyp with 
    | VAL8 => (etable_values value_is_i8 i = 1 /\ etable_values value_is_i16 i = 0 /\ etable_values value_is_i32 i = 0 /\ etable_values value_is_i64 i = 0 /\ etable_values value_type_is_i32 i = 1)
    | VAL16 =>  (etable_values value_is_i8 i = 0 /\ etable_values value_is_i16 i = 1 /\ etable_values value_is_i32 i = 0 /\ etable_values value_is_i64 i = 0 /\ etable_values value_type_is_i32 i = 1)
    | VAL32 => (etable_values value_is_i8 i = 0 /\ etable_values value_is_i16 i = 0 /\ etable_values value_is_i32 i = 1 /\ etable_values value_is_i64 i = 0 /\ etable_values value_type_is_i32 i = 1 /\ etable_values res_is_i64 i = 1) 
    | VAL64 => (etable_values value_is_i8 i = 0 /\ etable_values value_is_i16 i = 0 /\ etable_values value_is_i32 i = 0 /\ etable_values value_is_i64 i = 1 /\ etable_values value_type_is_i32 i = 0)
  end.

Definition result_type_spec (restyp: ConvOpRes) i := 
  match restyp with
  | RES32 => (etable_values res_is_i32 i = 1 /\ etable_values res_is_i64 i = 0)
  | RES64 =>  (etable_values res_is_i32 i = 0 /\ etable_values res_is_i64 i = 1  /\ etable_values value_is_i64 i = 0)
  end.


Definition OpConversion_value_type i :=
  if      (Z.eq_dec (etable_values value_is_i8 i) 1) then VAL8
  else if (Z.eq_dec (etable_values value_is_i16 i) 1)then VAL16
  else if (Z.eq_dec (etable_values value_is_i32 i) 1)then VAL32
  else if (Z.eq_dec (etable_values value_is_i64 i) 1)then VAL64
  else VAL64.

Lemma OpConversion_value_type_correct : forall srct i,
    value_type_spec srct i -> (OpConversion_value_type i) = srct.
Proof.
  intros srct i H.
  destruct srct; destruct H as [H1 [H2 [H3 [H4 H5]]]];
  unfold OpConversion_value_type;
  rewrite H1,H2,H3,H4; reflexivity.
Qed.

Definition OpConversion_result_type i :=
  if      (Z.eq_dec (etable_values res_is_i32 i) 1) then RES32
  else RES64.

Lemma OpConversion_result_type_correct : forall rest i,
    result_type_spec rest i -> (OpConversion_result_type i) = rest.
Proof.
  intros rest i H.
  destruct rest; destruct H as [H1 H2];
  unfold OpConversion_result_type;
  rewrite H1; reflexivity.
Qed.

Lemma only_one_value_type_ex : forall i,                
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    exists srctyp, value_type_spec srctyp i.
Proof.
  intros i Hrange Hops Henabled.
  unfold value_type_spec.
  destruct (only_one_value_type i Hrange Hops Henabled) as [H | [H | [H | H]]].
  - exists VAL8; auto.
  - exists VAL16; auto.
  - exists VAL32; auto.
  - exists VAL64; auto.
Qed.  

Lemma only_one_result_type_ex : forall i,                
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    exists restyp, result_type_spec restyp i.
Proof.
  intros i Hrange Hops Henabled.
  unfold value_type_spec.
  destruct (only_one_result_type i Hrange Hops Henabled) as [H | H].
  - exists RES32; auto.
  - exists RES64; auto.
Qed.
  
Lemma res_and_value_for_is_i32_wrap_i64 : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values is_i32_wrap_i64 i = 1 ->
    etable_values value_is_i64 i = 1 /\ etable_values res_is_i32 i = 1.
Proof.
  intros i Hrange Hops Hwrap.
  destruct (op_conversion_i32_wrap_i64 i Hrange) as [H _].
  simpl in H.
  replace(i+0) with i in * by lia.
  pose(Hval := value_is_i64_bit i).
  pose(Hres := res_is_i32_bit i).
  lia.
Qed.

Lemma res_and_value_for_is_i32_wrap_i64_only_if : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values value_is_i64 i = 1 ->
    etable_values res_is_i32 i = 1 ->
    etable_values is_i32_wrap_i64 i = 1.
Proof.
  (* This is a bug in zkWasm, they need to fix the contraints. *)
Admitted.

Lemma result_for_is_i32_wrap_i64 : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values is_i32_wrap_i64 i = 1 ->
    etable_values res i = 
    etable_values value_u16_cells_le_0 i + etable_values value_u16_cells_le_1 i * 2^16.
Proof.
  intros i Hrange Hops Hwrap.
  pose(H := op_conversion_i32_wrap_i64 i Hrange).
  simpl in *.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Lemma result_range_for_is_i32_wrap_i64 : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values is_i32_wrap_i64 i = 1 ->
    0 <= etable_values res i < 2^32.
Proof.
  intros i Hrange Hops Hwrap.
  rewrite (result_for_is_i32_wrap_i64 i Hrange Hops Hwrap).
  pose(Hu16 := value_U16_cells).
  destruct Hu16 as [H0 [H1 _]].
  specialize (H0 i).
  specialize (H1 i).
  lia.
Qed.

Lemma result_correct_for_wrap : forall i w_l,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values is_i32_wrap_i64 i = 1 ->
    etable_values value_u64_cell i = Wasm_int.Z_of_uint i64m w_l ->
    etable_values res i = Wasm_int.Z_of_uint i32m (wasm_wrap w_l).
Proof.
  intros i w_l Hrange Hops Hwrap Hval.
  rewrite (result_for_is_i32_wrap_i64 i Hrange Hops Hwrap).
  unfold wasm_wrap.
  rewrite <- Hval.
  simpl.
  unfold Wasm_int.Int32.Z_mod_modulus.
  pose(Hu64 := value_U64 i).
  pose(Hu16 := value_U16_cells).
  destruct Hu16 as [H0 [H1 [H2 H3]]].
  specialize (H0 i).
  specialize (H1 i).
  specialize (H2 i).
  specialize (H3 i).
  assert(Hvalrange : 0 <= etable_values value_u64_cell i < 2^64).
  - lia.
  rewrite Hval.
  destruct (Wasm_int.Z_of_uint i64m w_l).
  - lia.
  - rewrite (Zbits.P_mod_two_p_eq _ _).
    rewrite <- Hval.
    rewrite (two_power_nat_equiv _).
    unfold Wasm_int.Int32.wordsize.
    unfold Integers.Wordsize_32.wordsize.
    replace (Z.of_nat 32) with 32 by lia.
    rewrite Hu64.
    replace(etable_values value_u16_cells_le_0 i + etable_values value_u16_cells_le_1 i * 2 ^ 16 
    + etable_values value_u16_cells_le_2 i * 2^32 + etable_values value_u16_cells_le_3 i * 2^48)
    with ((etable_values value_u16_cells_le_0 i + etable_values value_u16_cells_le_1 i * 2 ^ 16) + 
    (etable_values value_u16_cells_le_2 i + etable_values value_u16_cells_le_3 i * 2^16) * 2^32) by lia.
    rewrite(Z_mod_plus _ _ _) by lia.
    rewrite(Z.mod_small _ _) by lia.
    simpl.
    reflexivity.
  - lia.
Qed.

Lemma shift_value : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    (etable_values value_is_i8 i = 1 -> etable_values shift i = 2^7) /\
    (etable_values value_is_i16 i = 1 -> etable_values shift i = 2^15) /\
    (etable_values value_is_i32 i = 1 -> etable_values shift i = 2^31) /\
    (etable_values value_is_i64 i = 1 -> etable_values shift i = 2^31).
Proof.
  intros i Hrange Hops Henabled.
  pose(H := op_conversion_helper i Hrange).
  simpl in *.
  replace(i+0) with i in * by lia.
  pose(Hval := only_one_value_type i Hrange Hops Henabled).
  lia.
Qed.

Lemma padding_value : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    (etable_values value_is_i8 i = 1 -> 
        (etable_values res_is_i64 i = 0 -> etable_values padding i = 0xFFFFFF00) /\
        (etable_values res_is_i64 i = 1 -> etable_values padding i = 0xFFFFFFFFFFFFFF00)) /\
    (etable_values value_is_i16 i = 1 -> 
        (etable_values res_is_i64 i = 0 -> etable_values padding i = 0xFFFF0000) /\
        (etable_values res_is_i64 i = 1 -> etable_values padding i = 0xFFFFFFFFFFFF0000)) /\
    (etable_values value_is_i32 i = 1 -> 
        etable_values res_is_i64 i = 1 -> etable_values padding i = 0xFFFFFFFF00000000) /\
    (etable_values value_is_i64 i = 1 ->
        etable_values res_is_i64 i = 1 -> etable_values padding i = 0xFFFFFFFF00000000).
Proof.
  intros i Hrange Hops Henabled.
  pose(H := op_conversion_helper i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  pose(Hval := only_one_value_type i Hrange Hops Henabled).
  lia.
Qed.

Lemma modulus_value : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values modulus i = etable_values shift i * 2.
Proof.
  intros i Hrange Hops.
  pose(H := op_conversion_helper i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Lemma rem_range : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    0 <= etable_values rem i < etable_values shift i.
Proof.
  intros i Hrange Hops.
  pose(H := op_conversion_split_operand i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  pose(Hrem := rem_U64 i).
  pose(Hremhelper := rem_helper_U64 i).
  lia.
Qed.

Lemma operand_division_by_shift : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    Z.div_eucl (etable_values value_u64_cell i) (etable_values shift i) =
    (etable_values d i * 2 + etable_values flag_bit i, etable_values rem i).
Proof.
  intros i Hrange Hops Henabled.
  rewrite (Zaux.Zdiv_eucl_unique _ _).
  pose(Hgate := op_conversion_split_operand i Hrange).
  simpl in Hgate.
  replace(i+0) with i in * by lia.
  destruct Hgate as [Hgate _].
  rewrite(modulus_value i Hrange Hops) in Hgate.
  assert(Hshift : etable_values shift i > 0).
  - pose(Hshiftval := shift_value i Hrange Hops).
    pose(Hval := only_one_value_type i Hrange Hops Henabled).
    lia.
  replace(etable_values value_u64_cell i) with
  ((etable_values d i * 2 + etable_values flag_bit i) * etable_values shift i + etable_values rem i) by lia.
  rewrite(Z.div_add_l _ _ _) by lia.
  rewrite(Z.div_small _ _) by apply (rem_range i Hrange Hops).
  rewrite(Z.add_comm _ (etable_values rem i)).
  rewrite(Z_mod_plus _ _ _) by apply Hshift.
  rewrite(Z.mod_small _ _) by apply (rem_range i Hrange Hops).
  rewrite(Z.add_0_r _).
  reflexivity.
Qed.

Lemma result_for_extension : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values res i = etable_values rem i +
    etable_values flag_bit i * etable_values shift i + (* most significant bit of value *)
    etable_values flag_bit i * etable_values padding i * etable_values sign_op i. (* sign extension *)
Proof.
  intros i Hrange Hops.
  pose(H := op_conversion_sign_extension i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.

(* Only unsigned extension is I64ExtendI32 *)
Lemma result_correct_for_unsigned_extension : forall i w_l,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    etable_values sign_op i = 0 ->
    etable_values value_is_i32 i = 1 ->
    etable_values value_u64_cell i = Wasm_int.Z_of_uint i32m w_l ->
    etable_values res i = Wasm_int.Z_of_uint i64m (wasm_extend_u w_l).
Proof.
  intros i w_l Hrange Hops Henabled Hsign Hi32 Hval.
  rewrite(result_for_extension i Hrange Hops).
  rewrite Hsign.
  rewrite(Z.mul_0_r _).
  rewrite(Z.add_0_r _).
  unfold wasm_extend_u.
  rewrite <- Hval.
  simpl.
  pose(Heucl := operand_division_by_shift i Hrange Hops).
  assert(Hnz : etable_values shift i <> 0).
  - pose(shift_value i Hrange Hops).
    pose(only_one_value_type i Hrange Hops Henabled).
    lia.
  pose(Hdiv := Z.div_eucl_eq (etable_values value_u64_cell i) (etable_values shift i) Hnz).
  rewrite Heucl in Hdiv; auto.
  rewrite Hdiv.
  assert(Hvalrange : etable_values value_u64_cell i < Wasm_int.Int32.modulus).
  - destruct w_l. 
    rewrite Hval.
    simpl.
    lia.
  unfold Wasm_int.Int32.modulus in Hvalrange.
  unfold Wasm_int.Int32.wordsize in Hvalrange.
  unfold Integers.Wordsize_32.wordsize in Hvalrange.
  rewrite(two_power_nat_equiv _) in Hvalrange.
  replace(Z.of_nat 32) with 32 in Hvalrange by lia.
  pose(Hshift := shift_value i Hrange Hops Henabled).
  destruct Hshift as [_ [_ [Hshift _]]].
  specialize (Hshift Hi32).
  pose(Hflag := flag_bit_bit i).
  pose(Hrem := rem_range i Hrange Hops).
  assert(Hd : etable_values d i = 0).
    - pose(d_U64 i).
      lia.
  rewrite Hd.
  rewrite(Z.mul_0_l _).
  rewrite(Z.add_0_l _).
  rewrite(Z.add_comm _ _).
  rewrite(Z.mul_comm _ _).
  pose(Hmod := Wasm_int.Int64.Z_mod_modulus_id).
  specialize (Hmod (etable_values shift i * etable_values flag_bit i + etable_values rem i)).
  assert(Hmodrange : -1 < etable_values shift i * etable_values flag_bit i + etable_values rem i < Wasm_int.Int64.modulus).
  - unfold Wasm_int.Int64.modulus.
    rewrite(two_power_nat_equiv _).
    unfold Wasm_int.Int64.wordsize.
    unfold Integers.Wordsize_64.wordsize.
    lia.
  specialize(Hmod Hmodrange).
  lia.
Qed.

Definition sign_extended i x := 
    (etable_values sign_op i) * (etable_values flag_bit i) * (etable_values padding i) 
    + x mod (etable_values modulus i).

Lemma Zodd_mod_2 : forall x, Z.odd (x mod 2) = Z.odd x.
Proof.
  intros x.
  pattern x at 2.
  rewrite (Coqlib.Z_div_mod_eq x 2) by lia.
  rewrite Z.add_comm.
  rewrite Z.odd_add_mul_2.
  reflexivity.
Qed.  

Lemma shift_nonnegative : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    0 <= etable_values shift i.
Proof.
  intros i Hrange Hops Henabled.
  destruct (shift_value i Hrange Hops) as [Hshift1 [Hshift2 [Hshift4 Hshift8]]]; auto.
  destruct (only_one_value_type i Hrange Hops Henabled) as [[H1 [H2 [H4 H8]]] | [[H1 [H2 [H4 H8]]] | [ [H1 [H2 [H4 [H8 H9]]]] | [H1 [H2 [H4 [H8 H9]]]]]]].
  - specialize (Hshift1 H1); lia.
  - specialize (Hshift2 H2); lia.
  - specialize (Hshift4 H4); lia.
  - specialize (Hshift8 H8); lia.
Qed.
  
Lemma leading_bit : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    Z.odd (etable_values flag_bit i)
      = Z.odd (((etable_values value_u64_cell i) mod (etable_values modulus i))  / (etable_values shift i)).
Proof.
  intros i Hrange Hops Henabled.
  assert (division := operand_division_by_shift i Hrange Hops Henabled).
  rewrite Zaux.Zdiv_eucl_unique in division.
  inversion division as [division1].
  rewrite modulus_value in * by auto.
  pose (shift_nonnegative i Hrange Hops Henabled).  
  rewrite Zaux.Zdiv_mod_mult by lia.
  rewrite Zodd_mod_2.  
  rewrite division1.
  replace (etable_values d i * 2 + etable_values flag_bit i)
    with (etable_values flag_bit i + 2 * etable_values d i) by lia.
  rewrite Z.odd_add_mul_2.
  reflexivity.
Qed.
  
Lemma leading_bit_8 : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    etable_values value_is_i8 i = 1 ->
    Z.odd (etable_values flag_bit i) = Z.odd (Z.shiftr (etable_values value_u64_cell i mod (etable_values modulus i)) 7).
Proof.
  intros i Hrange Hops Henabled Hi8.
  destruct (shift_value i Hrange  Hops Henabled) as [H _].
  specialize (H Hi8).
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite <- H.
  apply leading_bit; auto.
Qed.

Lemma leading_bit_16 : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    etable_values value_is_i16 i = 1 ->
    Z.odd (etable_values flag_bit i) = Z.odd (Z.shiftr (etable_values value_u64_cell i mod (etable_values modulus i)) 15).
Proof.
  intros i Hrange Hops Henabled Hi16.
  destruct (shift_value i Hrange  Hops Henabled) as [_ [H _]].
  specialize (H Hi16).
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite <- H.
  apply leading_bit; auto.
Qed.

Lemma leading_bit_32 : forall i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    etable_values value_is_i32 i = 1 ->
    Z.odd (etable_values flag_bit i) = Z.odd (Z.shiftr (etable_values value_u64_cell i mod (etable_values modulus i)) 31).
Proof.
  intros i Hrange Hops Henabled Hi32.
  destruct (shift_value i Hrange  Hops Henabled) as [_ [_ [H _]]].
  specialize (H Hi32).
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite <- H.
  apply leading_bit; auto.
Qed.


Definition modulus_value_ex : forall typ i,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    value_type_spec typ i ->
    etable_values modulus i = value_type_modulus typ.
Proof.
  intros typ i Hrange Hops Henabled Hvalue_type.
  assert (Hmodulus := modulus_value i Hrange Hops).
  destruct (shift_value i Hrange  Hops Henabled) as [Hshift_one [Hshift_two [Hshift_four Hshift_eight]]].
  destruct typ; destruct Hvalue_type as [Hone [Htwo [Hfour [Height _]]]].
  - specialize (Hshift_one Hone).
    rewrite Hshift_one in Hmodulus.
    rewrite Hmodulus.
    reflexivity.
  - specialize (Hshift_two Htwo).
    rewrite Hshift_two in Hmodulus.
    rewrite Hmodulus.
    reflexivity.
  - specialize (Hshift_four Hfour).
    rewrite Hshift_four in Hmodulus.
    rewrite Hmodulus.
    reflexivity.
  - specialize (Hshift_eight Height).
    rewrite Hshift_eight in Hmodulus.
    rewrite Hmodulus.
    reflexivity.
Qed.

Lemma sign_extended_correct: forall i (signed : bool) (src: ConvOpSrc) (res: ConvOpRes),
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->    
    value_type_spec src i ->
    result_type_spec res i ->
    etable_values sign_op i = (if signed then 1 else 0) ->
    (src = VAL32 -> res = RES64) ->
    (src <> VAL64) ->
    sign_extended i (etable_values value_u64_cell i)
     = sign_extend signed src res ((etable_values value_u64_cell i) mod (value_type_modulus src)).
Proof.
  intros i signed src res Hrange Hops Henabled Hvaltyp Hrestyp Hsigned Hforbid1 Hforbid2.
  rewrite <- (modulus_value_ex src i Hrange Hops Henabled Hvaltyp).
  destruct (padding_value i Hrange Hops Henabled) as [Hpadding_one [Hpadding_two [Hpadding_four Hpadding_eight]]].  
  destruct signed.
  - unfold sign_extended, sign_extend.
    rewrite Hsigned.
    destruct res.
    + destruct Hrestyp as [Hi32 Hi64].
      destruct src.
      * destruct Hvaltyp as [Hone [Htwo [Hfour Height]]].
         clear Hpadding_two Hpadding_four Hpadding_eight.
         destruct (Hpadding_one Hone) as [Hpadding _].
         specialize (Hpadding Hi64).      
         rewrite <- (leading_bit_8 i Hrange Hops Henabled Hone).
         destruct (flag_bit_bit i) as [Hflag | Hflag].
         ** rewrite Hflag. simpl. reflexivity.
         ** rewrite Hflag. rewrite Z.odd_1. rewrite Hpadding. lia.
      * destruct Hvaltyp as [Hone [Htwo [Hfour Height]]].
         clear Hpadding_one Hpadding_four Hpadding_eight.
         destruct (Hpadding_two Htwo) as [Hpadding _].
         specialize (Hpadding Hi64).      
         rewrite <- (leading_bit_16 i Hrange Hops Henabled Htwo).
         destruct (flag_bit_bit i) as [Hflag | Hflag].
         ** rewrite Hflag. simpl. reflexivity.
         ** rewrite Hflag. rewrite Z.odd_1. rewrite Hpadding. lia.
      * specialize (Hforbid1 eq_refl). congruence.
      * congruence.
    + destruct Hrestyp as [Hi32 [Hi64 _]].
      destruct src.
      * destruct Hvaltyp as [Hone [Htwo [Hfour [Height _]]]].
         clear Hpadding_two Hpadding_four Hpadding_eight.
         destruct (Hpadding_one Hone) as [_ Hpadding].
         specialize (Hpadding Hi64).      
         rewrite <- (leading_bit_8 i Hrange Hops Henabled Hone).
         destruct (flag_bit_bit i) as [Hflag | Hflag].
         ** rewrite Hflag. simpl. reflexivity.
         ** rewrite Hflag. rewrite Z.odd_1. rewrite Hpadding. lia.
      * destruct Hvaltyp as [Hone [Htwo [Hfour Height]]].
         clear Hpadding_one Hpadding_four Hpadding_eight.
         destruct (Hpadding_two Htwo) as [_ Hpadding].
         specialize (Hpadding Hi64).      
         rewrite <- (leading_bit_16 i Hrange Hops Henabled Htwo).
         destruct (flag_bit_bit i) as [Hflag | Hflag].
         ** rewrite Hflag. simpl. reflexivity.
         ** rewrite Hflag. rewrite Z.odd_1. rewrite Hpadding. lia.
      * destruct Hvaltyp as [Hone [Htwo [Hfour Height]]].
         clear Hpadding_one Hpadding_two Hpadding_eight.
         specialize (Hpadding_four Hfour Hi64).
         rewrite <- (leading_bit_32 i Hrange Hops Henabled Hfour).
         destruct (flag_bit_bit i) as [Hflag | Hflag].
         ** rewrite Hflag. simpl. reflexivity.
         ** rewrite Hflag. rewrite Z.odd_1. rewrite Hpadding_four. lia.            
      * congruence.
  - unfold sign_extended. simpl.
    rewrite Hsigned.
    lia.
Qed.
  
Lemma result_correct_for_extension : forall i w_l,
    0 <= i ->
    etable_values (ops_cell Conversion) i = 1 ->
    etable_values enabled_cell i = 1 ->
    etable_values value_u64_cell i = Wasm_int.Z_of_sint i32m w_l -> 
    etable_values res i = sign_extended i (Wasm_int.Z_of_sint i32m w_l).
Proof.
  intros i w_l Hrange Hops Henabled Hval.
  rewrite(result_for_extension i Hrange Hops).
  rewrite <- Hval.
  pose(Heucl := operand_division_by_shift i Hrange Hops).
  assert(Hnz : etable_values shift i <> 0).
  - pose(shift_value i Hrange Hops).
    pose(only_one_value_type i Hrange Hops).
    lia.
  pose(Hdiv := Z.div_eucl_eq (etable_values value_u64_cell i) (etable_values shift i) Hnz).
  rewrite Heucl in Hdiv; auto.
  rewrite Hdiv.
  unfold sign_extended.
  rewrite(modulus_value i Hrange Hops).
  replace(etable_values shift i * (etable_values d i * 2 + etable_values flag_bit i) + etable_values rem i) with
  (etable_values rem i + etable_values flag_bit i * etable_values shift i + etable_values d i * (etable_values shift i * 2)) by lia.
  rewrite(Z_mod_plus _ _ _).
  pose(flag_bit_bit i).
  pose(rem_range i Hrange Hops).
  rewrite(Z.mod_small _ _) by lia.
  lia.
  pose(Hshift := shift_value i Hrange Hops).
  pose(Htype := only_one_value_type i Hrange Hops Henabled).
  lia.
Qed.

Lemma conversionop_mops : forall i,
    0 <= i ->
    etable_values eid_cell i > 0 ->
    etable_values enabled_cell i = 1 ->
    etable_values (ops_cell Conversion) i = 1 ->
    mops_at_correct i ->
        mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with Conversion in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i Conversion Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).

  assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  {
    apply (write_cell_with_value_mops _ _ _ _ _ _ stack_write i Hrange); auto.
    - apply (eid_common i).
    - apply (res_is_i32_bit).
    - pose (sp_common i).
    - pose (sp_common i); lia.
  }
  lia.
Qed.
  
Theorem ConversionOp_Wrap_correct : forall i st x1 xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Conversion) i = 1 ->
  etable_values is_i32_wrap_i64 i = 1 ->
  state_rel i st ->
  wasm_stack st = Wasm_int.Z_of_uint i64m x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) (Wasm_int.Z_of_uint i32m (wasm_wrap x1):: xs)).
Proof.
  intros i st x1 xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (conversionop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hlhs: etable_values value_u64_cell i = Wasm_int.Z_of_uint i64m x1).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get value_type_is_i32)
                                 (enable := fun get => get (ops_cell Conversion))
                                 (value := fun get => get value_u64_cell).
    - apply Hrange.
    - apply Hop.
    - apply (value_type_is_i32_bit i).
    - eauto.
    - eauto.
    - apply stack_read.
  }
  assert (Hres: etable_values res i = Wasm_int.Z_of_uint i32m (wasm_wrap x1)).
  {
    apply (result_correct_for_wrap i x1 Hrange Hop Hop_class Hlhs).
  }
  rewrite <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Conversion); auto.
    rewrite iid_change with (idx := Conversion); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.
    
  eapply stack_rel_write_1 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get res_is_i32)
                                (enable := fun get => get (ops_cell Conversion)); auto; try lia.
  - apply (res_is_i32_bit i).
  - apply Hstk.
  - pose(Hsp := sp_change i Conversion Hrange Hrow_enabled Hop).
    replace(config_sp_diff (opcode_config Conversion i)) with 0 in Hsp by constructor.
    lia.
  - pose (mpages_change i Conversion); simpl in *; lia.    
  - rewrite (frame_id_change i Conversion); auto; reflexivity.
  - rewrite (fid_change i Conversion); auto.
  - apply stack_write.
Qed.

Theorem ConversionOp_Extend_correct : forall i (signed : bool) (srct: ConvOpSrc) (rest: ConvOpRes) st x1 xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Conversion) i = 1 ->
  value_type_spec srct i ->
  result_type_spec rest i ->
  etable_values sign_op i = (if signed then 1 else 0) ->
  (srct = VAL32 -> rest = RES64) ->
  (srct <> VAL64) ->
  state_rel i st ->
  wasm_stack st = Wasm_int.Z_of_sint i32m x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st)
                     (sign_extend signed srct rest ((Wasm_int.Z_of_sint i32m x1) mod (value_type_modulus srct)) :: xs)).
Proof.
  intros i signed srct rest st x1 xs Hrange Hrow_enabled Hmops Hop Hvaltyp Hrestyp Hsign Hforbid1 Hforbid2 Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (conversionop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Mops'']].
  assert (Hlhs: etable_values value_u64_cell i = Wasm_int.Z_of_sint i32m x1).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => get value_type_is_i32)
                                 (enable := fun get => get (ops_cell Conversion))
                                 (value := fun get => get value_u64_cell).
    - apply Hrange.
    - apply Hop.
    - apply (value_type_is_i32_bit i).
    - eauto.
    - eauto.
    - apply stack_read.
  }
  assert (Hres: etable_values res i = sign_extended i (Wasm_int.Z_of_sint i32m x1)).
  {
    apply (result_correct_for_extension i x1 Hrange Hop Hrow_enabled Hlhs).
  }
  rewrite <- Hlhs in Hres.
  erewrite sign_extended_correct in Hres by eauto.
  rewrite Hlhs in Hres.
  
  rewrite <-Hlhs in Hstk.  rewrite <-Hres. clear Hsign Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values res i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Conversion); auto.
    rewrite iid_change with (idx := Conversion); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values res i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.
    
  eapply stack_rel_write_1 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get res_is_i32)
                                (enable := fun get => get (ops_cell Conversion)); auto; try lia.
  - apply (res_is_i32_bit i).
  - apply Hstk.
  - pose(Hsp := sp_change i Conversion Hrange Hrow_enabled Hop).
    replace(config_sp_diff (opcode_config Conversion i)) with 0 in Hsp by constructor.
    lia.
  - pose (mpages_change i Conversion); simpl in *; lia.    
  - rewrite (frame_id_change i Conversion); auto; reflexivity.
  - rewrite (fid_change i Conversion); auto.
  - apply stack_write.
Qed.


Require Import ImageTableModel.
Require Import InjectivityHelper.

Lemma Conversion_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values ETableModel.enabled_cell i = 1 ->    
  etable_values (ops_cell Conversion) i = 1 ->
  exists (signed : bool) (srct: ConvOpSrc) (rest: ConvOpRes),
       value_type_spec srct i
    /\ result_type_spec rest i
    /\ etable_values sign_op i = (if signed then 1 else 0)
    /\ program (wasm_pc st) = IConversion signed (bool_of_Z (etable_values value_type_is_i32 i)) srct rest
    /\ (srct = VAL64 -> (rest = RES32 /\ etable_values is_i32_wrap_i64 i = 1))
    /\ (srct = VAL32 -> rest = RES64)
.
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct (only_one_value_type_ex i Hrange Hops Henabled) as [srctyp Hsrc].  
  destruct (only_one_result_type_ex i Hrange Hops Henabled) as [restyp Hres].
  exists (bool_of_Z (etable_values sign_op i)).
  exists srctyp.
  exists restyp.

  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i Conversion Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.

  split; auto.
  split; auto.
  split.
  { destruct (sign_op_bit i) as [Hsign | Hsign]; rewrite Hsign; reflexivity. }

  assert (Hsignbit :  (if bool_of_Z (etable_values sign_op i) then Z.shiftl 1 7 else 0) = ( etable_values sign_op i * Z.shiftl 1 7)).
  {
    destruct (sign_op_bit i) as [Hsign | Hsign]; rewrite Hsign; reflexivity.
  } 
  destruct srctyp; destruct restyp.
  - destruct Hsrc as [Hsel1 [Hsel2 [Hsel3 [Hsel4 Hsel5]]]].
    destruct Hres as [Hsel6 Hsel7].
    split.
    +  apply opcode_of_instruction_inj.
       rewrite <- Hopcode. clear Hopcode.
       unfold opcode_config, config_opcode, opcode_of_instruction, encode_conversion, encode_ConvOp.
       f_equal.
       rewrite Hsignbit.
       rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
       rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
       rewrite <- !Zplus_assoc.
       f_equal.
    + split; intros; congruence.
  - destruct Hsrc as [Hsel1 [Hsel2 [Hsel3 [Hsel4 Hsel5]]]].
    destruct Hres as [Hsel6 [Hsel7 Hsel8]].
    split.
    +  apply opcode_of_instruction_inj.
       rewrite <- Hopcode. clear Hopcode.
       unfold opcode_config, config_opcode, opcode_of_instruction, encode_conversion, encode_ConvOp.
       f_equal.
       rewrite Hsignbit.
       rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
       rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
       rewrite <- !Zplus_assoc.
       f_equal.
    + split; intros; congruence.
  - destruct Hsrc as [Hsel1 [Hsel2 [Hsel3 [Hsel4 Hsel5]]]].
    destruct Hres as [Hsel6 Hsel7].
    split.
    +  apply opcode_of_instruction_inj.
       rewrite <- Hopcode. clear Hopcode.
       unfold opcode_config, config_opcode, opcode_of_instruction, encode_conversion, encode_ConvOp.
       f_equal.
       rewrite Hsignbit.
       rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
       rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
       rewrite <- !Zplus_assoc.
       f_equal.
    + split; intros; congruence.
  - destruct Hsrc as [Hsel1 [Hsel2 [Hsel3 [Hsel4 Hsel5]]]].
    destruct Hres as [Hsel6 [Hsel7 Hsel8]].
    split.
    +  apply opcode_of_instruction_inj.
       rewrite <- Hopcode. clear Hopcode.
       unfold opcode_config, config_opcode, opcode_of_instruction, encode_conversion, encode_ConvOp.
       f_equal.
       rewrite Hsignbit.
       rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
       rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
       rewrite <- !Zplus_assoc.
       f_equal.
    + split; intros; congruence.

   - destruct Hsrc as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 Hsel5']]]]].
    destruct Hres as [Hsel6 Hsel7].
    split.
    +  apply opcode_of_instruction_inj.
       rewrite <- Hopcode. clear Hopcode.
       unfold opcode_config, config_opcode, opcode_of_instruction, encode_conversion, encode_ConvOp.
       f_equal.
       rewrite Hsignbit.
       rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
       rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
       rewrite <- !Zplus_assoc.
       f_equal.
    + split; intros; try congruence.
  - destruct Hsrc as [Hsel1 [Hsel2 [Hsel3 [Hsel4 [Hsel5 _]]]]].
    destruct Hres as [Hsel6 [Hsel7 _]].
    split.
    +  apply opcode_of_instruction_inj.
       rewrite <- Hopcode. clear Hopcode.
       unfold opcode_config, config_opcode, opcode_of_instruction, encode_conversion, encode_ConvOp.
       f_equal.
       rewrite Hsignbit.
       rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
       rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
       rewrite <- !Zplus_assoc.
       f_equal.
    + split;  intros; congruence.

  - destruct Hsrc as [Hsel1 [Hsel2 [Hsel3 [Hsel4 Hsel5]]]].
    destruct Hres as [Hsel6 Hsel7].
    split.
    +  apply opcode_of_instruction_inj.
       rewrite <- Hopcode. clear Hopcode.
       unfold opcode_config, config_opcode, opcode_of_instruction, encode_conversion, encode_ConvOp.
       f_equal.
       rewrite Hsignbit.
       rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
       rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
       rewrite <- !Zplus_assoc.
       f_equal.
    + split; auto.
      split. auto.
      apply res_and_value_for_is_i32_wrap_i64_only_if; auto.
      intros; congruence.
  - destruct Hsrc as [Hsel1 [Hsel2 [Hsel3 [Hsel4 Hsel5]]]].
    destruct Hres as [Hsel6 [Hsel7 Hsel8]].
    split.
    +  apply opcode_of_instruction_inj.
       rewrite <- Hopcode. clear Hopcode.
       unfold opcode_config, config_opcode, opcode_of_instruction, encode_conversion, encode_ConvOp.
       f_equal.
       rewrite Hsignbit.
       rewrite !CommonData.shiftl_1_n by (cbv - [ Z.le ] ; lia).
       rewrite !Hsel1, !Hsel2, !Hsel3, !Hsel4, !Hsel5, !Hsel6, !Hsel7.
       rewrite <- !Zplus_assoc.
       f_equal.
    + split;  intros; congruence.
Qed.
