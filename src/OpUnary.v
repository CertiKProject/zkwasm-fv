(* Copyright (C) CertiK 2024-2026 *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETable.
Require MTable.

Require Import OpUnaryModel.

(* Proofs about op_unary.rs. *)

Require Import Wasm.numerics.
Require Import IntegerFunctions.
Require Import BitTableModel.
Require BitTable.
Require Import Lia.
Require Import MTable.
Require Import Relation RelationHelper.

Theorem opcode_mops_correct_unary : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Unary i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config Unary i)) with 1.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  - apply MTable.mtable_write_mops with
      (offset := etable_values sp_cell i + 1)
      (is_i32 := etable_values is_i32 i)
      (value := etable_values result i); auto.
    apply (alloc_memory_table_lookup_write_cell_with_value_correct _ _ _ _ _ _ 
      stack_write i Hrange); auto.
    - apply eid_common.
    - apply is_i32_bit.
    - pose(sp_common i); lia.
  lia.
Qed.

Lemma single_selector : forall i,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    (etable_values is_ctz i = 1 /\ etable_values is_clz i = 0 /\ etable_values op_unary_is_popcnt i = 0)
 \/ (etable_values is_ctz i = 0 /\ etable_values is_clz i = 1 /\ etable_values op_unary_is_popcnt i = 0)
 \/ (etable_values is_ctz i = 0 /\ etable_values is_clz i = 0 /\ etable_values op_unary_is_popcnt i = 1).
Proof.
  intros i Hrange.
  pose(H := op_unary_selector i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  pose(is_clz_bit i).
  pose(is_ctz_bit i).
  pose(is_popcnt_bit i).
  lia.
Qed.

Require Import ImageTableModel.
Require Import InjectivityHelper.

Definition Unary_op i :=
  if (Z.eq_dec (etable_values is_ctz i) 1) then CTZ
  else if (Z.eq_dec (etable_values is_clz i) 1) then CLZ
  else POPCNT.

Lemma Unary_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->
  etable_values (ops_cell Unary) i = 1 ->
  exists op,
    op = Unary_op i
    /\ program (wasm_pc st) = IUnary (bool_of_Z (etable_values is_i32 i)) op
    /\ match op with
         CTZ => etable_values is_ctz i = 1
       | CLZ => etable_values is_clz i = 1
       | POPCNT => etable_values op_unary_is_popcnt i = 1  end.
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i Unary Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  destruct (single_selector i Hrange Hops) as [Hctz | [Hclz | Hpopcnt]].
  - exists CTZ.
    split. {
      unfold Unary_op.
      destruct Hctz as [H1 _].
      rewrite H1. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    replace (  Z.shiftl (Z_of_UnaryOp CTZ) OPCODE_ARG0_SHIFT +
                 Z.shiftl (Z_of_bool (bool_of_Z (etable_values is_i32 i))) OPCODE_ARG1_SHIFT)
      with   (Z.shiftl (Z_of_bool (bool_of_Z (etable_values is_i32 i))) OPCODE_ARG1_SHIFT
              + Z.shiftl (Z_of_UnaryOp CTZ) OPCODE_ARG0_SHIFT) by lia.
    rewrite bool_of_Z_simpl.
    2: { apply is_i32_bit. }
    rewrite CommonData.shiftl_1_n.
    2: { cbv - [ Z.le ] ; lia. }
    f_equal.
    destruct Hctz as [Hctz1 [Hctz2 Hctz3]].
    rewrite Hctz1, Hctz2, Hctz3.
    reflexivity.
  - exists CLZ.
    split. {
      unfold Unary_op.
      destruct Hclz as [H1 [H2 _]].
      rewrite H1, H2. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    replace (  Z.shiftl (Z_of_UnaryOp CLZ) OPCODE_ARG0_SHIFT +
                 Z.shiftl (Z_of_bool (bool_of_Z (etable_values is_i32 i))) OPCODE_ARG1_SHIFT)
      with   (Z.shiftl (Z_of_bool (bool_of_Z (etable_values is_i32 i))) OPCODE_ARG1_SHIFT
              + Z.shiftl (Z_of_UnaryOp CLZ) OPCODE_ARG0_SHIFT) by lia.
    rewrite bool_of_Z_simpl.
    2: { apply is_i32_bit. }
    rewrite CommonData.shiftl_1_n.
    2: { cbv - [ Z.le ] ; lia. }
    f_equal.
    destruct Hclz as [Hctz1 [Hctz2 Hctz3]].
    rewrite Hctz1, Hctz2, Hctz3.
    reflexivity.
  - exists POPCNT.
    split. {
      unfold Unary_op.
      destruct Hpopcnt as [H1 [H2 _]].
      rewrite H1, H2. reflexivity. }
    split; [|now tauto].
    apply opcode_of_instruction_inj.
    rewrite <- Hopcode. clear Hopcode.
    unfold opcode_config, config_opcode, opcode_of_instruction.
    rewrite <- !Zplus_assoc.
    f_equal.
    replace (  Z.shiftl (Z_of_UnaryOp POPCNT) OPCODE_ARG0_SHIFT +
                 Z.shiftl (Z_of_bool (bool_of_Z (etable_values is_i32 i))) OPCODE_ARG1_SHIFT)
      with   (Z.shiftl (Z_of_bool (bool_of_Z (etable_values is_i32 i))) OPCODE_ARG1_SHIFT
              + Z.shiftl (Z_of_UnaryOp POPCNT) OPCODE_ARG0_SHIFT) by lia.
    rewrite bool_of_Z_simpl.
    2: { apply is_i32_bit. }
    rewrite CommonData.shiftl_1_n.
    2: { cbv - [ Z.le ] ; lia. }
    f_equal.
    destruct Hpopcnt as [Hctz1 [Hctz2 Hctz3]].
    rewrite Hctz1, Hctz2, Hctz3.
    reflexivity.
Qed.

Lemma operand_is_zero_and_operand : forall i,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    etable_values operand_is_zero i = 1 ->
    etable_values operand i = 0.
Proof.
  intros i Hrange.
  pose(H := op_unary_zero_cond i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  lia.
Qed.

Lemma operand_is_not_zero_and_operand : forall i,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    etable_values operand_is_zero i = 0 ->
    etable_values operand i <> 0.
Proof.
  intros i Hrange.
  pose(H := op_unary_zero_cond i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  lia.
Qed.

Lemma bits_values : forall i,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    etable_values bits i = 32 \/ etable_values bits i = 64.
Proof.
  intros i Hrange Hop.
  pose(H := op_unary_bits_gate i Hrange).
  pose(Hbit := is_i32_bit i).
  simpl in *.
  replace (i+0) with i in * by lia.
  destruct Hbit.
  - rewrite H0 in H. lia.
  - rewrite H0 in H. lia.
Qed.

Lemma lookup_pow_values : forall i,
    0 <= i ->
    (etable_values lookup_pow_power i <> 0 \/ etable_values lookup_pow_modulus i <> 0) ->
    128 <= etable_values lookup_pow_power i < 256 /\
      etable_values lookup_pow_modulus i = 2^(etable_values lookup_pow_power i - 128).
Proof.
  intros i Hrange Hnonzero.
  assert (Hin:=ETableModel.c8d i Hrange).
  apply RTable.in_op_table_power in Hin; auto.
Qed.

(* Clz proofs *)
Lemma clz_value_for_operand_is_zero : forall i,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    etable_values is_clz i = 1 ->
    etable_values operand_is_zero i = 1 ->
    etable_values result i = etable_values bits i.
Proof.
  intros i Hrange Hop Hclz Hiszero.
  pose(H := op_unary_clz i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  destruct H as [? _].
  lia.
Qed.

Lemma clz_aux1_range : forall i,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    etable_values is_clz i = 1 ->
    etable_values operand_is_zero i = 0 ->
    0 <= etable_values aux1 i < etable_values lookup_pow_modulus i.
Proof.
  intros i Hrange Hop Hclz Hiszero.
  pose(H := op_unary_clz i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  destruct H as [_ [_ [? _]]].
  rewrite Hiszero in H.
  simpl in H.
  pose(Haux1 := is64_aux1 i).
  pose(Haux2 := is64_aux2 i).
  lia.
Qed.

Lemma clz_division_theorem : forall i,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    etable_values is_clz i = 1 ->
    etable_values operand_is_zero i = 0 ->
    Z.div_eucl (etable_values operand i) (etable_values lookup_pow_modulus i) 
    = (1, etable_values aux1 i).
Proof.
  intros i Hrange Hop Hclz Hiszero.
  pose(Haux1 := clz_aux1_range i Hrange Hop Hclz Hiszero).
  destruct (lookup_pow_values i Hrange ltac:(lia)) as [Hpower Hmodulus].   
  pose(H := op_unary_clz i Hrange).
  simpl in H.
  destruct H as [_ [? _]].
  replace (i+0) with i in * by lia.
  rewrite Hiszero in H.
  simpl in H.
  assert(etable_values operand i = etable_values lookup_pow_modulus i + etable_values aux1 i).
  - lia.
  clear H.
  pose(Hunique := Zaux.Zdiv_eucl_unique (etable_values operand i) (etable_values lookup_pow_modulus i)).
  assert(1 = etable_values operand i / (etable_values lookup_pow_modulus i)).
  - pose(Z.div_unique (etable_values operand i) (etable_values lookup_pow_modulus i) 1 (etable_values aux1 i)).
    apply e.
    left. apply Haux1.
    lia.
  replace (etable_values operand i / etable_values lookup_pow_modulus i) with 1 in Hunique.
  assert(etable_values aux1 i = etable_values operand i mod (etable_values lookup_pow_modulus i)). 
  - pose(Z.mod_unique (etable_values operand i) (etable_values lookup_pow_modulus i) 1 (etable_values aux1 i)).
    apply e.
    left. apply Haux1.
    lia.
  replace (etable_values operand i mod (etable_values lookup_pow_modulus i)) with (etable_values aux1 i) in Hunique.
  apply Hunique.
Qed.

Lemma clz_value_for_operand_is_not_zero : forall i,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    etable_values is_clz i = 1 ->
    etable_values operand_is_zero i = 0 ->
    0 <=  (etable_values operand i) < Wasm_int.Int64.modulus ->
    etable_values result i = clz_64 (etable_values operand i) - (etable_values is_i32 i * 32).
Proof.
  intros i Hrange Hops Hclz Hiszero Hoperand_range.
  pose(H := op_unary_clz i Hrange).
  simpl in H.
  pose(Hbits := op_unary_bits_gate i Hrange).
  simpl in Hbits.
  replace (i+0) with i in * by lia.
  rewrite Hiszero in H.
  simpl in H.
  destruct H as [_ [Hdiv [_ [Hres _]]]].
  pose(Haux := clz_aux1_range i Hrange Hops Hclz Hiszero).
  pose(lookup_pow_values i Hrange).
  assert(clz_64 (etable_values operand i) = 64 - (etable_values lookup_pow_power i - 128) - 1).
  - apply (clz_64_value (etable_values operand i) (etable_values lookup_pow_power i - 128) (etable_values aux1 i)).
    {
      destruct (is64_aux1 i) as [Haux1_nonzero Haux1_upper].
      assert (etable_values operand i = 2 ^ (etable_values lookup_pow_power i - 128) + etable_values aux1 i) by lia.
      assert (2 ^ (etable_values lookup_pow_power i - 128) <= etable_values operand i) by lia.
      assert (Hexp_lt: 2 ^ (etable_values lookup_pow_power i - 128) < 2 ^ 64).
      { unfold Wasm_int.Int64.modulus in Hoperand_range.
        change Wasm_int.Int64.wordsize with 64%nat in Hoperand_range.
        rewrite two_power_nat_correct, Zpower_nat_Z in Hoperand_range.
        change (Z.of_nat 64)%nat with 64 in Hoperand_range.
        lia.
      }
      rewrite <- Z.pow_lt_mono_r_iff in Hexp_lt by lia.
      lia.
    }
    lia. lia. 
  rewrite H.
  assert(etable_values result i = etable_values bits i - etable_values lookup_pow_power i + 127).
  - lia.
  rewrite H0.
  pose(Hbit := is_i32_bit i).
  destruct Hbit.
  - rewrite H1 in *. 
    replace (etable_values bits i) with 64 by lia. 
    lia.
  - rewrite H1 in *.
    replace (etable_values bits i) with 32 by lia.
    lia.
Qed.

Lemma clz_result_correct : forall i w_l,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    etable_values is_clz i = 1 ->
    etable_values operand i = Wasm_int.Z_of_uint i64m w_l ->
    etable_values result i = Wasm_int.Z_of_uint i64m (Wasm_int.Int64.clz w_l) - (etable_values is_i32 i) * 32.
Proof.
  intros i w_l Hrange Hops Hclz Hoperand.
  pose(Hiszero := operand_is_zero_bit i).
  pose(Hdef := clz_64_definition_matches_wasm w_l).
  assert (Hoperand_range : 0 <= etable_values operand i < Wasm_int.Int64.modulus).
  {
    simpl in Hoperand.
    rewrite Hoperand.
    assert (H:= Wasm_int.Int64.unsigned_range_2 w_l).
    unfold  Wasm_int.Int64.max_unsigned in H.
    lia.
  }
  destruct Hiszero as [Hisnotzero | Hiszero].
  - pose(Hval := clz_value_for_operand_is_not_zero i Hrange Hops Hclz Hisnotzero Hoperand_range).
    rewrite Hval.
    pose(Hbit := is_i32_bit i).
    destruct Hbit as [Hbit0 | Hbit1].
    + rewrite Hbit0.
      rewrite Hoperand.
      lia.
    + rewrite Hbit1.
      rewrite Hoperand.
      lia.
  - pose(Hval := clz_value_for_operand_is_zero i Hrange Hops Hclz Hiszero).
    rewrite Hval.
    pose(Hop := operand_is_zero_and_operand i Hrange Hops Hiszero).
    rewrite <- Hdef.
    rewrite <- Hoperand.
    rewrite Hop.
    pose(Hclzval := clz_64_value 0 0 0).
    replace (clz_64 0) with 64 by lia.
    pose(Hbits := op_unary_bits_gate i Hrange).
    simpl in Hbits.
    replace (i+0) with i in Hbits by lia.
    pose(Hbit := is_i32_bit i).
    destruct Hbit as [Hbit0 | Hbit1].
    + rewrite Hbit0 in Hbits.
      lia.
    + rewrite Hbit1 in Hbits.
      lia.
Qed.

(* Ctz proofs *)
Lemma ctz_value_for_operand_is_zero : forall i,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    etable_values is_ctz i = 1 ->
    etable_values operand_is_zero i = 1 ->
    etable_values result i = etable_values bits i.
Proof.
  intros i Hrange Hops Hctz Hiszero.
  pose(H := op_unary_ctz i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  lia.
Qed.

Lemma ctz_degree_helper_range : forall i,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    etable_values is_ctz i = 1 ->
    etable_values ctz_degree_helper i = 0 \/ 
    etable_values ctz_degree_helper i > etable_values lookup_pow_modulus i.
Proof.
  intros i Hrange Hops Hctz.
  pose(H := op_unary_ctz i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  destruct H as [? _].
  rewrite Hops, Hctz in H.
  pose(is64_aux1 i).
  destruct a as [Haux _].
  destruct (Z.eq_dec (etable_values ctz_degree_helper i) 0)  as [l|l]; [left;lia |].
  assert (a:= lookup_pow_values i Hrange ltac:(lia)).
  assert(etable_values lookup_pow_modulus i > 0).
  - lia.
  case_eq (etable_values aux1 i).
  - lia.
  - intros Hpos Hauxp. right.
    assert(etable_values ctz_degree_helper i = etable_values aux1 i * etable_values lookup_pow_modulus i * 2).
    lia.
    rewrite H1.
    assert(etable_values aux1 i * 2 > 1).
    lia. 
    replace(etable_values lookup_pow_modulus i) with (etable_values lookup_pow_modulus i * 1) by lia.
    replace(etable_values aux1 i * (etable_values lookup_pow_modulus i * 1) * 2) with (etable_values lookup_pow_modulus i * (etable_values aux1 i * 2)) by lia.
    apply (Zmult_gt_compat_l (etable_values aux1 i * 2) 1 (etable_values lookup_pow_modulus i)).
    apply H0. apply H2.
  - intros Hneg Hauxn.
    assert(0 > etable_values aux1 i).
    lia.
    contradiction.
Qed.

Lemma result_nonnegative: forall i,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    0 <= etable_values result i.
Proof.
  intros i Hrange Hops.
  destruct (write_with_value_range
                 memory_table_lookup_stack_write i
                 (fun get => get sp_cell + 1)
                 (fun get => get is_i32)
                 (fun get => get (ops_cell Unary))
                 MTableModel.LocationType_Stack).
  - auto.
  - pose (sp_common i); lia.
  - pose (is_i32_bit i); lia.
  - auto.
  - auto.
  - apply stack_write.
  - lia.
Qed.

Opaque Z.add Z.sub Z.mul.

Lemma ctz_value_for_operand_is_not_zero : forall i (b : bool),
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    etable_values is_ctz i = 1 ->
    etable_values operand_is_zero i = 0 ->
    0 <= etable_values operand i < 2 ^ (if b then 32 else 64) ->
    etable_values result i = ctz (etable_values operand i) b.
Proof.
  intros i b Hrange Hops Hctz Hiszero Hoprange.
  pose(H := op_unary_ctz i Hrange).
  simpl in H.
  replace (i+0) with i in * by lia.
  destruct H as [Hdegree_helper [_ [Hdecomp [Hres _]]]].
  rewrite Hops, Hiszero, Hctz in *.
  simpl in *.
  assert (Hpower_nonzero : (etable_values lookup_pow_power i) > 0).
  {
    assert (0 <= etable_values result i) by (apply result_nonnegative; auto).
    lia.
  }
  assert (Hlookup_pow := lookup_pow_values i Hrange ltac:(lia)).
  destruct Hlookup_pow as [Hlookup_pow1 Hlookup_pow2].
  assert (ctz (etable_values operand i) b = etable_values lookup_pow_power i - 128).
  {

    apply (IntegerFunctions.ctz_value  (etable_values operand i) (etable_values lookup_pow_power i - 128) (etable_values aux1 i)).
    - lia.
    - lia.
    - pose (is64_aux1 i).  lia.
    - rewrite Z.pow_add_r by lia.
      change (2^1) with 2.
      rewrite Z.mul_assoc.
      lia.
  }
  rewrite H.
  lia.
Qed.

Lemma ctz_64_result_correct : forall i w_l,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    etable_values is_ctz i = 1 ->
    etable_values is_i32 i = 0 ->
    etable_values operand i = Wasm_int.Z_of_uint i64m w_l ->
    etable_values result i = Wasm_int.Z_of_uint i64m (Wasm_int.Int64.ctz w_l).
Proof.
  intros i w_l Hrange Hops Hctz Hi32 Hoperand.
  pose(Hiszero := operand_is_zero_bit i).
  pose(Hdef := ctz_64_definition_matches_wasm w_l).
  destruct Hiszero as [Hisnotzero | Hiszero].
  - pose(Hval := ctz_value_for_operand_is_not_zero i false Hrange Hops Hctz Hisnotzero).
    rewrite Hval.
    { rewrite Hoperand.
      apply Hdef. }
    { rewrite Hoperand.
      rewrite Z_of_Wasm64_uint_spec.
      destruct w_l as [w_l w_l_p].
      simpl.
      change  Wasm_int.Int64.modulus with (Z.pow_pos 2 64) in w_l_p.
      lia.
    }      
  - pose(Hval := ctz_value_for_operand_is_zero i Hrange Hops Hctz Hiszero).
    rewrite Hval.
    rewrite <- Hdef.
    rewrite <- Hoperand.
    rewrite(operand_is_zero_and_operand i Hrange Hops Hiszero).
    change (ctz 0 false) with 64.
    pose(Hbits := op_unary_bits_gate i Hrange).
    simpl in Hbits.
    replace (i+0) with i in Hbits by lia.
    rewrite Hi32 in Hbits.
    lia.
Qed.

Lemma ctz_32_result_correct : forall i w_l,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    etable_values is_ctz i = 1 ->
    etable_values is_i32 i = 1 ->
    etable_values operand i = Wasm_int.Z_of_uint i32m w_l ->
    etable_values result i = Wasm_int.Z_of_uint i32m (Wasm_int.Int32.ctz w_l).
Proof.
  intros i w_l Hrange Hops Hctz Hi32 Hoperand.
  pose(Hiszero := operand_is_zero_bit i).
  pose(Hdef := ctz_32_definition_matches_wasm w_l).
  destruct Hiszero as [Hisnotzero | Hiszero].
  - pose(Hval := ctz_value_for_operand_is_not_zero i true Hrange Hops Hctz Hisnotzero).
    rewrite Hval.
    { rewrite Hoperand.
      apply Hdef. }
    { rewrite Hoperand.
      rewrite Z_of_Wasm32_uint_spec.
      destruct w_l as [w_l w_l_p].
      simpl.
      change  Wasm_int.Int32.modulus with (Z.pow_pos 2 32) in w_l_p.
      lia.
    }      
  - pose(Hval := ctz_value_for_operand_is_zero i Hrange Hops Hctz Hiszero).
    rewrite Hval.
    rewrite <- Hdef.
    rewrite <- Hoperand.
    rewrite(operand_is_zero_and_operand i Hrange Hops Hiszero).
    change (ctz 0 true) with 32.
    pose(Hbits := op_unary_bits_gate i Hrange).
    simpl in Hbits.
    replace (i+0) with i in Hbits by lia.
    rewrite Hi32 in Hbits.
    lia.
Qed.

(* Popcnt proofs *)
Lemma lookup_val : forall i,
    0 <= i ->
    etable_values (ops_cell Unary) i = 1 ->
    etable_values op_unary_is_popcnt i = 1 ->
    exists j,
       0 <= j
       /\ value bit_table block_sel (j + 1) = 1
       /\ value bit_table op j              = popcnt_op_class
       /\ value bit_table val_l j           = etable_values operand      i
       /\ value bit_table val_r j           = 0
       /\ value bit_table val_res j         = etable_values result      i.
Proof.
  intros i Hrange Hop.
  destruct (c8f i Hrange) as [j Hc8f].
  exists j.
  assert (Hlookup := op_unary_popcnt_lookup i Hrange).
  simpl in Hlookup.
  replace (i+0) with i in * by lia.
  lia.
Qed.

(* Stack related proofs *)
Lemma unaryop_mops : forall i,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    etable_values (ops_cell Unary) i = 1 ->
    mops_at_correct i ->
       mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\ mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with Unary in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i Unary Hrow_enabled)); auto.
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

Theorem UnaryOp_Clz_correct : forall i st x1 xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Unary) i = 1 ->
  etable_values is_clz i = 1 ->
  state_rel i st ->
  wasm_stack st = Wasm_int.Z_of_uint i64m x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_clz i64m x1) - (etable_values is_i32 i) * 32:: xs)).
Proof.
  intros i st x1 xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (unaryop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hlhs: etable_values operand i = Wasm_int.Z_of_uint i64m x1).
  {
    eapply stack_rel_read_1 with (is_i32 := fun get => get is_i32)
                                 (enable := fun get => get (ops_cell Unary)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - eauto.
    - apply stack_read.
  }
  assert (Hres: etable_values result i = Wasm_int.Z_of_uint i64m (Wasm_int.int_clz i64m x1) - (etable_values is_i32 i) * 32).
  {
    apply (clz_result_correct i x1 Hrange Hop Hop_class Hlhs).
  }
  rewrite <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values result i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Unary); auto.
    rewrite iid_change with (idx := Unary); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values result i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_1 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get op_unary_is_i32)
                                (enable := fun get => get (ops_cell Unary)); auto; try lia.
  - apply (is_i32_bit i).
  - apply Hstk.
  - pose(Hsp := sp_change i Unary Hrange Hrow_enabled Hop).
    replace(config_sp_diff (opcode_config Unary i)) with 0 in Hsp by constructor.
    lia.
  - pose (mpages_change i Unary); simpl in *; lia.
  - rewrite (frame_id_change i Unary); auto; reflexivity.
  - rewrite (fid_change i Unary); auto.
  - apply stack_write.
Qed.

Theorem UnaryOp_Ctz_64_correct : forall i st x1 xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Unary) i = 1 ->
  etable_values is_ctz i = 1 ->
  etable_values is_i32 i = 0 ->
  state_rel i st ->
  wasm_stack st = Wasm_int.Z_of_uint i64m x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_ctz i64m x1):: xs)).
Proof.
  intros i st x1 xs Hrange Hrow_enabled Hmops Hop Hop_class Hi32 Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (unaryop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hlhs: etable_values operand i = Wasm_int.Z_of_uint i64m x1).
  {
    eapply stack_rel_read_1 with (is_i32 := fun get => get is_i32)
                                 (enable := fun get => get (ops_cell Unary)).
    - apply Hrange.
    - apply Hop.
    - auto.
    - eauto.
    - eauto.
    - apply stack_read.
  }
  assert (Hres: etable_values result i = Wasm_int.Z_of_uint i64m (Wasm_int.int_ctz i64m x1)).
  {
    apply (ctz_64_result_correct i x1 Hrange Hop Hop_class Hi32 Hlhs).
  }
  rewrite <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values result i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Unary); auto.
    rewrite iid_change with (idx := Unary); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values result i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_1 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get op_unary_is_i32)
                                (enable := fun get => get (ops_cell Unary)); auto; try lia.
  - apply Hstk.
  - pose(Hsp := sp_change i Unary Hrange Hrow_enabled Hop).
    replace(config_sp_diff (opcode_config Unary i)) with 0 in Hsp by constructor.
    lia.
  - pose (mpages_change i Unary); simpl in *; lia.
  - rewrite (frame_id_change i Unary); auto; reflexivity.
  - rewrite (fid_change i Unary); auto.
  - apply stack_write.
Qed.

Theorem UnaryOp_Ctz_32_correct : forall i st x1 xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Unary) i = 1 ->
  etable_values is_ctz i = 1 ->
  etable_values is_i32 i = 1 ->
  state_rel i st ->
  wasm_stack st = Wasm_int.Z_of_uint i32m x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) (Wasm_int.Z_of_uint i32m (Wasm_int.int_ctz i32m x1):: xs)).
Proof.
  intros i st x1 xs Hrange Hrow_enabled Hmops Hop Hop_class Hi32 Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (unaryop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hlhs: etable_values operand i = Wasm_int.Z_of_uint i32m x1).
  {
    eapply stack_rel_read_1 with (is_i32 := fun get => get is_i32)
                                 (enable := fun get => get (ops_cell Unary)).
    - apply Hrange.
    - apply Hop.
    - auto.
    - eauto.
    - eauto.
    - apply stack_read.
  }
  assert (Hres: etable_values result i = Wasm_int.Z_of_uint i32m (Wasm_int.int_ctz i32m x1)).
  {
    apply (ctz_32_result_correct i x1 Hrange Hop Hop_class Hi32 Hlhs).
  }
  rewrite <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values result i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Unary); auto.
    rewrite iid_change with (idx := Unary); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values result i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_1 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get op_unary_is_i32)
                                (enable := fun get => get (ops_cell Unary)); auto; try lia.
  - apply Hstk.
  - pose(Hsp := sp_change i Unary Hrange Hrow_enabled Hop).
    replace(config_sp_diff (opcode_config Unary i)) with 0 in Hsp by constructor.
    lia.
  - pose (mpages_change i Unary); simpl in *; lia.
  - rewrite (frame_id_change i Unary); auto; reflexivity.
  - rewrite (fid_change i Unary); auto.
  - apply stack_write.
Qed.

Theorem UnaryOp_Popcnt_correct : forall i st x1 xs,
  0 <= i ->
  (etable_values enabled_cell i) = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell Unary) i = 1 ->
  etable_values op_unary_is_popcnt i = 1 ->
  state_rel i st ->
  wasm_stack st = Wasm_int.Z_of_uint i64m x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_popcnt i64m x1):: xs)).
Proof.
  intros i st x1 xs Hrange Hrow_enabled Hmops Hop Hop_class Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (unaryop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].    
  assert (Hlhs: etable_values operand i = Wasm_int.Z_of_uint i64m x1).
  {
    eapply stack_rel_read_1 with (is_i32 := fun get => get is_i32)
                                 (enable := fun get => get (ops_cell Unary)).
    - apply Hrange.
    - apply Hop.
    - apply (is_i32_bit i).
    - eauto.
    - eauto.
    - apply stack_read. }
  assert (Hres: etable_values result i = Wasm_int.Z_of_uint i64m (Wasm_int.int_popcnt i64m x1)).
  {
    destruct (lookup_val i Hrange Hop) as [j [Hbit1 [Hbit2 [Hbit3 [Hbit4 [Hbit5 Hbit6]]]]]].
    - apply Hop_class.
    - rewrite Hlhs in *.
      rewrite <-  Hbit6.
      pose (BitTable.in_bit_table_popcnt _ _ Hbit1 Hbit2 Hbit3 Hbit4 Hbit5).
      congruence.
  }
  rewrite <-Hlhs in Hstk.  rewrite <-Hres. clear Hop_class Hlhs Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values result i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := Unary); auto.
    rewrite iid_change with (idx := Unary); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values result i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.
    
  eapply stack_rel_write_1 with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => get op_unary_is_i32)
                                (enable := fun get => get (ops_cell Unary)); auto; try lia.
  - apply (is_i32_bit i).
  - apply Hstk.
  - pose(Hsp := sp_change i Unary Hrange Hrow_enabled Hop).
    replace(config_sp_diff (opcode_config Unary i)) with 0 in Hsp by constructor.
    lia.
  - pose (mpages_change i Unary); simpl in *; lia.
  - rewrite (frame_id_change i Unary); auto; reflexivity.
  - rewrite (fid_change i Unary); auto.
  - apply stack_write.
Qed.    
