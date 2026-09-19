(* Copyright (C) CertiK 2024-2026 *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import Wasm.numerics.
Require        Wasm.datatypes.
Require Import Lia.

Require MTableModel MTable JTableModel JTable.

Require Export ETableModel.

(* Doesn't have to be a tight bound, it's used to prove rest_mops
    doesn't overflow. *)
Definition max_mops := 10.
Lemma max_mops_correct : forall o i,
    0 <= config_mops (opcode_config o i) < max_mops.
Proof.
  intros o i.
  unfold max_mops; destruct o; simpl; try lia.
  - pose(op_br_if_eqz_cond_is_zero_cell_bit i).
    pose(op_br_if_eqz_keep_cell_bit i).
    lia.
  - pose(op_br_if_cond_is_not_zero_cell_bit i).
    pose(op_br_if_keep_cell_bit i).
    lia.
  - pose(op_br_keep_cell_bit i); lia.
  - pose(op_return_keep_cell_bit i); lia.
  - destruct(op_store_is_cross_block_bit i); rewrite H; lia.
  - pose(op_br_table_keep_bit i); lia.
Qed.


(***** Definitions/lemmas about counting mops. *)

Lemma enabled_seq : forall i,
    0 <= i ->
    etable_values enabled_cell i = 0 ->
    etable_values enabled_cell (i+1) = 0.
Proof.
  intros i Hrange H.
  destruct (gate_c1 i Hrange) as [G _].
  replace (i+0) with i in * by lia.
  unfold value in *.
  simpl in *.
  lia.
Qed.
  
Definition instruction_mops i :=
  if (etable_values enabled_cell i =? 1) 
      then config_mops (opcode_config (class_of_row i) i)
      else 0. 

Fixpoint instructions_mops' i n :=
  match n with
  | O => 0
  | S n' =>
      instruction_mops i + instructions_mops' (i+1) n'
  end.

(* The sum of all the intended mops of the instructions in rows `i`-`etable_numRow`.   *)
Definition instructions_mops (i : Z) : Z :=
  instructions_mops' i (Z.to_nat (etable_numRow - i)).

Lemma rest_mops_correct' : forall n i,
    0 <= i ->
    i + Z.of_nat n = etable_numRow ->
    etable_values rest_mops_cell i <= instructions_mops' i n.
Proof.
  induction n.
  - simpl.
    intros.
    replace i with etable_numRow by lia.
    rewrite rest_mops_terminates. lia.
  - intros i Hrange H.
    replace (i + Z.of_nat (S n)) with (i+1 + Z.of_nat n) in * by lia.
    simpl.
    specialize (IHn (i+1) ltac:(lia) H).
    unfold instruction_mops.
    destruct (enabled_bit i) as [Henabled|Henabled]; rewrite Henabled.
    + rewrite (proj2 (Z.eqb_neq 0 1)) by lia.
      rewrite rest_mops_change_disabled; auto.
    + rewrite Z.eqb_refl.
      destruct (class_of_row_op i (class_of_row i) Henabled) as [_ Hclass].
      rewrite (rest_mops_change_enabled i (class_of_row i) Hrange Henabled (Hclass eq_refl)).
      lia.
Qed.

(* In most cases, rest_mops[i] = instructions_mops(i).
   The inequality would happen if the final row of the etable had enabled=1,
   in which case the rest_mops_change gate for the final row would not apply
   and the mops for that instruction would not be counted. *)
Lemma rest_mops_correct : forall i,
    0 <= i <= etable_numRow ->
    etable_values rest_mops_cell i <= instructions_mops i.
Proof.
  unfold instructions_mops. intros.
  apply rest_mops_correct'; lia.
Qed.

Definition opcode_mops_correct (c : OpcodeClass) i :=
    etable_values (ops_cell c) i = 1 ->
      MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack
    + MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap
    + MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Global
    >= config_mops (opcode_config c i).

Lemma enabled_seq_mono : forall n,
    etable_values enabled_cell (Z.of_nat n) = 1 ->
    forall m,  (m < n)%nat ->
               etable_values enabled_cell (Z.of_nat m) = 1.
Proof.
  induction n; intros Henabled m Hlt.
  - inversion Hlt.
  - destruct (enabled_bit (Z.of_nat n)).
    + replace (Z.of_nat (S n)) with (Z.of_nat n +1) in Henabled by lia.
      apply enabled_seq in H; lia.
    + inversion Hlt; subst.
      * auto.
      * apply IHn.
        auto.
        lia.
Qed.

Lemma enabled_seq_backwards' : forall n i,
    0 <= i ->
    etable_values enabled_cell (i + Z.of_nat n) = 1 ->
    etable_values enabled_cell i = 1.
Proof.
  induction n.
  - simpl. intros. replace (i+0) with i in * by lia. auto.
  - intros i Hrange H.
    replace (i + Z.of_nat (S n)) with  (i + 1 + Z.of_nat n) in H by lia.
    specialize (IHn (i+1) ltac:(lia) H).
    destruct (enabled_bit i) as [e | e].
    + apply enabled_seq in e; congruence.
    + auto.
Qed.

Lemma enabled_seq_backwards : forall i j,
    0 <= i <= j ->
    etable_values enabled_cell j = 1 ->
    etable_values enabled_cell i = 1.
Proof.
  intros i j Hrange H.
  replace j with (i+Z.of_nat (Z.to_nat (j-i))) in H by lia.
  apply enabled_seq_backwards' in H; lia.
Qed.  

Lemma enabled_seq_prev : forall i,
    0 <= i ->
    etable_values enabled_cell (i+1) = 1 ->
    etable_values enabled_cell i = 1.
Proof.
  intros i Hrange Henabled.
  destruct (enabled_bit i).
  - apply enabled_seq in H.
    congruence.
    lia.
  - auto.
Qed.

(* the maximum eid in an enabled row between i and i+n *)
Fixpoint max_eid' i n :=
  match n with
  | O => 0
  | S n => if (etable_values enabled_cell i =? 1)
           then Z.max (etable_values eid_cell i) (max_eid' (i+1) n)
           else 0
  end.

(* The maximum eid in an enabled row between 0 and etable_numRom. *)
Definition max_eid := max_eid' 0 (Z.to_nat (etable_numRow+1)).

Lemma max_eid'_correct : forall n i j,
    0 <= i ->
    i <= j < i+(Z.of_nat n) ->
    etable_values enabled_cell j = 1 ->
    etable_values eid_cell j <= max_eid' i n.
Proof.
  induction n.
  - simpl. lia.
  - intros i j Hrange Hbound Henabled.
    destruct (Z.eq_dec i j).
    + subst.
      simpl.
      rewrite Henabled, Z.eqb_refl. lia.
    + specialize (IHn (i+1) j ltac:(lia) ltac:(lia) Henabled).
      simpl.
      apply (enabled_seq_backwards i j) in Henabled; [|lia].
      rewrite Henabled, Z.eqb_refl.
      lia.
Qed.      

Lemma max_eid_correct : forall i,
    0 <= i <= etable_numRow ->
    etable_values enabled_cell i = 1 ->
    etable_values eid_cell i <= max_eid.
Proof.
  intros i Hrange Henabled.
  unfold max_eid.
  apply max_eid'_correct; lia.
Qed.

Lemma max_eid'_S: forall i n,
    0 <= i ->
    (n > 0)%nat ->
    etable_values enabled_cell (i+1) = 1 ->
    max_eid' i (S n) = max_eid' (i+1) n.
Proof.
  intros i n Hrange Hn Henabled.
  simpl.
  assert (Henabled' := enabled_seq_prev i Hrange Henabled).
  rewrite Henabled', Z.eqb_refl.
  pose (eid_common i).  
  destruct n.
  - lia.
  - simpl.
    rewrite Henabled, Z.eqb_refl.
    rewrite eid_change by auto.
    lia.
Qed.

Lemma max_eid'_cut : forall n m i,
    0 <= i ->
    (m > 0)%nat ->
    etable_values enabled_cell (i+Z.of_nat n) = 1 ->
    max_eid' i (n+m) = max_eid' (i+Z.of_nat n) m.
Proof.
  induction n; intros m i Hrange Hm Henable.
  - simpl. replace (i+0) with i  in * by lia. auto.
  - replace  (i + Z.of_nat (S n))  with  (i + 1 + Z.of_nat n) in * by lia.
    specialize (IHn m (i+1) ltac:(lia) Hm Henable).
    replace (S n + m)%nat with (S (n+m))%nat by lia.
    rewrite max_eid'_S; auto; try lia.
    apply enabled_seq_backwards with (i + 1 + Z.of_nat n); lia.
Qed.

Lemma max_eid'_tight : forall k i n,
    0 <= k ->
    k <= i < k + Z.of_nat n ->
    etable_values enabled_cell i = 1 ->
    etable_values enabled_cell (i+1) = 0 ->
    etable_values eid_cell i = max_eid' k n.
Proof.
  intros k i n Hrange Hbound Henabled Henabled'.
  replace n with ((Z.to_nat (i-k)) + (n - Z.to_nat (i-k)))%nat by lia.
  rewrite max_eid'_cut.
  - replace (k + Z.of_nat (Z.to_nat (i - k))) with i by lia.
    assert ( (n - Z.to_nat (i - k)) > 0)%nat by lia.
    remember  (n - Z.to_nat (i - k))%nat as m. clear Heqm.
    destruct m as [|m]; [lia|].
    simpl.
    rewrite Henabled, Z.eqb_refl.
    pose (eid_common i).
    destruct m.
    + simpl. lia.
    + simpl. rewrite Henabled'. simpl. lia.      
  - assumption.
  - lia.
  - replace (k + Z.of_nat (Z.to_nat (i - k))) with i by lia.
    assumption.
Qed.
    
Lemma max_eid_tight : forall i,
    0 <= i <= etable_numRow ->
    etable_values enabled_cell i = 1 ->
    etable_values enabled_cell (i+1) = 0 ->
    etable_values eid_cell i = max_eid.
Proof.
  intros i Hrange Henabled.
  unfold max_eid.
  apply max_eid'_tight; lia.  
Qed.

Definition mops_at_correct i :=
    MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack
  + MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap
  + MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Global
  = config_mops (opcode_config (class_of_row i) i).

Section mops_correct.
  Hypothesis all_opcode_mops_correct : forall c i,
      0 <= i ->
      etable_values enabled_cell i = 1 ->
      opcode_mops_correct c i.

  Lemma instruction_mops_bound : forall i,
    0 <= i ->
      MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack
    + MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap
    + MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Global
    >= instruction_mops i.
  Proof.
    intros i Hrange.
    unfold instruction_mops.
    destruct (enabled_bit i) as [Henabled|Henabled]; rewrite Henabled.
    - rewrite (proj2 (Z.eqb_neq 0 1)) by lia.
      pose (MTable.mops_at_nonnegative  (etable_values eid_cell i) MTableModel.LocationType_Stack).
      pose (MTable.mops_at_nonnegative  (etable_values eid_cell i) MTableModel.LocationType_Heap).
      pose (MTable.mops_at_nonnegative  (etable_values eid_cell i) MTableModel.LocationType_Global).
      lia.
    - rewrite Z.eqb_refl.
      specialize (all_opcode_mops_correct (class_of_row i) i).
      unfold opcode_mops_correct in all_opcode_mops_correct.
      rewrite (class_of_row_op  i (class_of_row i)) in all_opcode_mops_correct by auto.
      specialize (all_opcode_mops_correct Hrange Henabled eq_refl).
      lia.
  Qed.

  Lemma instruction_mops'_disabled : forall n i,
      0 <= i ->
      etable_values enabled_cell i = 0 ->
      instructions_mops' i n = 0.
  Proof.
    induction n; simpl; intros.
    - reflexivity.
    - unfold instruction_mops.
      rewrite H0.
      rewrite (proj2 (Z.eqb_neq 0 1)) by lia.
      rewrite IHn; try lia.
      rewrite enabled_seq; lia.
  Qed.      
      
  Lemma cum_mops_bound': forall n i,
    0 <= i ->
    i + Z.of_nat n = etable_numRow ->
    MTable.cum_mops (etable_values eid_cell i) (max_eid+1) >= instructions_mops' i n.
  Proof.
    induction n.
    - simpl.
      intros.
      pose (MTable.cum_mops_nonnegative (etable_values eid_cell i) (max_eid + 1)).
      lia.
    - intros i Hrange Hrange2.
      replace (i + Z.of_nat (S n)) with (i+1 + Z.of_nat n) in Hrange2 by lia.

      destruct (enabled_bit i) as [Henabled | Henabled].
      + rewrite instruction_mops'_disabled; auto.
        pose  (MTable.cum_mops_nonnegative (etable_values eid_cell i) (max_eid + 1)).
        lia.
      + specialize (IHn (i+1) ltac:(lia) ltac:(lia)). 
        rewrite MTable.cum_mops_cons.
        2: {
          pose (eid_common i).
          assert (Hmax_eid := max_eid_correct i ltac:(lia)).
          lia.
        }
        assert (Hmops_bound := instruction_mops_bound i).
        simpl.
        rewrite eid_change in IHn by lia.
        lia.
  Qed.

  Lemma cum_mops_equal' : forall n i,
    0 <= i ->
    i + Z.of_nat n = etable_numRow ->
    MTable.cum_mops (etable_values eid_cell i) (max_eid+1) <= instructions_mops' i n ->
    MTable.cum_mops (etable_values eid_cell i) (max_eid+1)  = instructions_mops' i n.
  Proof.
    induction n.
    - simpl.
      intros.
      pose (MTable.cum_mops_nonnegative (etable_values eid_cell i) (max_eid + 1)).
      lia.
    - intros i Hrange Hrange2 Hle.
      destruct (enabled_bit i) as [Henabled|Henabled].
      + rewrite (instruction_mops'_disabled (S n) i Hrange Henabled) in *.
        pose  (MTable.cum_mops_nonnegative (etable_values eid_cell i) (max_eid + 1)).
        lia.
      + replace (i + Z.of_nat (S n)) with (i+1 + Z.of_nat n) in Hrange2 by lia.
        specialize (IHn (i+1) ltac:(lia) ltac:(lia)).
        simpl in Hle.
        assert (Hblah:  0 <= etable_values eid_cell i < max_eid + 1).
        {
            pose (eid_common i).
            assert (Hmax_eid := max_eid_correct i ltac:(lia) Henabled).
            lia.
        }
        rewrite MTable.cum_mops_cons in Hle by (apply Hblah).
        assert (Hge := cum_mops_bound' (S n) i ltac:(lia) ltac:(lia)).
        rewrite MTable.cum_mops_cons in Hge by (apply Hblah).
        simpl in Hge.
        rewrite MTable.cum_mops_cons by (apply Hblah).
        simpl.
        lia.
  Qed.

  Lemma instructions_mops_cons : forall i,
      0 <= i < etable_numRow ->
      instructions_mops i = instruction_mops i + (instructions_mops (i+1)).
  Proof.
    intros i Hrange.
    unfold instructions_mops.
    replace ((Z.to_nat (etable_numRow - i))) with (S (Z.to_nat (etable_numRow - (i + 1)))) by lia.
    reflexivity.
  Qed.

  Lemma cum_mops_equal : forall n,
      0 <= Z.of_nat n < etable_numRow ->
      (forall m, (m < n)%nat -> etable_values enabled_cell (Z.of_nat m) = 1) -> 
    MTable.cum_mops (etable_values eid_cell (Z.of_nat n)) (max_eid+1) = instructions_mops (Z.of_nat n).
  Proof.
    induction n.
    - simpl. intros [Hrange1 Hrange2] Hprev_enabled.
      apply cum_mops_equal'.
      + auto.
      + lia.
      + change (instructions_mops' 0 (Z.to_nat (etable_numRow - 0)))
          with (instructions_mops 0).
        cut ( MTable.cum_mops (etable_values eid_cell (Z.of_nat 0)) (max_eid + 1) <=  etable_values rest_mops_cell 0).
        { simpl.
          assert (Hrest_mops_correct :=rest_mops_correct 0 ltac:(lia)). lia. }
        rewrite constraint_rest_mops.
        apply MTable.rest_mops_correct.
    - intros [Hrange1 Hrange2] Hprev_enabled.
      simpl in Hprev_enabled.
      destruct (enabled_bit (Z.of_nat (S n))) as [Hdisabled | _].
      + assert (Heid: etable_values eid_cell (Z.of_nat n) = max_eid). {
          apply max_eid_tight.
          lia.
          apply Hprev_enabled; lia.
          replace (Z.of_nat n + 1)  with (Z.of_nat (S n)); lia.
        }

        replace (etable_values eid_cell (Z.of_nat (S n))) 
        with  (etable_values eid_cell (Z.of_nat n) + 1) in *.
        2: {
          replace (Z.of_nat (S n)) with ((Z.of_nat n) + 1) by lia.
          rewrite eid_change; auto.
          lia.
        }
        rewrite Heid, MTable.cum_mops_empty_range.
        unfold instructions_mops. rewrite instruction_mops'_disabled; lia.
      + assert (Henabled' : forall m, (m < n)%nat -> etable_values enabled_cell (Z.of_nat m) = 1). {
          intros.
          apply Hprev_enabled.
          lia.
      }
      specialize (IHn ltac:(lia) Henabled').
      rewrite instructions_mops_cons in IHn by lia.
      rewrite MTable.cum_mops_cons in IHn.
      2: {
        specialize (Hprev_enabled n ltac:(lia)).
        assert (Hmax_eid_correct := max_eid_correct (Z.of_nat n) ltac:(lia) Hprev_enabled).
        pose (eid_common (Z.of_nat n)).
        lia.
      }        
      assert ( MTable.cum_mops (etable_values eid_cell (Z.of_nat (S n))) (max_eid+1)
               >= instructions_mops (Z.of_nat (S n))).
        {
          apply cum_mops_bound'.
          auto.
          lia.
        }
      replace (etable_values eid_cell (Z.of_nat (S n))) 
        with  (etable_values eid_cell (Z.of_nat n) + 1) in *.
      2: {
        replace (Z.of_nat (S n)) with ((Z.of_nat n) + 1) by lia.
        rewrite eid_change; auto.
        lia.
      }
      replace (Z.of_nat (S n))
        with  (Z.of_nat n + 1) in * by lia.
      pose (instruction_mops_bound (Z.of_nat n)).
      lia.
  Qed.

  Theorem mops_correct : forall i,
      0 <= i < etable_numRow ->
      i+1 < etable_numRow -> 
      etable_values enabled_cell i = 1 ->
      mops_at_correct i.
  Proof.
    intros i Hrange Hrange' Henabled.
    assert (Hinstruction_mops : instruction_mops i = config_mops (opcode_config (class_of_row i) i)).
    {
      unfold instruction_mops.
      rewrite Henabled.
      rewrite Z.eqb_refl.
      reflexivity.
    }
    assert (Hprev_enabled : forall m, (m < Z.to_nat i)%nat -> etable_values enabled_cell (Z.of_nat m) = 1). {
      apply  enabled_seq_mono.
      rewrite Z2Nat.id; lia.
    }
    assert (Heq := cum_mops_equal (Z.to_nat i) ltac:(lia) Hprev_enabled).
    rewrite (Z2Nat.id i ltac:(lia)) in Heq.
    rewrite instructions_mops_cons in Heq by lia.
    rewrite MTable.cum_mops_cons in Heq.
    2: {
            pose (eid_common i).
            assert (Hmax_eid := max_eid_correct i ltac:(lia) Henabled).
            lia.
    }
      
    rewrite <- (eid_change i ltac:(lia) Henabled) in Heq.
    assert (Hprev_enabled' : forall m, (m < Z.to_nat (i+1))%nat -> etable_values enabled_cell (Z.of_nat m) = 1). {
      intros m Hm.
      replace ( Z.to_nat (i + 1)) with (S (Z.to_nat i)) in Hm by lia.
      inversion Hm.
      - subst.
        rewrite Z2Nat.id; lia.
      - subst.
        apply enabled_seq_mono with (n:=Z.to_nat i).
        rewrite Z2Nat.id; lia.
        lia.
    }
    assert (Heq' := cum_mops_equal (Z.to_nat (i+1)) ltac:(lia) Hprev_enabled').
    rewrite (Z2Nat.id (i+1) ltac:(lia)) in Heq'.

    unfold mops_at_correct.
    lia.
  Qed.
End mops_correct.

Definition decode_call_jops (x : Z) : Z :=
  Z.land x ((Z.ones JTableModel.JOPS_SEPARATE)).

Definition decode_return_jops (x : Z) : Z :=
      Z.shiftr x JTableModel.JOPS_SEPARATE.

Definition opcode_jops_correct (c : OpcodeClass) i :=
    0 <= i ->
    etable_values enabled_cell i = 1 ->
    etable_values (ops_cell c) i = 1 ->
      JTable.jops_at (etable_values eid_cell i)
    >=  decode_call_jops (config_jops (opcode_config c i)).

Definition jops_at_correct i :=
    JTable.jops_at (etable_values eid_cell i)
  = decode_call_jops (config_jops (opcode_config (class_of_row i) i)).

Definition instruction_jops i :=
  if etable_values enabled_cell i =? 1
  then decode_call_jops (config_jops (opcode_config (class_of_row i) i))
  else 0.

Fixpoint instructions_jops' i n {struct n} :=
  match n with
  | O => 0
  | S n' =>
      instruction_jops i + instructions_jops' (i+1) n'
  end.

Lemma decode_call_jops_zero : decode_call_jops 0 = 0.
Proof.
  reflexivity.
Qed.

Lemma decode_return_jops_zero : decode_return_jops 0 = 0.
Proof.
  reflexivity.
Qed.

Definition encode_jops_no_mod  return_instructions call_instructions :=
   (Z.lor (Z.shiftl return_instructions JTableModel.JOPS_SEPARATE) call_instructions).

Lemma encode_jops_no_mod_spec : forall x y,
   0 <= x  <= common ->
   0 <= y  <= common ->
   JTableModel.encode_jops x y = encode_jops_no_mod x y.
Proof.
  intros.
  unfold JTableModel.encode_jops.

  rewrite Z.mod_small.
  2: {
    split.
    - rewrite Z.lor_nonneg.
      split; [|lia].
      rewrite Z.shiftl_nonneg.
      lia.
    - apply Z.lt_trans with ( 2 ^ (1 + 5 * CommonModel.COMMON_RANGE_OFFSET)).
      2: { apply  CommonModel.encode_frame_table_entry_order1. }
      refine (proj2 (IntegerFunctions.lor_bound_n _ _  _ _ _ _)).
      + unfold  CommonModel.COMMON_RANGE_OFFSET; lia.
      + rewrite Z.shiftl_mul_pow2.
      2: { unfold JTableModel.JOPS_SEPARATE. lia. }
      split; [unfold JTableModel.JOPS_SEPARATE; lia |].
      apply Z.le_lt_trans with  (common * 2 ^ (JTableModel.JOPS_SEPARATE)).
      * unfold JTableModel.JOPS_SEPARATE. lia.
      rewrite JTableModel.common_is_COMMON_RANGE_OFFSET.
      unfold CommonModel.COMMON_RANGE_OFFSET, JTableModel.JOPS_SEPARATE.
      lia.
      * rewrite JTableModel.common_is_COMMON_RANGE_OFFSET in *.
        unfold CommonModel.COMMON_RANGE_OFFSET in *.
        lia.
  }
  reflexivity.      
Qed.


Lemma decode_encode_call_jops : forall x y,
    0 <= x <= common ->
    0 <= y <= common ->
    decode_call_jops (JTableModel.encode_jops x y) = y.
Proof.
  unfold decode_call_jops.
  intros x y Hrangex Hrangey.

  rewrite encode_jops_no_mod_spec by lia.
  unfold encode_jops_no_mod.

  rewrite Z.land_lor_distr_l.

  replace (Z.land (Z.shiftl x JTableModel.JOPS_SEPARATE) (Z.ones JTableModel.JOPS_SEPARATE)) with 0.
  2: {
    rewrite IntegerFunctions.land_ones_high.
    reflexivity.
    unfold JTableModel.JOPS_SEPARATE; lia.
  }  
  rewrite Z.lor_0_l.
  rewrite Z.land_ones_low; try lia.

  destruct (Z.eq_dec y 0).
  - subst.
    simpl.
    unfold JTableModel.JOPS_SEPARATE; lia.
  - rewrite <- Z.log2_lt_pow2 by lia.
    rewrite JTableModel.common_is_COMMON_RANGE_OFFSET in *.
    unfold CommonModel.COMMON_RANGE_OFFSET,  JTableModel.JOPS_SEPARATE in *.
    lia.
Qed.

Lemma decode_encode_return_jops : forall x y,
    0 <= x <= common ->
    0 <= y <= common ->
    decode_return_jops (JTableModel.encode_jops x y) = x.
Proof.
  unfold decode_return_jops.
  intros x y Hrangex Hrangey.

  rewrite encode_jops_no_mod_spec by lia.
  unfold encode_jops_no_mod.

  rewrite Z.shiftr_lor.

  replace (Z.shiftr y JTableModel.JOPS_SEPARATE) with 0.
  2: {
    rewrite Z.shiftr_eq_0; [lia | lia |].
    destruct (Z.eq_dec y 0).
    - subst; cbv; auto.
    - rewrite <- Z.log2_lt_pow2 by lia.
      rewrite JTableModel.common_is_COMMON_RANGE_OFFSET in *.
      unfold CommonModel.COMMON_RANGE_OFFSET,  JTableModel.JOPS_SEPARATE in *.
      lia.
  }

  rewrite Z.lor_0_r.  
  rewrite Z.shiftr_shiftl_l.
  2: { unfold JTableModel.JOPS_SEPARATE; lia. }
  replace (JTableModel.JOPS_SEPARATE - JTableModel.JOPS_SEPARATE) with 0; reflexivity.
Qed.
                                                              
(* The sum of all the intended jops of the instructions in rows `i`-`etable_numRow`.   *)
Definition instructions_jops (i : Z) : Z :=
  instructions_jops' i (Z.to_nat (etable_numRow - i)).


Lemma return_jops_bound : forall c i,
    0 <= decode_return_jops (config_jops (opcode_config c i)) <= 1.
Proof.
  intros c i.
  destruct c; simpl;
    try rewrite decode_return_jops_zero; 
    try rewrite decode_encode_return_jops by (pose CommonModel.one_lt_common; lia);
    lia.
Qed.

Lemma call_jops_bound : forall c i,
    0 <= decode_call_jops (config_jops (opcode_config c i)) <= 1.
Proof.
  intros c i.
  destruct c; simpl;
    try rewrite decode_call_jops_zero; 
    try rewrite decode_encode_call_jops by (pose CommonModel.one_lt_common; lia);
    lia.
Qed.

Lemma encode_decode_encode_jops : forall c i,
  config_jops (opcode_config c i) =
  JTableModel.encode_jops
    (decode_return_jops (config_jops (opcode_config c i)))
    (decode_call_jops (config_jops (opcode_config c i))).
Proof.
  intros c i.
  destruct c; simpl; try reflexivity.
  + pose CommonModel.one_lt_common.
    rewrite encode_jops_no_mod_spec by lia.
    change  (decode_return_jops (encode_jops_no_mod 0 1)) with 0.
    change  (decode_call_jops (encode_jops_no_mod 0 1)) with 1.
    rewrite encode_jops_no_mod_spec by lia.
    reflexivity.
  + pose CommonModel.one_lt_common.
    rewrite encode_jops_no_mod_spec by lia.
    change  (decode_return_jops (encode_jops_no_mod 1 0)) with 1.
    change  (decode_call_jops (encode_jops_no_mod 1 0)) with 0.
    rewrite encode_jops_no_mod_spec by lia.
    reflexivity.
  + pose CommonModel.one_lt_common.
    rewrite encode_jops_no_mod_spec by lia.
    change  (decode_return_jops (encode_jops_no_mod 0 1)) with 0.
    change  (decode_call_jops (encode_jops_no_mod 0 1)) with 1.
    rewrite encode_jops_no_mod_spec by lia.
    reflexivity.
Qed.

Lemma shift_plus : forall n a b ,
    0 <= n ->
    Z.shiftl a n + Z.shiftl b n = Z.shiftl (a+b) n.
Proof.
  intros.
  rewrite !Z.shiftl_mul_pow2 by lia.
  lia.
Qed.  

Lemma encode_jops_add : forall x y dx dy,
    0 <= x ->
    x + 1 <= common ->
    0 <= y ->
    y + 1 <= common ->
    0 <= dx <= 1 ->
    0 <= dy <= 1 ->
   JTableModel.encode_jops x y + JTableModel.encode_jops dx dy
   = JTableModel.encode_jops (x + dx) (y + dy).
Proof.
  intros x y dx dy Hx Hx1 Hy Hy1 Hdx Hdy.
  pose CommonModel.one_lt_common.
  assert (common < 2 ^ JTableModel.JOPS_SEPARATE).
  {
    rewrite JTableModel.common_is_COMMON_RANGE_OFFSET.
    unfold CommonModel.COMMON_RANGE_OFFSET, JTableModel.JOPS_SEPARATE.
    lia.
  }
  rewrite !encode_jops_no_mod_spec by lia.

  assert (0 <= JTableModel.JOPS_SEPARATE) by (unfold JTableModel.JOPS_SEPARATE; lia).
  
  unfold  encode_jops_no_mod.
  rewrite Z.lor_comm.
  rewrite <- IntegerFunctions.plus_lor_n by lia.
  rewrite Z.lor_comm.
  rewrite <- IntegerFunctions.plus_lor_n by lia.
  replace  (y + Z.shiftl x JTableModel.JOPS_SEPARATE + (dy + Z.shiftl dx JTableModel.JOPS_SEPARATE))
    with ((y+dy)+(Z.shiftl x JTableModel.JOPS_SEPARATE + Z.shiftl dx JTableModel.JOPS_SEPARATE))
    by lia.
  rewrite shift_plus  by (unfold JTableModel.JOPS_SEPARATE; lia).
  rewrite IntegerFunctions.plus_lor_n by lia.
  rewrite Z.lor_comm.
  reflexivity.
Qed.

Lemma rest_jops_correct' : forall n i,
    0 <= i ->
    i + Z.of_nat n = etable_numRow ->
    exists x y,
         0 <= x <= Z.of_nat n
      /\ 0 <= y <= Z.of_nat n
      /\ y <= instructions_jops' i n
      /\ etable_values rest_jops_cell i = JTableModel.encode_jops x y.
Proof.
  induction n.
  - simpl.
    intros.
    replace i with etable_numRow by lia.
    rewrite rest_jops_terminates.
    exists 0. exists 0.
    change ( JTableModel.encode_jops 0 0) with 0.
    repeat split; try lia.
  - intros i Hrange H.
    replace (i + Z.of_nat (S n)) with (i+1 + Z.of_nat n) in * by lia.
    simpl.
    specialize (IHn (i+1) ltac:(lia) H).
    unfold instruction_jops.
    destruct (enabled_bit i) as [Henabled|Henabled]; rewrite Henabled.
    + rewrite (proj2 (Z.eqb_neq 0 1)) by lia.
      rewrite rest_jops_change_disabled; auto.
      replace ( 0 + instructions_jops' (i + 1) n ) with ( 0 + instructions_jops' (i + 1) n) by lia.
      destruct IHn as [x [y [Hx [Hy [Hinstr Hval]]]]].
      exists x. exists y.
      repeat split; lia.
    + rewrite Z.eqb_refl.
      destruct (class_of_row_op i (class_of_row i) Henabled) as [_ Hclass].      
      rewrite (rest_jops_change_enabled i (class_of_row i) Hrange Henabled (Hclass eq_refl)).

      destruct IHn as [x [y [Hx [Hy [Hinstr Hval]]]]].
      exists (x + decode_return_jops (config_jops (opcode_config (class_of_row i) i))).
      exists (y + decode_call_jops (config_jops (opcode_config (class_of_row i) i))).
      assert (Hreturn_jops_bound := return_jops_bound (class_of_row i) i).
      assert (Hcall_jops_bound := call_jops_bound (class_of_row i) i).
      split; [lia|].
      split; [lia|].
      split; [lia|].
      rewrite Hval.
      pattern  (config_jops (opcode_config (class_of_row i) i)) at 1.
      rewrite encode_decode_encode_jops.
      pose etable_numRow_le_common.
      rewrite encode_jops_add; lia.
Qed.

Lemma rest_jops_correct : forall i,
    0 <= i <= etable_numRow ->
    decode_call_jops (etable_values rest_jops_cell i) <= instructions_jops i.
Proof.
  pose etable_numRow_le_common.
  unfold instructions_jops. intros.
  destruct (rest_jops_correct' (Z.to_nat (etable_numRow - i)) i)
         as [x [y [Hx [Hy [H1 H2]]]]]
  ; try lia.
  rewrite H2.
  rewrite decode_encode_call_jops by lia.
  lia.
Qed. 

Section jops_correct.
  Hypothesis all_opcode_jops_correct : forall c i, opcode_jops_correct c i.

  Lemma instruction_jops_bound : forall i,
      0 <= i ->
      JTable.jops_at (etable_values eid_cell i)
    >= instruction_jops i.
  Proof.
    intros.
    unfold instruction_jops.
    destruct (enabled_bit i) as [Henabled|Henabled]; rewrite Henabled.
    - rewrite (proj2 (Z.eqb_neq 0 1)) by lia.
      pose (JTable.jops_at_nonnegative  (etable_values eid_cell i)).
      lia.
    - rewrite Z.eqb_refl.
      specialize (all_opcode_jops_correct (class_of_row i) i).
      unfold opcode_jops_correct in all_opcode_jops_correct.
      rewrite (class_of_row_op  i (class_of_row i)) in all_opcode_jops_correct by auto.
      specialize (all_opcode_jops_correct ltac:(lia) Henabled eq_refl).
      lia.
  Qed.

  Lemma instruction_jops'_disabled : forall n i,
      0 <= i ->
      etable_values enabled_cell i = 0 ->
      instructions_jops' i n = 0.
  Proof.
    induction n; simpl; intros.
    - reflexivity.
    - unfold instruction_jops.
      rewrite H0.
      rewrite (proj2 (Z.eqb_neq 0 1)) by lia.
      rewrite IHn; try lia.
      rewrite enabled_seq; lia.
  Qed.
      
  Lemma cum_jops_bound': forall n i,
    0 <= i ->
    i + Z.of_nat n = etable_numRow ->
    JTable.cum_jops (etable_values eid_cell i) (max_eid+1) >= instructions_jops' i n.
  Proof.
    induction n.
    - simpl.
      intros.
      pose (JTable.cum_jops_nonnegative (etable_values eid_cell i) (max_eid + 1)).
      lia.
    - intros i Hrange Hrange2.
      replace (i + Z.of_nat (S n)) with (i+1 + Z.of_nat n) in Hrange2 by lia.

      destruct (enabled_bit i) as [Henabled | Henabled].
      + rewrite instruction_jops'_disabled; auto.
        pose  (JTable.cum_jops_nonnegative (etable_values eid_cell i) (max_eid + 1)).
        lia.
      + specialize (IHn (i+1) ltac:(lia) ltac:(lia)).
        rewrite JTable.cum_jops_cons.
        2: {
          pose (eid_common i).
          assert (Hmax_eid := max_eid_correct i ltac:(lia)).
          lia.
        }
        assert (Hjops_bound := instruction_jops_bound i).
        simpl.
        rewrite eid_change in IHn by lia.
        lia.
  Qed.

  Lemma cum_jops_equal' : forall n i,
    0 <= i ->
    i + Z.of_nat n = etable_numRow ->
    JTable.cum_jops (etable_values eid_cell i) (max_eid+1) <= instructions_jops' i n ->
    JTable.cum_jops (etable_values eid_cell i) (max_eid+1)  = instructions_jops' i n.
  Proof.
    induction n.
    - simpl.
      intros.
      pose (JTable.cum_jops_nonnegative (etable_values eid_cell i) (max_eid + 1)).
      lia.
    - intros i Hrange Hrange2 Hle.
      destruct (enabled_bit i) as [Henabled|Henabled].
      + rewrite (instruction_jops'_disabled (S n) i Hrange Henabled) in *.
        pose  (JTable.cum_jops_nonnegative (etable_values eid_cell i) (max_eid + 1)).
        lia.
      + replace (i + Z.of_nat (S n)) with (i+1 + Z.of_nat n) in Hrange2 by lia.
        specialize (IHn (i+1) ltac:(lia) ltac:(lia)).
        simpl in Hle.
        assert (Hblah:  0 <= etable_values eid_cell i < max_eid + 1).
        {
            pose (eid_common i).
            assert (Hmax_eid := max_eid_correct i ltac:(lia) Henabled).
            lia.
        }
        rewrite JTable.cum_jops_cons in Hle by (apply Hblah).
        assert (Hge := cum_jops_bound' (S n) i ltac:(lia) ltac:(lia)).
        rewrite JTable.cum_jops_cons in Hge by (apply Hblah).
        simpl in Hge.
        rewrite JTable.cum_jops_cons by (apply Hblah).
        simpl.
        lia.
  Qed.

  Lemma instructions_jops_cons : forall i,
      0 <= i < etable_numRow ->
      instructions_jops i = instruction_jops i + (instructions_jops (i+1)).
  Proof.
    intros i Hrange.
    unfold instructions_jops.
    replace ((Z.to_nat (etable_numRow - i))) with (S (Z.to_nat (etable_numRow - (i + 1)))) by lia.
    reflexivity.
  Qed.

  Lemma cum_jops_equal : forall n,
      0 <= Z.of_nat n < etable_numRow ->
      (forall m, (m < n)%nat -> etable_values enabled_cell (Z.of_nat m) = 1) -> 
    JTable.cum_jops (etable_values eid_cell (Z.of_nat n)) (max_eid+1) = instructions_jops (Z.of_nat n).
  Proof.
    induction n.
    - simpl. intros [Hrange1 Hrange2] Hprev_enabled.
      apply cum_jops_equal'.
      + auto.
      + lia.
      + change (instructions_jops' 0 (Z.to_nat (etable_numRow - 0)))
          with (instructions_jops 0).
        cut (JTable.cum_jops (etable_values eid_cell (Z.of_nat 0)) (max_eid + 1) <=  decode_call_jops (etable_values rest_jops_cell 0)).
        { simpl.
          assert (Hrest_jops_correct := rest_jops_correct 0 ltac:(lia)). lia. }
        rewrite constraint_rest_jops.
        apply JTable.rest_jops_correct.
    - intros [Hrange1 Hrange2] Hprev_enabled.
      simpl in Hprev_enabled.
      destruct (enabled_bit (Z.of_nat (S n))) as [Hdisabled | _].
      + assert (Heid: etable_values eid_cell (Z.of_nat n) = max_eid). {
          apply max_eid_tight.
          lia.
          apply Hprev_enabled; lia.
          replace (Z.of_nat n + 1)  with (Z.of_nat (S n)); lia.
        }

        replace (etable_values eid_cell (Z.of_nat (S n))) 
        with  (etable_values eid_cell (Z.of_nat n) + 1) in *.
        2: {
          replace (Z.of_nat (S n)) with ((Z.of_nat n) + 1) by lia.
          rewrite eid_change; auto.
          lia.
        }
        rewrite Heid, JTable.cum_jops_empty_range.
        unfold instructions_jops. rewrite instruction_jops'_disabled; lia.
      + assert (Henabled' : forall m, (m < n)%nat -> etable_values enabled_cell (Z.of_nat m) = 1). {
          intros.
          apply Hprev_enabled.
          lia.
      }
      specialize (IHn ltac:(lia) Henabled').
      rewrite instructions_jops_cons in IHn by lia.
      rewrite JTable.cum_jops_cons in IHn.
      2: {
        specialize (Hprev_enabled n ltac:(lia)).
        assert (Hmax_eid_correct := max_eid_correct (Z.of_nat n) ltac:(lia) Hprev_enabled).
        pose (eid_common (Z.of_nat n)).
        lia.
      }
      assert (JTable.cum_jops (etable_values eid_cell (Z.of_nat (S n))) (max_eid+1)
               >= instructions_jops (Z.of_nat (S n))).
        {
          apply cum_jops_bound'.
          auto.
          lia.
        }
      replace (etable_values eid_cell (Z.of_nat (S n))) 
        with  (etable_values eid_cell (Z.of_nat n) + 1) in *.
      2: {
        replace (Z.of_nat (S n)) with ((Z.of_nat n) + 1) by lia.
        rewrite eid_change; auto.
        lia.
      }
      replace (Z.of_nat (S n))
        with  (Z.of_nat n + 1) in * by lia.
      pose (instruction_jops_bound (Z.of_nat n)).
      lia.
  Qed.

  Theorem jops_correct : forall i,
      0 <= i < etable_numRow ->
      i+1 < etable_numRow -> 
      etable_values enabled_cell i = 1 ->
      jops_at_correct i.
  Proof.
    intros i Hrange Hrange' Henabled.
    assert (Hinstruction_jops : instruction_jops i = decode_call_jops (config_jops (opcode_config (class_of_row i) i))).
    {
      unfold instruction_jops.
      rewrite Henabled.
      rewrite Z.eqb_refl.
      reflexivity.
    }
    assert (Hprev_enabled : forall m, (m < Z.to_nat i)%nat -> etable_values enabled_cell (Z.of_nat m) = 1). {
      apply  enabled_seq_mono.
      rewrite Z2Nat.id; lia.
    }
    assert (Heq := cum_jops_equal (Z.to_nat i) ltac:(lia) Hprev_enabled).
    rewrite (Z2Nat.id i ltac:(lia)) in Heq.
    rewrite instructions_jops_cons in Heq by lia.
    rewrite JTable.cum_jops_cons in Heq.
    2: {
            pose (eid_common i).
            assert (Hmax_eid := max_eid_correct i ltac:(lia) Henabled).
            lia.
    }
      
    rewrite <- (eid_change i ltac:(lia) Henabled) in Heq.
    assert (Hprev_enabled' : forall m, (m < Z.to_nat (i+1))%nat -> etable_values enabled_cell (Z.of_nat m) = 1). {
      intros m Hm.
      replace ( Z.to_nat (i + 1)) with (S (Z.to_nat i)) in Hm by lia.
      inversion Hm.
      - subst.
        rewrite Z2Nat.id; lia.
      - subst.
        apply enabled_seq_mono with (n:=Z.to_nat i).
        rewrite Z2Nat.id; lia.
        lia.
    }
    assert (Heq' := cum_jops_equal (Z.to_nat (i+1)) ltac:(lia) Hprev_enabled').
    rewrite (Z2Nat.id (i+1) ltac:(lia)) in Heq'.

    unfold jops_at_correct.
    lia.
  Qed.
End jops_correct.

Lemma eid_value' : forall n,
 etable_values enabled_cell (Z.of_nat n) = 1 ->
 etable_values eid_cell (Z.of_nat n) = 1+(Z.of_nat n).
Proof.
  induction n.
  - intros.
    simpl.
    rewrite initial_eid. lia.
  - intros Henabled.
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
    assert (Henabled' := (enabled_seq_prev (Z.of_nat n) ltac:(lia) Henabled)).
    rewrite (eid_change (Z.of_nat n) ltac:(lia) Henabled').
    specialize (IHn Henabled').
    lia.
Qed.

Lemma eid_value : forall i,
 0 <= i ->
 etable_values enabled_cell i = 1 ->
 etable_values eid_cell i = 1+i.
Proof.
  intros.
  replace i with (Z.of_nat (Z.to_nat i)) in * by lia.
  rewrite eid_value' by auto.
  lia.
Qed.


Import JTableModel.

Definition opcode_encoding_bounded (c: OpcodeClass) i :=
  0 <= i ->
  0 <= config_opcode (opcode_config c i) < 2^ImageTableModel.OPCODE_SHIFT.

Require OpCallModel.
Require OpCallIndirectModel.
Require CallReturnHelper.

Section jops_at_bounded.

  
Lemma Zlt_succ_lt_or_eq : forall n m,  n < m + 1 -> n < m \/ n = m.
Proof.
  lia.
Qed.

Lemma next_iid_common : forall i,
    0 <= i ->
    etable_values enabled_cell i = 1 ->
    (class_of_row i = Call \/ class_of_row i = CallIndirect) ->
    0 <= etable_values iid_cell i + 1 < common.    
Proof.
  intros i Hrange Henabled Hclass.
  assert (Hlookup : ImageTableModel.in_itable  (etable_values itable_lookup_cell i)).
  {
    unfold in_itable.
    apply itable_lookup_in_itable; auto.
  }
  destruct Hclass.
  - rewrite itable_lookup_encode with (idx:=Call) in Hlookup; try lia; auto.
    2: {
      rewrite class_of_row_op; auto.
    }
    refine (call_iid_small _ _ _ _ _ _ Hlookup _).
    pose (fid_common i); lia.
    pose (iid_common i); lia.
    left; reflexivity.
  - rewrite itable_lookup_encode with (idx:=CallIndirect) in Hlookup; try lia; auto.
    2: {
      rewrite class_of_row_op; auto.
    }
    refine (call_iid_small _ _ _ _ _ _ Hlookup _).
    pose (fid_common i); lia.
    pose (iid_common i); lia.
    right; reflexivity.
Qed.

Lemma all_opcodes_jops_correct: forall (c : OpcodeClass) (i : Z), opcode_jops_correct c i.
  unfold opcode_jops_correct.
  intros c i Hrange Henabled Hclass.
  assert (Hjops_nonnegative := JTable.jops_at_nonnegative  (etable_values eid_cell i)).
  destruct c eqn:c_eq; simpl;
    try rewrite decode_call_jops_zero;
    try rewrite decode_encode_call_jops by (pose CommonModel.one_lt_common; lia);
    try lia.
  - assert (Hin := CallReturnHelper.Call_jtable_entry i Hrange Henabled Hclass).
    eapply JTable.jtable_call_ops.
    6: { apply Hin. }
    + split.
      rewrite eid_value; lia.
      pose (eid_common i); lia.
    + pose (frame_id_common i); lia.
    + pose (OpCallModel.index_common i); lia.
    + pose (fid_common i); lia.
    + apply  next_iid_common; eauto.
      rewrite <- (class_of_row_op i Call); auto.
  - assert (Hin := CallReturnHelper.CallIndirect_jtable_entry i Hrange Henabled Hclass).
    eapply JTable.jtable_call_ops.
    6: { apply Hin. }
    + split.
      rewrite eid_value; lia.
      pose (eid_common i); lia.
    + pose (frame_id_common i); lia.
    + pose (OpCallIndirectModel.func_index_common i); lia.
    + pose (fid_common i); lia.
    + apply  next_iid_common; eauto.
      rewrite <- (class_of_row_op i CallIndirect); auto.
Qed.

Lemma jops_at_case : forall i,
      0 <= i < etable_numRow ->
      i+1 < etable_numRow -> 
      etable_values enabled_cell i = 1 ->
      (JTable.jops_at (etable_values eid_cell i) = 0 /\ config_next_frame_id (opcode_config (class_of_row i) i)  = None
       \/ (JTable.jops_at (etable_values eid_cell i) = 1 /\ class_of_row i = Call)
       \/ (JTable.jops_at (etable_values eid_cell i) = 1 /\ class_of_row i = CallIndirect)
       \/ (JTable.jops_at (etable_values eid_cell i) = 0 /\ class_of_row i = Return)).
Proof.
  intros i Hrange Hmore_range Henabled.
  assert (Hjops_correct := jops_correct all_opcodes_jops_correct i Hrange Hmore_range Henabled).
  unfold jops_at_correct in Hjops_correct.
  destruct (class_of_row i); simpl in *;
    try rewrite decode_call_jops_zero in Hjops_correct; eauto.

  - rewrite decode_encode_call_jops in Hjops_correct by (pose CommonModel.one_lt_common; lia).
    right; left; eauto.

  - rewrite decode_encode_call_jops in Hjops_correct by (pose CommonModel.one_lt_common; lia).
    right; right; right; eauto.

  - rewrite decode_encode_call_jops in Hjops_correct by (pose CommonModel.one_lt_common; lia).
    right; right; left; eauto.
Qed.    
  
Theorem jtable_wellformedness : forall n,
    (Z.of_nat n) + 1 < etable_numRow ->
    etable_values enabled_cell (Z.of_nat n) = 1 ->    
    (0 <= (etable_values frame_id_cell (Z.of_nat n))
     /\ etable_values frame_id_cell (Z.of_nat n) <= etable_values eid_cell (Z.of_nat n))
     /\ (forall frame_id last_frame_id callee_fid fid iid,
            0 <= frame_id < etable_values eid_cell (Z.of_nat n) ->
            JTableModel.in_jtable (encode_frame_table_entry frame_id last_frame_id callee_fid fid iid) ->
            0 <= last_frame_id < common ->
            0 <= callee_fid < common ->
            0 <= fid < common ->
            0 <= iid < common ->
          0 <= last_frame_id /\ last_frame_id <= frame_id).
Proof.
  induction n.
  - intros Hnumrow Henabled.
    split.
    + simpl. rewrite initial_frame_id, initial_eid. lia.
    + intros.
      simpl in *.
      rewrite initial_eid in *.
      apply JTable.id_zero_entries in H0; lia.
  - intros Hnumrow Henabled.
    replace ((Z.of_nat (S n))) with ((Z.of_nat n)+1) in * by lia.
    assert (Henabled_prev := enabled_seq_prev (Z.of_nat n) ltac:(lia) Henabled).
    specialize (IHn ltac:(lia) Henabled_prev).
    destruct IHn as [IH1 IH2].
    destruct (jops_at_case (Z.of_nat n) ltac:(lia) ltac:(lia) Henabled_prev)
      as [[Hjops Hframe_id_change]
         | [[Hjops Hclass_call]
           | [[Hjops Hclass_callindirect] | [Hjops Hclass_return]]]].
  - split.
    + rewrite eid_change; try lia; auto.
      rewrite (frame_id_change (Z.of_nat n) (class_of_row (Z.of_nat n))); try lia.
      rewrite Hframe_id_change; lia.
      rewrite class_of_row_op; auto.
    + intros  frame_id last_frame_id callee_fid fid iid.
      rewrite eid_change; try lia; auto.
      intros Hframe_id_le_eid Hin Hlast_frame_id_common Hcallee_fid_common Hfid_common Hiid_common.
      destruct Hframe_id_le_eid as [Hframe_id_nonnegative Hframe_id_le_eid].
      apply Zlt_succ_lt_or_eq in Hframe_id_le_eid.
      destruct Hframe_id_le_eid as [Hframe_id_le | Hframe_id_eq].
      destruct (Z.eq_dec frame_id 0) as [Hzero | Hnonzero].
      * apply JTable.id_zero_entries in Hin;
        lia.
      * apply (IH2 frame_id last_frame_id callee_fid fid iid); try lia.
        apply Hin.
      * destruct (Z.eq_dec frame_id 0) as [Hzero | Hnonzero].
        { apply JTable.id_zero_entries in Hin;
            lia. }
        { destruct (JTable.jtable_no_ops frame_id last_frame_id callee_fid fid iid); try lia.
          ** pose (eid_common (Z.of_nat n)); lia.
          ** apply Hin.
          ** rewrite Hframe_id_eq.
             apply Hjops. }
  - split.
    + rewrite eid_change; try lia; auto.
      rewrite (frame_id_change (Z.of_nat n) Call); try lia; auto.
      simpl.
      lia.
      rewrite class_of_row_op; auto.
    + intros  frame_id last_frame_id callee_fid fid iid.
      rewrite eid_change; try lia; auto.
      intros Hframe_id_le_eid Hin Hlast_frame_id_common Hcallee_fid_common Hfid_common Hiid_common.
      destruct Hframe_id_le_eid as [Hframe_id_nonnegative Hframe_id_le_eid].
      apply Zlt_succ_lt_or_eq in Hframe_id_le_eid.
      destruct Hframe_id_le_eid as [Hframe_id_le | Hframe_id_eq].
      * apply (IH2 frame_id last_frame_id callee_fid fid iid); try lia.
        apply Hin.
      * assert (Hclass_call' : etable_values (ops_cell Call) (Z.of_nat n) = 1)
          by (apply class_of_row_op; auto).
        assert (Hin2 := CallReturnHelper.Call_jtable_entry (Z.of_nat n) ltac:(lia) Henabled_prev Hclass_call').
        assert (Hjops' :  JTable.jops_at (etable_values eid_cell (Z.of_nat n)) <= 1) by lia.
        rewrite <- Hframe_id_eq in Hjops', Hin2.
        pose (frame_id_common (Z.of_nat n)).
        pose (OpCallModel.index_common (Z.of_nat n)).
        pose (fid_common (Z.of_nat n)).
        pose (iid_common (Z.of_nat n + 1)).
        destruct (JTable.in_jtable_unique Hjops' Hin Hin2) as [? [? [? ?]]]; try lia.
        { rewrite Hframe_id_eq.
          split.
          rewrite eid_value; lia.
          pose (eid_common (Z.of_nat n)); lia.
        }
        { apply  next_iid_common; eauto; lia. }          
  - split.
    + rewrite eid_change; try lia; auto.
      rewrite (frame_id_change (Z.of_nat n) CallIndirect); try lia; auto.
      simpl.
      lia.
      rewrite class_of_row_op; auto.
    + intros  frame_id last_frame_id callee_fid fid iid.
      rewrite eid_change; try lia; auto.
      intros Hframe_id_le_eid Hin Hlast_frame_id_common Hcallee_fid_common Hfid_common Hiid_common.
      destruct Hframe_id_le_eid as [Hframe_id_nonnegative Hframe_id_le_eid].
      apply Zlt_succ_lt_or_eq in Hframe_id_le_eid.
      destruct Hframe_id_le_eid as [Hframe_id_le | Hframe_id_eq].
      * apply (IH2 frame_id last_frame_id callee_fid fid iid); try lia.
        apply Hin.
      * assert (Hclass_call' : etable_values (ops_cell CallIndirect) (Z.of_nat n) = 1)
          by (apply class_of_row_op; auto).
        assert (Hin2 := CallReturnHelper.CallIndirect_jtable_entry (Z.of_nat n) ltac:(lia) Henabled_prev Hclass_call').
        assert (Hjops' :  JTable.jops_at (etable_values eid_cell (Z.of_nat n)) <= 1) by lia.
        rewrite <- Hframe_id_eq in Hjops', Hin2.

        pose (frame_id_common (Z.of_nat n)).
        pose (OpCallIndirectModel.func_index_common (Z.of_nat n)).
        pose (fid_common (Z.of_nat n)).
        pose (iid_common (Z.of_nat n + 1)).
        destruct (JTable.in_jtable_unique Hjops' Hin Hin2) as [? [? [? ?]]]; try lia.
        { rewrite Hframe_id_eq.
          split.
          rewrite eid_value; lia.
          pose (eid_common (Z.of_nat n)); lia.
        }
        { apply  next_iid_common; eauto; lia. }          
  - assert (Hclass_return' : etable_values (ops_cell Return) (Z.of_nat n) = 1)
          by (apply class_of_row_op; auto).
        assert (Hin2 := CallReturnHelper.Return_jtable_entry (Z.of_nat n) ltac:(lia) Henabled_prev Hclass_return').
    split.
    + rewrite eid_change; try lia; auto.
      destruct (Zle_lt_or_eq _ _ (proj2 IH1)) as [Hframe_id_lt | Hframe_id_eq].      
      *
        assert (Hframe_id_bound:  0 <= etable_values frame_id_cell (Z.of_nat n) < etable_values eid_cell (Z.of_nat n)) by lia.
        specialize (IH2 _ _ _ _ _  Hframe_id_bound Hin2).
        pose (frame_id_common (Z.of_nat n + 1)).
        pose (fid_common (Z.of_nat n)).
        pose (fid_common (Z.of_nat n + 1)).
        pose (iid_common (Z.of_nat n + 1)).
        specialize (IH2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        destruct IH1.
        split; lia. 
      * destruct (Z.eq_dec (etable_values frame_id_cell (Z.of_nat n)) 0).
        {
          pose (frame_id_common (Z.of_nat n + 1)).
          pose (fid_common (Z.of_nat n)).
          pose (fid_common (Z.of_nat n + 1)).
          pose (iid_common (Z.of_nat n + 1)).
          apply JTable.id_zero_entries in Hin2;
            try lia.
        }
        {
        pose (frame_id_common (Z.of_nat n)).
        pose (frame_id_common (Z.of_nat n + 1)).
        pose (fid_common (Z.of_nat n)).
        pose (fid_common (Z.of_nat n + 1)).
        pose (iid_common (Z.of_nat n + 1)).
        destruct (JTable.jtable_no_ops  (etable_values frame_id_cell (Z.of_nat n))
                    (etable_values frame_id_cell (Z.of_nat n + 1))
                    (etable_values fid_cell (Z.of_nat n))
                    (etable_values fid_cell (Z.of_nat n + 1))
                    (etable_values iid_cell (Z.of_nat n + 1))); try lia.
        apply Hin2.
          ** rewrite Hframe_id_eq.
             apply Hjops. }
    + intros  frame_id last_frame_id callee_fid fid iid.
      rewrite eid_change; try lia; auto.
      intros Hframe_id_le_eid Hin  Hlast_frame_id_common Hcallee_fid_common Hfid_common Hiid_common.
      destruct (Zlt_succ_lt_or_eq _ _ (proj2 Hframe_id_le_eid))
        as  [Hframe_id_le | Hframe_id_eq].
      
      * apply (IH2 frame_id last_frame_id callee_fid fid iid); try lia.
        apply Hin.        
      * rewrite Hframe_id_eq in Hin.


        
        destruct (JTable.jtable_no_ops  (etable_values eid_cell (Z.of_nat n)) last_frame_id callee_fid
             fid iid); try lia.
        ** split.           
           rewrite eid_value; lia.
           pose (eid_common (Z.of_nat n)); lia.
        ** apply Hin.
Qed.

Corollary jops_at_bounded : forall i,
      0 <= i < etable_numRow ->
      i+1 < etable_numRow -> 
      etable_values enabled_cell i = 1 ->
      etable_values frame_id_cell i > 0 ->
      JTable.jops_at (etable_values frame_id_cell i) <= 1.
  Proof.
    intros i Hrange Hmore_range Henabled Hframe_nonzero.
    destruct (jtable_wellformedness (Z.to_nat i)) as [[Hframe_id_range Hframe_id_bound] _].
    { lia. }
    { replace  (Z.of_nat (Z.to_nat i)) with i by lia. auto. }
    replace (Z.of_nat (Z.to_nat i)) with i in * by lia.
    assert (Heid_value := eid_value i ltac:(lia) Henabled).
    assert (Henabled' : etable_values enabled_cell (etable_values frame_id_cell i - 1) = 1)
       by (apply enabled_seq_backwards with i; lia).
    destruct (jops_at_case (etable_values frame_id_cell i - 1))
               as [[? _] | [[? _] | [[? _] | [? _]]]].
    ** lia.
    ** lia.
    ** apply Henabled'.
    ** rewrite eid_value in H by (auto; lia).
       replace ((1 + (etable_values frame_id_cell i - 1))) with (etable_values frame_id_cell i) in H; lia.
    ** rewrite eid_value in H by (auto; lia).
       replace ((1 + (etable_values frame_id_cell i - 1))) with (etable_values frame_id_cell i) in H; lia.
    ** rewrite eid_value in H by (auto; lia).
       replace ((1 + (etable_values frame_id_cell i - 1))) with (etable_values frame_id_cell i) in H; lia.
    ** rewrite eid_value in H by (auto; lia).
       replace ((1 + (etable_values frame_id_cell i - 1))) with (etable_values frame_id_cell i) in H; lia.
Qed.

End jops_at_bounded.


Lemma eid_nonzero' : forall n,
 etable_values enabled_cell (Z.of_nat n) = 1 ->
 etable_values eid_cell (Z.of_nat n) > 0.
Proof.  
  induction n.
  - intros.
    simpl.
    rewrite initial_eid. lia.
  - intros Henabled.
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
    assert (Henabled' := (enabled_seq_prev (Z.of_nat n) ltac:(lia) Henabled)).
    rewrite (eid_change (Z.of_nat n) ltac:(lia) Henabled').
    specialize (IHn Henabled').
    lia.
Qed.

Lemma eid_nonzero : forall i,
 0 <= i ->
 etable_values enabled_cell i = 1 ->
 etable_values eid_cell i > 0.
Proof.
  intros.
  replace i with (Z.of_nat (Z.to_nat i)) in * by lia.
  apply eid_nonzero'; auto.
Qed.

