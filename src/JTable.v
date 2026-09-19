(* Copyright (C) CertiK 2024-2026 *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import CommonModel.
Require Import CommonData.
Require Import ImageTableModel.
Require Import JTableModel.

Open Scope Z_scope.

(* More convenient definition without the modulo operation, 
   proved equivalent below. *)
Definition encode_frame_table_entry_nomod (frame_id last_frame_id callee_fid fid iid : Z) :=
  let IID_SHIFT := 0 in
  let FID_SHIFT := IID_SHIFT + COMMON_RANGE_OFFSET in
  let CALLEE_FID := FID_SHIFT + COMMON_RANGE_OFFSET in
  let LAST_JUMP_FRAME_ID_SHIFT := CALLEE_FID + COMMON_RANGE_OFFSET in
  let FRAME_ID_SHIFT := LAST_JUMP_FRAME_ID_SHIFT + COMMON_RANGE_OFFSET in

  frame_id * (Z.shiftl 1 FRAME_ID_SHIFT) 
  + last_frame_id * (Z.shiftl 1 LAST_JUMP_FRAME_ID_SHIFT)
  + callee_fid * (Z.shiftl 1 CALLEE_FID)
  + fid * (Z.shiftl 1 FID_SHIFT)
  + iid.

Lemma jtable_offset_max_nonzero: JtableOffsetMax <> 0.
Proof.
  unfold JtableOffsetMax.
  lia.
Qed.

Lemma jtable_offset_max_pos: 0 < JtableOffsetMax.
Proof.
  unfold JtableOffsetMax.
  lia.
Qed.

Lemma jops_separate_pos:
  0 < JOPS_SEPARATE.
Proof. unfold JOPS_SEPARATE. lia. Qed.


Lemma Z_mul_mod_l:
  forall a b,
    (a * b) mod a = 0.
Proof.
  intros. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

  Lemma Z_div_mul:
    forall x m,
      m <> 0 ->
      x mod m = 0 ->
      x = (x / m) * m.
  Proof.
    intros x m Hm Hmod.
    rewrite Z.mul_comm.
    rewrite <- (Z_div_exact_full_2 x m) by lia.
    reflexivity.
  Qed.

  Lemma Z_mod_exists_mul:
    forall x m,
      m <> 0 ->
      x mod m = 0 ->
      exists k, x = k * m.
  Proof.
    intros x m Hm Hmod.
    exists (x / m).
    rewrite <- Z_div_mul by lia.
    reflexivity.
  Qed.

Lemma Z_add_mul_2: forall a, a + a = 2 * a.
Proof. intros. lia. Qed.

Lemma Z_add_mul_3: forall a, a + a + a = 3 * a.
Proof. intros. lia. Qed.

Lemma Z_add_mul_4: forall a, a + a + a + a = 4 * a.
Proof. intros. lia. Qed.

Lemma Z_shift_cons:
  forall a n,
    Z.shiftr a (Z.of_nat (S n)) = Z.shiftr (a / 2) (Z.of_nat n).
Proof.
  intros a n.
  replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia.
  replace (a / 2) with (a / 2 ^ 1) by reflexivity.
  rewrite <- Z.shiftr_div_pow2 by lia.
  rewrite Z.shiftr_shiftr by lia.
  reflexivity.
Qed.

Lemma Z_div_neg:
  forall a b,
    0 < b ->
    a <= 0 ->
    a / b <= 0.
Proof.
  intros a b Hb Ha.
  apply (Z_div_le a 0 b ltac:(lia)) in Ha.
  rewrite Zdiv_0_l in Ha.
  assumption.
Qed.

Lemma Z_div_pos:
  forall a b,
    0 < b ->
    0 < a / b ->
    0 < a.
Proof.
  intros a b Hb Hdiv.
  destruct (Z_zerop a) as [Hzero | Hnz].
  - rewrite Hzero in Hdiv.
    rewrite Z.div_0_l in Hdiv by lia.
    lia.
  - assert (a < 0 \/ a > 0) as [Hneg | Hpos] by lia.
    + assert (a <= 0) as Ha' by lia.
      assert (0 <= a / b) as Hdiv' by lia.
      pose proof (Z_div_neg a b ltac:(lia) Ha') as Hneg'.
      lia.
    + lia.
Qed.

Lemma Z_shiftr_pos':
  forall a n,
    (Z.shiftr a (Z.of_nat n)) > 0 ->
    a > 0.
Proof.
  intros a n Hshift. generalize n a Hshift. clear a n Hshift.
  induction n as [|n IHn]; intros a Hshift.
  - simpl in Hshift.
    rewrite Z.shiftr_0_r in Hshift.
    assumption.
  - rewrite Z_shift_cons in Hshift.
    apply IHn in Hshift.
    pose proof (Z_div_pos a 2 ltac:(lia) ltac:(lia)).
    lia.
Qed.

Lemma Z_shiftr_pos:
  forall a n,
    0 <= n ->
    0 < Z.shiftr a n ->
    0 < a.
Proof.
  intros a n Hn Hshift.
  pose (n' := Z.to_nat n).
  assert (n = Z.of_nat n') as Hn' by lia.
  rewrite Hn' in Hshift.
  pose proof (Z_shiftr_pos' a n' ltac:(lia)) as Hpos.
  lia.
Qed.

Lemma Z_shiftl_add:
  forall a b n,
    0 <= n ->
    Z.shiftl (a + b) n = Z.shiftl a n + Z.shiftl b n.
Proof.
  intros a b n Hn.
  replace (Z.shiftl a n) with (Z.shiftl a (0 + n)) by (rewrite Z.add_0_l; lia).
  rewrite shiftl_distr_l by lia.
  rewrite Z.shiftl_0_r.
  rewrite Z.add_comm.
  reflexivity.
Qed.

Lemma Z_land_shiftl_ones_0:
forall n x,
  0 <= n ->
  Z.land (Z.shiftl x n) (Z.ones n) = 0.
Proof.
  intros n x Hn.
  apply Z.bits_inj'. intros i Hlen.
  rewrite Z.land_spec.
  rewrite Z.bits_0.
  rewrite Z.shiftl_spec; [|lia].
  assert (i < n \/ n <= i)%Z as Hni by lia.
  destruct Hni as [Hni | Hni].
  - rewrite Z.testbit_neg_r; [|lia].
    rewrite Bool.andb_false_l.
    reflexivity.
  - erewrite Z.ones_spec_high with (n:=n)(m:=i); [|lia].
    rewrite Bool.andb_false_r.
    reflexivity.
Qed.

Lemma Z_land_shiftl_0':
  forall n x y,
    0 <= n ->
    0 < y < 2 ^ n ->
    Z.land (Z.shiftl x n) y = 0.
Proof.
  intros n x y Hn Hy.
  apply Z.bits_inj'. intros i Hlen.
  rewrite Z.land_spec.
  rewrite Z.shiftl_spec; [|lia].
  assert (i < n \/ n <= i)%Z as [Hni | Hni] by lia.
  - rewrite Z.testbit_neg_r; [|lia].
    rewrite Bool.andb_false_l.
    rewrite Z.testbit_0_l.
    reflexivity.
  - rewrite (Z.bits_above_log2 y i); [|lia|].
    rewrite Z.testbit_0_l.
    rewrite Bool.andb_false_r.
    reflexivity.
    + assert (Z.log2 y < n) as Hlog2yn.
      {
        apply Z.log2_lt_pow2; lia.
      }
      lia.
Qed.

Lemma Z_land_shiftl_0:
  forall n x y,
    0 <= n ->
    0 <= y < 2 ^ n ->
    Z.land (Z.shiftl x n) y = 0.
Proof.
  intros n x y Hn Hy.
  destruct (Z_zerop y) as [Hy0 | Hypos].
  - rewrite Hy0.
    rewrite Z.land_0_r.
    reflexivity.
  - apply Z_land_shiftl_0'; lia.
Qed.

Lemma Z_lor_shiftl_add:
  forall a b n,
    0 <= n ->
    0 <= b < 2 ^ n ->
    Z.lor (Z.shiftl a n) b = Z.shiftl a n + b.
Proof.
  intros a b n Hn Hb.
  pose proof (shiftl_land_0 n b a Hn Hb) as Hland.
  assert (Z.land (Z.shiftl a n) b = 0) as Hland' by (rewrite Z.land_comm; lia).
  rewrite Z.add_nocarry_lxor by lia.
  rewrite Z.lxor_lor by lia.
  reflexivity.
Qed.

Lemma Z_lor_shiftl_sub_r:
  forall a b n,
    0 <= n ->
    0 <= b < 2 ^ n ->
    Z.lor (Z.shiftl a n) b - b = Z.shiftl a n.
Proof.
  intros a b n Hn Hb.
  pose proof (Z_lor_shiftl_add a b n Hn Hb) as Hadd.
  lia.
Qed.

Lemma Z_segment_as_nat:
  forall i j k,
  i <= j <= k ->
  exists (m n: nat),
    j = i + Z.of_nat m /\
    k = i + Z.of_nat m + Z.of_nat n.
Proof.
  intros i j k Hij.
  exists (Z.to_nat (j - i)), (Z.to_nat (k - j)).
  split; [lia|].
  lia.
Qed.

Lemma Z_pow_lt_lt:
  forall a b k,
    1 < a ->
    0 < b ->
    1 < k ->
    a ^ b < a ^ (k * b).
Proof.
  intros until k. intros Ha Hb Hk.
  apply Z.pow_lt_mono_r; [lia|lia|..].
  rewrite Z.mul_comm.
  apply Z.lt_mul_diag_r; lia.
Qed.

Lemma Z_log2_0:
  Z.log2 0 = 0.
Proof. reflexivity. Qed.

Lemma Z_log2_pow_bound:
  forall val p,
    0 < p ->
    0 <= val < 2 ^ p ->
    0 <= Z.log2 val < p.
Proof.
  intros until p. intros Hp Hbound.
  pose proof (Z.log2_nonneg val) as Hnonneg.
  assert (val = 0 \/ 0 < val) as [Hzero | Hpos] by lia.
  - rewrite Hzero.
    rewrite Z_log2_0.
    lia.
  - pose proof (Z.log2_lt_pow2 val p Hpos) as Hlt.
    lia.
Qed.

Lemma ForallP_singleton:
  forall {A} (P : A -> Prop) (x : A) (l : list A),
    Forall P (x :: nil) -> P x.
Proof.
  intros. inversion H; subst. assumption.
Qed.


(* Unlike the ETable and MTable, the JTable doesn't use an "allocator" 
   but instead "handwrites" the table offsets. We prove the code directly
   against the Halo2-level table, but to make the rest of the proof 
   easier we manually prove an abstraction layer similar to what the 
   allocator provides. 

   This is called `ajtable`, for "allocated jtable".
 *)

Inductive ajtable_cols :=
| enabled_cell
| rest_cell
| entry_cell
| static_bit_cell.

Definition ajtable_values (c : ajtable_cols) (i : Z) :=
  match c with
  | enabled_cell => jtable_values data_col (JtableOffsetMax * i + JtableOffsetEnable)
  | rest_cell   => jtable_values data_col (JtableOffsetMax * i + JtableOffsetRest)
  | entry_cell  => jtable_values data_col (JtableOffsetMax * i + JtableOffsetEntry)
  | static_bit_cell => jtable_values static_bit_col (JtableOffsetMax * i)
  end.

Definition ajtable_numRow := Z.div jtable_numRow JtableOffsetMax.

Definition return_of_encoded_jops enc :=
  Z.shiftr enc JTableModel.JOPS_SEPARATE.

Definition call_of_encoded_jops enc :=
  Z.land enc (Z.ones JTableModel.JOPS_SEPARATE).

Opaque Z.mul Z.add.

Lemma ajtable_numRow_nonneg:
  0 <= ajtable_numRow.
Proof.
  pose proof jtable_numRow_nonneg.
  pose proof jtable_offset_max_pos.
  unfold ajtable_numRow.
  apply Z.div_pos; lia.
Qed.

Lemma ajtable_numRow_upper_bound:
  ajtable_numRow < 2 ^ JOPS_SEPARATE.
Proof.
  pose proof jtable_numRow_upper_bound as Hj.
  pose proof jtable_offset_max_pos as Hjmax.
  pose proof jtable_numRow_nonneg as Hnonneg.
  pose proof jops_separate_pos as Hsep.
  unfold ajtable_numRow.
  assert (jtable_numRow = 0 \/ 0 < jtable_numRow) as [Hj0 | Hjpos] by lia.
  - rewrite Hj0.
    rewrite Z.div_0_l by lia.
    apply Z.pow_pos_nonneg; lia.
  - apply Z.div_lt_upper_bound; [lia|].
    rewrite Z.mul_comm.
    assert (1 < JtableOffsetMax) as Hmax by (unfold JtableOffsetMax; lia).
    apply Z.lt_mul_r; lia.
Qed.

Lemma ajtable_numRow_lower_bound:
    STATIC_FRAME_ENTRY_NUMBER < ajtable_numRow.
Proof.
  pose proof jtable_numRow_lower_bound as Hj.
  unfold ajtable_numRow.
  assumption.
Qed.

Lemma ajtable_static_entries_first: forall i,
    ajtable_values static_bit_cell i = 1 <-> (i < STATIC_FRAME_ENTRY_NUMBER).
Proof.
  intros i.
  unfold ajtable_values.
  apply static_entries_first.
Qed.

Lemma ajtable_static_entries_id_zero: forall i,
    ajtable_values static_bit_cell i = 1 -> entry_id (ajtable_values entry_cell i) = 0.
Proof.
  intros i.
  unfold ajtable_values.
  apply static_entries_id_zero.
Qed.

Lemma ajtable_static_entries_next_id_zero: forall i,
    ajtable_values static_bit_cell i = 1 -> next_entry_id (ajtable_values entry_cell i) = 0.
Proof.
  intros i.
  unfold ajtable_values.
  apply static_entries_next_id_zero.
Qed.

Lemma ajtable_frame_id_is_positive: forall i,
    ajtable_values enabled_cell i = 1 -> 
    ajtable_values static_bit_cell i = 0 ->
    entry_id (ajtable_values entry_cell i) > 0.
Proof.
  intros i.
  unfold ajtable_values.
  apply frame_id_is_positive.
Qed.

Lemma enable_is_bit : forall i,
    0 <= i ->
    ajtable_values enabled_cell i = 0 \/ ajtable_values enabled_cell i = 1.
Proof.
  intros i Hrange.
  simpl.
  unfold JtableOffsetEnable.
  destruct (jtable_enable_is_bit (JtableOffsetMax*i) ltac:(unfold JtableOffsetMax; lia)) as [Hgate _].
  unfold enable in Hgate.
  simpl in Hgate.
  rewrite sel_spec in Hgate.
  replace ((JtableOffsetMax * i + 0) mod JtableOffsetMax) with 0 in Hgate.
  2: {
    replace (JtableOffsetMax*i + 0) with (i*JtableOffsetMax) by lia.
    rewrite Z_mod_mult.
    reflexivity.
  }
  unfold JtableOffsetEnable in *.
  simpl in Hgate.
  rewrite <- Z.mul_assoc in Hgate.
  apply Z.eq_mul_0 in Hgate.
  destruct Hgate; lia.
Qed.

Lemma static_is_bit': forall i,
  0 <= i ->
  ajtable_values static_bit_cell i = 0 \/ ajtable_values static_bit_cell i = 1.
Proof.
  intros i Hi.
  simpl.
  pose proof (static_is_bit (JtableOffsetMax * i)) as Hstatic.
  assumption.
Qed.

Lemma sel_col_aligned: forall i,
  0 <= i ->
  jtable_values sel_col (JtableOffsetMax * i) = 1.
Proof.
  intros i Hrange.
  rewrite sel_spec.
  rewrite Z.mul_comm.
  rewrite Z_mod_mult.
  simpl.
  reflexivity.
Qed.

Lemma rest_jops_change_enabled : forall i,
  0 <= i ->
  ajtable_values enabled_cell i = 1 ->
  ajtable_values rest_cell i
  = ajtable_values rest_cell (i+1)
     + (encode_jops 1 1) - (ajtable_values static_bit_cell i).
Proof.
  intros i Hrange.
  simpl.
  unfold JtableOffsetEnable, JtableOffsetRest.
  destruct (c3 (JtableOffsetMax*i) ltac:(unfold JtableOffsetMax; lia)) as [Hgate _].
  rewrite !Z.add_0_r in Hgate. rewrite !Z.add_0_r.
  intros Henable.
  simpl in Hgate.
  rewrite sel_col_aligned in Hgate by lia. rewrite Z.mul_1_r in Hgate.
  unfold enable, JtableOffsetEnable in Hgate.
  rewrite Z.add_0_r in Hgate.
  rewrite Henable in Hgate.
  rewrite !Z.mul_1_r in Hgate.
  unfold rest, next_rest in Hgate.
  unfold JtableOffsetRest in Hgate.
  assert ((JtableOffsetMax * i + (1 + JtableOffsetMax)) = (JtableOffsetMax * (i + 1) + 1)) as Hrest by lia.
  rewrite Hrest in Hgate.
  lia.
Qed.

Lemma rest_jops_change_disabled : forall i,
  0 <= i ->
  ajtable_values enabled_cell i = 0 ->
  ajtable_values rest_cell i = ajtable_values rest_cell (i+1).
Proof.
  intros i Hrange Henable.
  simpl.
  pose proof (c3 (JtableOffsetMax*i) ltac:(unfold JtableOffsetMax; lia)) as Hgate.
  unfold enable, rest, next_rest in Hgate, Henable; simpl in Hgate, Henable.
  rewrite Henable in Hgate.
  rewrite !Z.add_0_r in Hgate.
  rewrite !Z.mul_0_r in Hgate.
  rewrite sel_spec in Hgate.
  assert (((JtableOffsetMax * i) mod JtableOffsetMax) = 0) as Hmod by 
      (rewrite Z_mul_mod_l; lia).
  rewrite Hmod in Hgate; simpl in Hgate.
  rewrite !Z.mul_1_r in Hgate.
  destruct Hgate as (_ & Hgate & _).
  replace ((JtableOffsetMax * i + (JtableOffsetRest + JtableOffsetMax))) with
    (JtableOffsetMax * (i + 1) + JtableOffsetRest) in Hgate by lia.
  lia.
Qed.

Lemma rest_jops_ends_up : forall i,
  0 <= i ->
  ajtable_values enabled_cell i = 0 ->
  ajtable_values static_bit_cell i = 0 ->
  ajtable_values rest_cell i = 0.
Proof.
  intros i Hrange Henable Hstatic.
  simpl. simpl in Henable, Hstatic.
  pose proof (c5 (JtableOffsetMax*i) ltac:(unfold JtableOffsetMax; lia)) as Hgate.
  unfold enable, rest in Hgate.
  Opaque Z.sub.
  simpl in Hgate.
  Transparent Z.sub.
  rewrite !Z.add_0_r in Hgate.
  rewrite !Z.add_0_r in Henable.
  rewrite Henable, Hstatic in Hgate.
  rewrite sel_spec in Hgate.
  assert (((JtableOffsetMax * i) mod JtableOffsetMax) = 0) as Hmod by 
      (rewrite Z_mul_mod_l; lia).
  rewrite Hmod in Hgate; simpl in Hgate.
  replace ((1 - 0) * (1 - 0)) with 1 in Hgate by lia.
  rewrite Z.mul_1_r, Z.mul_1_l in Hgate.
  destruct Hgate as [Hgate _].
  assumption.
Qed.

Lemma disabled_entry_zero : forall i,
  0 <= i ->
  ajtable_values enabled_cell i = 0 ->
  ajtable_values entry_cell i = 0.
Proof.
  intros i Hrange Henable.
  simpl. simpl in Henable.
  pose proof (c6 (JtableOffsetMax*i) ltac:(unfold JtableOffsetMax; lia)) as Hgate.
  unfold enable, entry in Hgate.
  Opaque Z.sub.
  simpl in Hgate.
  Transparent Z.sub.
  rewrite !Z.add_0_r in Hgate.
  rewrite !Z.add_0_r in Henable.
  rewrite Henable in Hgate.
  rewrite sel_spec in Hgate.
  assert (((JtableOffsetMax * i) mod JtableOffsetMax) = 0) as Hmod by 
      (rewrite Z_mul_mod_l; lia).
  rewrite Hmod in Hgate; simpl in Hgate.
  rewrite Z.mul_1_l, Z.mul_1_r in Hgate.
  destruct Hgate as [Hgate _].
  assumption.
Qed.

Lemma entry_nonzero_enabled: forall i,
  0 <= i ->
  ajtable_values entry_cell i > 0 ->
  ajtable_values enabled_cell i = 1.
Proof.
  intros i Hi Hentry.
  pose proof (c6 (JtableOffsetMax*i) ltac:(unfold JtableOffsetMax; lia)) as Hgate.
  unfold enable, entry in Hgate.
  Opaque Z.sub.
  simpl in Hgate.
  Transparent Z.sub.
  rewrite !Z.add_0_r in Hgate.
  rewrite sel_col_aligned in Hgate by lia.
  rewrite Z.mul_1_r in Hgate.
  destruct Hgate as [Hgate _].
  remember (jtable_values data_col (JtableOffsetMax * i)) as enable.
  simpl in Hentry.
  remember (jtable_values data_col (JtableOffsetMax * i + JtableOffsetEntry)) as entry.
  assert (enable = 1) as Henable.
  {
    destruct (enable_is_bit i ltac:(lia)) as [Henable | Henable].
    - simpl in Henable.
      unfold JtableOffsetEnable in Henable.
      rewrite Z.add_0_r in Henable.
      rewrite <- Heqenable in Henable.
      exfalso.
      lia.
    - simpl in Henable.
      unfold JtableOffsetEnable in Henable.
      rewrite Z.add_0_r in Henable.
      rewrite <- Heqenable in Henable.
      assumption.
  }
  simpl.
  unfold JtableOffsetEnable.
  rewrite Z.add_0_r.
  rewrite <- Heqenable.
  assumption.
Qed.

Lemma encode_frame_table_entry_bound: forall frame_id last_frame_id callee_fid fid iid,
    0 <= frame_id < common ->
    0 <= last_frame_id < common ->
    0 <= callee_fid < common ->
    0 <= fid < common ->
    0 <= iid < common ->
    0 <= encode_frame_table_entry_nomod frame_id last_frame_id callee_fid fid iid < field_order.
Proof.
  intros until iid. intros Hframe Hlast Hcallee Hfid Hiid.
  unfold encode_frame_table_entry_nomod.
  rewrite !Z.add_0_l.
  replace ((COMMON_RANGE_OFFSET + COMMON_RANGE_OFFSET)) with
      (2 * COMMON_RANGE_OFFSET) by lia.
  replace (2 * COMMON_RANGE_OFFSET + COMMON_RANGE_OFFSET) with
      (3 * COMMON_RANGE_OFFSET) by lia.
  replace (3 * COMMON_RANGE_OFFSET + COMMON_RANGE_OFFSET) with
      (4 * COMMON_RANGE_OFFSET) by lia.
  assert (COMMON_RANGE_OFFSET > 0) as Hoffset by (unfold COMMON_RANGE_OFFSET; lia).
  rewrite !shiftl_1_n by lia.
  pose proof (encode_frame_table_entry_order) as Horder.
  rewrite !common_is_COMMON_RANGE_OFFSET in *.
  rewrite Zplus_assoc_reverse.
  remember (Z.shiftl fid COMMON_RANGE_OFFSET + iid) as entry2.
  rewrite Zplus_assoc_reverse.
  remember (Z.shiftl callee_fid (2 * COMMON_RANGE_OFFSET) + entry2) as entry3.
  rewrite Zplus_assoc_reverse.
  remember (Z.shiftl last_frame_id (3 * COMMON_RANGE_OFFSET) + entry3) as entry4.
  assert (0 <= Z.shiftl frame_id (4 * COMMON_RANGE_OFFSET) + entry4 < 2 ^ (5 * COMMON_RANGE_OFFSET)) as Hentry.
  {
    apply disjoint_add_range_rev with (a:=entry4) (b:=frame_id)
      (n:=4 * COMMON_RANGE_OFFSET) (m:=COMMON_RANGE_OFFSET); [lia|lia|..|lia].
    rewrite Heqentry4.
    apply disjoint_add_range_rev with (a:=entry3) (b:=last_frame_id)
      (n:=3 * COMMON_RANGE_OFFSET) (m:=COMMON_RANGE_OFFSET); [lia|lia|..|lia].
    rewrite Heqentry3.
    apply disjoint_add_range_rev with (a:=entry2) (b:=callee_fid)
      (n:=2 * COMMON_RANGE_OFFSET) (m:=COMMON_RANGE_OFFSET); [lia|lia|..|lia].
    rewrite Heqentry2.
    apply disjoint_add_range_rev with (a:=iid) (b:=fid)
      (n:=COMMON_RANGE_OFFSET) (m:=COMMON_RANGE_OFFSET); [lia|lia|..|lia].
    assumption.
  }
  lia.
Qed.

Lemma encode_frame_table_entry_eq: forall frame_id last_frame_id callee_fid fid iid,
    0 <= frame_id < common ->
    0 <= last_frame_id < common ->
    0 <= callee_fid < common ->
    0 <= fid < common ->
    0 <= iid < common ->
    encode_frame_table_entry frame_id last_frame_id callee_fid fid iid
    = encode_frame_table_entry_nomod frame_id last_frame_id callee_fid fid iid.
Proof.
  intros until iid. intros Hframe Hlast Hcallee Hfid Hiid.
  generalize (encode_frame_table_entry_bound frame_id last_frame_id callee_fid fid iid Hframe Hlast Hcallee Hfid Hiid).
  unfold encode_frame_table_entry, encode_frame_table_entry_nomod.
  rewrite !Z.add_0_l.
  intros Hbound.
  rewrite Z.mod_small; lia.
Qed.

Lemma encode_frame_table_entry_inj : forall frame_id frame_id' last_frame_id last_frame_id' callee_fid callee_fid' fid fid' iid iid',
    0 <= frame_id  < common ->
    0 <= frame_id' < common ->
    0 <= last_frame_id  < common ->
    0 <= last_frame_id' < common ->
    0 <= callee_fid  < common ->
    0 <= callee_fid' < common ->
    0 <= fid  < common ->
    0 <= fid' < common ->
    0 <= iid  < common ->
    0 <= iid' < common ->
    encode_frame_table_entry frame_id last_frame_id callee_fid fid iid
    = encode_frame_table_entry frame_id' last_frame_id' callee_fid' fid' iid' ->
    (frame_id=frame_id'
     /\ last_frame_id=last_frame_id'
     /\ callee_fid=callee_fid'
     /\ fid=fid'
     /\ iid=iid').
Proof.
  intros until iid'.
  intros Hframe Hframe' Hlast Hlast' Hcallee Hcallee' Hfid Hfid' Hiid Hiid' Heq.
  rewrite !encode_frame_table_entry_eq in Heq by lia.
  rewrite common_is_COMMON_RANGE_OFFSET in *.
  unfold encode_frame_table_entry_nomod in Heq.
  rewrite !Z.add_0_l in Heq.
  assert (0 <= COMMON_RANGE_OFFSET) as Hoffset 
    by (unfold COMMON_RANGE_OFFSET; lia).
  rewrite !shiftl_1_n in Heq by lia.
  rewrite Z_add_mul_3 in Heq.
  remember COMMON_RANGE_OFFSET as OFF.
  replace (3 * OFF + OFF) with (OFF + 3 * OFF) in Heq by lia.
  rewrite !shiftl_distr_l in Heq by lia.
  rewrite Z_add_mul_2 in Heq.
  replace (3 * OFF) with (OFF + 2 * OFF) in Heq by lia.
  rewrite !shiftl_distr_l in Heq by lia.
  replace (2 * OFF) with (OFF + OFF) in Heq by lia.
  rewrite !shiftl_distr_l in Heq by lia.
  eapply disjoint_inj_rev in Heq as [H0 Heq]; [|lia|lia|lia].
  eapply disjoint_inj in Heq as [H1 Heq]; [|lia|lia|lia].
  eapply disjoint_inj in Heq as [H2 Heq]; [|lia|lia|lia].
  eapply disjoint_inj in Heq as [He Heq]; [|lia|lia|lia].
  split; [assumption|].
  split; [assumption|].
  split; [assumption|].
  split; [assumption|].
  assumption.
Qed.

(**
 * Entry ID
 *)

Lemma entry_id_spec  : forall frame_id last_frame_id callee_fid fid iid ,
    0 <= frame_id  < common ->
    0 <= last_frame_id  < common ->
    0 <= callee_fid  < common ->
    0 <= fid  < common ->
    0 <= iid  < common ->
    entry_id (encode_frame_table_entry frame_id last_frame_id callee_fid fid iid) = frame_id.
Proof.
  intros until iid. intros Hframe Hlast Hcallee Hfid Hiid.
  rewrite encode_frame_table_entry_eq by lia.
  unfold entry_id, encode_frame_table_entry_nomod.
  rewrite !Z.add_0_l.
  rewrite Z_add_mul_4.
  rewrite Z_add_mul_3, Z_add_mul_2.
  assert (0 <= COMMON_RANGE_OFFSET) as Hoff by (unfold COMMON_RANGE_OFFSET; lia).
  rewrite !shiftl_1_n by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  do 3 (rewrite <- Z.add_assoc).
  rewrite Z.add_comm.
  rewrite Z.div_add by lia.
  rewrite Z.div_small; [lia|].
  remember (Z.shiftl fid COMMON_RANGE_OFFSET + iid) as entry2.
  remember (Z.shiftl callee_fid (2 * COMMON_RANGE_OFFSET) + entry2) as entry3.
  rewrite common_is_COMMON_RANGE_OFFSET in *.
  assert (0 <= entry2 < 2 ^ (2 * COMMON_RANGE_OFFSET)) as Hentry2.
  {
    rewrite Heqentry2.
    replace (2 * COMMON_RANGE_OFFSET) with (COMMON_RANGE_OFFSET + COMMON_RANGE_OFFSET) by lia.
    apply disjoint_add_range_rev; lia.
  }
  assert (0 <= entry3 < 2 ^ (3 * COMMON_RANGE_OFFSET)) as Hentry3.
  {
    rewrite Heqentry3.
    replace (3 * COMMON_RANGE_OFFSET) with (2 * COMMON_RANGE_OFFSET + COMMON_RANGE_OFFSET) by lia.
    apply disjoint_add_range_rev; lia.
  }
  replace (4 * COMMON_RANGE_OFFSET) with (3 * COMMON_RANGE_OFFSET + COMMON_RANGE_OFFSET) by lia.
  apply disjoint_add_range_rev; lia.
Qed.

Lemma next_entry_id_spec  : forall frame_id last_frame_id callee_fid fid iid ,
    0 <= frame_id  < common ->
    0 <= last_frame_id  < common ->
    0 <= callee_fid  < common ->
    0 <= fid  < common ->
    0 <= iid  < common ->
    next_entry_id (encode_frame_table_entry frame_id last_frame_id callee_fid fid iid) = last_frame_id.
Proof.
  intros until iid. intros Hframe Hlast Hcallee Hfid Hiid.
  rewrite encode_frame_table_entry_eq by lia.
  unfold next_entry_id, encode_frame_table_entry_nomod.
  rewrite !Z.add_0_l.
  rewrite Z_add_mul_4.
  rewrite Z_add_mul_3, Z_add_mul_2.
  assert (0 <= COMMON_RANGE_OFFSET) as Hoff by (unfold COMMON_RANGE_OFFSET; lia).
  rewrite !shiftl_1_n by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite !Z.shiftr_div_pow2 by lia.

  replace
    (frame_id * 2 ^ (4 * COMMON_RANGE_OFFSET) + last_frame_id * 2 ^ (3 * COMMON_RANGE_OFFSET)
      + callee_fid * 2 ^ (2 * COMMON_RANGE_OFFSET) + fid * 2 ^ COMMON_RANGE_OFFSET + iid)
    with
    ((callee_fid * 2 ^ (2 * COMMON_RANGE_OFFSET) + fid * 2 ^ COMMON_RANGE_OFFSET + iid)
      + (frame_id * 2 ^ (4 * COMMON_RANGE_OFFSET) + last_frame_id * 2 ^ (3 * COMMON_RANGE_OFFSET)))
    by lia.

  replace (frame_id * 2 ^ (4 * COMMON_RANGE_OFFSET) + last_frame_id * 2 ^ (3 * COMMON_RANGE_OFFSET))
    with  ((frame_id * 2 ^ COMMON_RANGE_OFFSET + last_frame_id) * 2 ^ (3 * COMMON_RANGE_OFFSET))
          by (unfold COMMON_RANGE_OFFSET; lia).

  rewrite Z_div_plus by (unfold COMMON_RANGE_OFFSET; lia).

  rewrite Z.div_small.
  2: {
    rewrite JTableModel.common_is_COMMON_RANGE_OFFSET in *.
    unfold COMMON_RANGE_OFFSET in *.
    lia.
   }

  rewrite Z.add_0_l.

  rewrite <- Z.shiftl_mul_pow2 by lia.
  rewrite Z.add_comm.
  rewrite IntegerFunctions.plus_lor_n.
  2: { unfold COMMON_RANGE_OFFSET; lia. }
  2: { rewrite <- common_is_COMMON_RANGE_OFFSET. lia. }
  rewrite Z.land_lor_distr_l.
  rewrite IntegerFunctions.land_ones_high by (unfold COMMON_RANGE_OFFSET; lia).
  rewrite Z.lor_0_r.
  destruct (Z.eq_dec last_frame_id 0).
  - subst.
    rewrite Z.land_0_l.
    reflexivity.
  - rewrite Z.land_ones_low; try lia.
    rewrite <- Z.log2_lt_pow2; try lia.
    rewrite JTableModel.common_is_COMMON_RANGE_OFFSET in *.
    lia.
Qed.

Lemma frame_id_has_entry:
  forall entry frame_id,
  0 < frame_id ->
  entry_id entry = frame_id ->
  entry > 0.
Proof.
  intros entry frame_id Hframe Hentry.
  unfold entry_id in Hentry.
  rewrite Z.add_0_l in Hentry.
  replace (COMMON_RANGE_OFFSET + COMMON_RANGE_OFFSET +
            COMMON_RANGE_OFFSET + COMMON_RANGE_OFFSET) with 
          (4 * COMMON_RANGE_OFFSET) in Hentry by lia.
  remember (4 * COMMON_RANGE_OFFSET) as shift.
  assert (0 <= shift) as Hshift.
  {
    rewrite Heqshift.
    unfold COMMON_RANGE_OFFSET.
    lia.
  }
  rewrite <- Hentry in Hframe.
  pose proof (Z_shiftr_pos entry shift Hshift Hframe) as Hentry'.
  lia.
Qed.

Lemma jops_encode_range:
  forall n_calls n_returns,
    0 <= n_calls < 2 ^ JOPS_SEPARATE ->
    0 <= n_returns < 2 ^ JOPS_SEPARATE ->
    0 <= Z.lor (Z.shiftl n_returns JOPS_SEPARATE) n_calls < 2 ^ (2 * JOPS_SEPARATE).
Proof.
  intros until n_returns. intros Hcalls Hreturns.
  pose proof jops_separate_pos as Hsep.
  split.
  - apply Z.lor_nonneg; split.
    + apply Z.shiftl_nonneg; lia.
    + lia.
  - destruct (Z_zerop n_returns) as [Hzero | Hnonzero].
    + rewrite Hzero.
      rewrite Z.shiftl_0_l.
      rewrite Z.lor_0_l.
      assert (2 ^ JOPS_SEPARATE < 2 ^ (2 * JOPS_SEPARATE))
        as Hpow
        by (apply Z_pow_lt_lt; lia).
      lia.
    + assert (0 <= n_returns) as Hret by lia.
      pose proof (Z_log2_pow_bound n_returns JOPS_SEPARATE Hsep Hreturns) as Hlog_ret.
      pose proof (Z_log2_pow_bound n_calls JOPS_SEPARATE Hsep Hcalls) as Hlog_call.
      apply Z.log2_lt_cancel.
      rewrite Z.log2_lor.
      * rewrite Z.log2_shiftl by lia.
        rewrite Z.max_l by lia.
        rewrite Z.log2_pow2 by lia.
        lia.
      * apply Z.shiftl_nonneg; lia.
      * lia.
Qed.


Lemma jops_encode_unwrap:
  forall n_calls n_returns,
    0 <= n_calls < 2 ^ JOPS_SEPARATE ->
    0 <= n_returns < 2 ^ JOPS_SEPARATE ->
    encode_jops n_returns n_calls = Z.lor (Z.shiftl n_returns JOPS_SEPARATE) n_calls.
Proof.
  intros until n_returns. intros Hcalls Hreturns.
  unfold encode_jops.
  pose proof (jops_encode_range n_calls n_returns Hcalls Hreturns) as Hbound.
  pose proof encode_jops_order as Horder.
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.

Lemma encode_jops_0:
  encode_jops 0 0 = 0.
Proof.
  rewrite jops_encode_unwrap by (unfold JOPS_SEPARATE; lia).
  rewrite Z.shiftl_0_l.
  rewrite Z.lor_0_l.
  reflexivity.
Qed.

Lemma encode_jops_sub_1:
  encode_jops 1 1 - 1 = Z.shiftl 1 JOPS_SEPARATE.
Proof.
  rewrite jops_encode_unwrap by (unfold JOPS_SEPARATE; lia).
  rewrite Z_lor_shiftl_sub_r by (unfold JOPS_SEPARATE; lia).
  reflexivity.
Qed.

Lemma encode_jops_1:
  Z.land (encode_jops 1 1) (Z.ones (JOPS_SEPARATE)) = 1.
Proof.
  rewrite jops_encode_unwrap by (unfold JOPS_SEPARATE; lia).
  rewrite Z.land_lor_distr_l by (unfold JOPS_SEPARATE; lia).
  rewrite Z_land_shiftl_ones_0 by (unfold JOPS_SEPARATE; lia).
  rewrite Z.lor_0_l.
  rewrite Z.land_ones by (unfold JOPS_SEPARATE; lia).
  rewrite Z.mod_small by (unfold JOPS_SEPARATE; lia).
  reflexivity.
Qed.

Lemma encode_jops_1_nonneg:
  0 <= encode_jops 1 1.
Proof.
  rewrite jops_encode_unwrap by (unfold JOPS_SEPARATE; lia).
  apply Z.lor_nonneg; split.
  - apply Z.shiftl_nonneg; lia.
  - lia.
Qed.

Lemma encode_jops_nonneg:
  forall r c,
    0 <= r < 2 ^ JOPS_SEPARATE ->
    0 <= c < 2 ^ JOPS_SEPARATE ->
    0 <= encode_jops r c.
Proof.
  intros r c Hr Hc.
  rewrite jops_encode_unwrap by lia. 
  apply Z.lor_nonneg; split.
  - apply Z.shiftl_nonneg; lia.
  - lia.
Qed.

Lemma encode_jops_sub_static_nonneg:
  forall i,
    0 <= i ->
    0 <= encode_jops 1 1 - ajtable_values static_bit_cell i.
Proof.
  intros i Hi.
  pose proof encode_jops_1_nonneg as Henc.
  pose proof (static_is_bit' i Hi) as [Hsta | Hsta]; rewrite Hsta.
  - rewrite Z.sub_0_r.
    lia.
  - rewrite encode_jops_sub_1.
    apply Z.shiftl_nonneg; lia.
Qed.

  Lemma jops_encode_return:
    forall n_calls n_returns enc,
      0 <= n_calls < 2 ^ JOPS_SEPARATE ->
      0 <= n_returns < 2 ^ JOPS_SEPARATE ->
      encode_jops n_returns n_calls = enc ->
      return_of_encoded_jops enc = n_returns.
  Proof.
    intros until enc. intros Hcall Hret Henc.
    unfold return_of_encoded_jops.
    rewrite <- Henc.
    pose proof jops_separate_pos as Hsep.
    rewrite jops_encode_unwrap by lia.
    rewrite Z.shiftr_lor by lia.
    rewrite Z.shiftr_shiftl_r by lia.
    rewrite Z.sub_diag.
    assert (Z.shiftr n_calls JOPS_SEPARATE = 0) as Hcalls.
    {
      apply Z.shiftr_eq_0.
      - lia.
      - assert (n_calls = 0 \/ 0 < n_calls) as [Hc0 | Hcpos] by lia.
        + rewrite Hc0.
          rewrite Z_log2_0.
          lia.
        + apply Z.log2_lt_pow2; lia.
    }
    rewrite Hcalls.
    rewrite Z.lor_0_r.
    rewrite Z.shiftr_0_r.
    reflexivity.
  Qed.

  Lemma jops_encode_call:
    forall n_calls n_returns enc,
      0 <= n_calls < 2 ^ JOPS_SEPARATE ->
      0 <= n_returns < 2 ^ JOPS_SEPARATE ->
      encode_jops n_returns n_calls = enc ->
      call_of_encoded_jops enc = n_calls.
  Proof.
    intros until enc. intros Hcall Hret Henc.
    unfold call_of_encoded_jops.
    rewrite <- Henc.
    pose proof jops_separate_pos as Hsep.
    rewrite jops_encode_unwrap by lia.
    rewrite Z.land_lor_distr_l by lia.
    assert (Z.land (Z.shiftl n_returns JOPS_SEPARATE) 
      (Z.ones JOPS_SEPARATE) = 0) as Hret'.
    {
      apply Z_land_shiftl_ones_0; lia.
    }
    rewrite Hret'.
    rewrite Z.lor_0_l.
    rewrite Z.land_ones by lia.
    rewrite Z.mod_small by lia.
    reflexivity.
  Qed.

  Lemma encode_jops_add:
    forall c1 r1 c2 r2,
      0 <= c1 ->
      0 <= r1 ->
      0 <= c2 ->
      0 <= r2 ->
      c1 + c2 < 2 ^ JOPS_SEPARATE ->
      r1 + r2 < 2 ^ JOPS_SEPARATE ->
      encode_jops r1 c1 + encode_jops r2 c2 = encode_jops (r1 + r2) (c1 + c2).
  Proof.
    intros until r2. intros Hc1 Hr1 Hc2 Hr2 Hc Hr.
    pose proof jops_separate_pos as Hsep.
    assert (c1 < 2 ^ JOPS_SEPARATE) as Hc1' by lia.
    assert (c2 < 2 ^ JOPS_SEPARATE) as Hc2' by lia.
    assert (r1 < 2 ^ JOPS_SEPARATE) as Hr1' by lia.
    assert (r2 < 2 ^ JOPS_SEPARATE) as Hr2' by lia.
    rewrite !jops_encode_unwrap by lia.
    assert (Z.land (Z.shiftl r1 JOPS_SEPARATE) c1 = 0) as Hr1c1 by (apply Z_land_shiftl_0; lia).
    assert (Z.land (Z.shiftl r2 JOPS_SEPARATE) c2 = 0) as Hr2c2 by (apply Z_land_shiftl_0; lia).
    assert (Z.land (Z.shiftl (r1 + r2) JOPS_SEPARATE) (c1 + c2) = 0) as Hr1r2c1c2 by (apply Z_land_shiftl_0; lia).
    do 3 (rewrite <- Z.lxor_lor by lia).
    do 3 (rewrite <- Z.add_nocarry_lxor by lia).
    rewrite !Z.add_assoc.
    replace (Z.shiftl r1 JOPS_SEPARATE + c1 + Z.shiftl r2 JOPS_SEPARATE + c2) with
      (Z.shiftl r1 JOPS_SEPARATE + Z.shiftl r2 JOPS_SEPARATE + c1 + c2) by lia.
    rewrite <- Z_shiftl_add by lia.
    reflexivity.
  Qed.

  Lemma encode_jops_i_upper_bound:
    forall i,
      0 <= i <= ajtable_numRow ->
      encode_jops i i < 2 ^ (2 * JOPS_SEPARATE).
  Proof.
    intros i Hi.
    pose proof ajtable_numRow_upper_bound as Hbound.
    pose proof ajtable_numRow_nonneg as Hnonneg.
    pose proof (jops_encode_range i i ltac:(lia) ltac:(lia)) as Hrange.
    rewrite jops_encode_unwrap by lia.
    lia.
  Qed.

  Lemma encode_jops_of_upper_bound:
    encode_jops ajtable_numRow ajtable_numRow < 2 ^ (2 * JOPS_SEPARATE).
  Proof.
    pose proof ajtable_numRow_upper_bound as Hbound.
    pose proof ajtable_numRow_nonneg as Hnonneg.
    pose proof (jops_encode_range ajtable_numRow ajtable_numRow ltac:(lia) ltac:(lia)) as Hrange.
    rewrite jops_encode_unwrap by lia.
    lia.
  Qed.

Require Import Bool.

(* Counting jops. These lemmas similar to the corresponding definitions in gather_mops in MTable.v. *)

Section gather_jops. 
  
  Section gather.
  Variable min_eid max_eid :Z.
  
  Fixpoint gather_jops' (i : Z) (n:nat) :=
    if i <? ajtable_numRow - 1 then
      match n with
      | O => 0
      | S n' =>
        (
          if (ajtable_values enabled_cell i =? 1) 
          then
              (if (min_eid <=? entry_id (ajtable_values entry_cell i))
               && (entry_id (ajtable_values entry_cell i) <? max_eid)
               then
                 (if ajtable_values static_bit_cell i =? 1 then 0 else 1)
               else 0)
          else
            0
        ) + gather_jops' (i + 1) n'
      end
    else
      0.

  Definition gather_jops (from to : Z) :=
    gather_jops' from (Z.to_nat (to - from)).

  Definition jops_of i :=
    if i <? ajtable_numRow - 1 then
      if (ajtable_values enabled_cell i =? 1) 
      then
        if (min_eid <=? entry_id (ajtable_values entry_cell i))
            && (entry_id (ajtable_values entry_cell i) <? max_eid)
        then
          (if ajtable_values static_bit_cell i =? 1 then 0 else 1)
        else 0
      else 0
    else 0.

  Lemma jops_of_last:
      jops_of (ajtable_numRow - 1) = 0.
  Proof.
    unfold jops_of.
    replace (ajtable_numRow - 1 <? ajtable_numRow - 1) with false by lia.
    reflexivity.
  Qed.

  Lemma jops_of_invalid_i:
    forall i,
      i >= ajtable_numRow ->
      jops_of i = 0.
  Proof.
    intros i Hi.
    unfold jops_of.
    replace (i <? ajtable_numRow - 1) with false by lia.
    reflexivity.
  Qed.

  Lemma gather_jops_unwrap:
    forall i n,
    gather_jops i (i + Z.of_nat n) = gather_jops' i n.
  Proof.
    intros i n.
    unfold gather_jops.
    replace (i + Z.of_nat n - i) with (Z.of_nat n) by lia.
    rewrite Nat2Z.id by lia.
    reflexivity.
  Qed.

  Lemma gather_jops'_unwrap:
   forall i j,
     gather_jops i j = gather_jops' i (Z.to_nat (j - i)).
  Proof.
    intros i j.
    unfold gather_jops.
    reflexivity.
  Qed.

  Lemma gather_jops'_0:
    forall i,
    gather_jops' i 0 = 0.
  Proof.
    intros i.
    simpl.
    destruct (i <? ajtable_numRow - 1); reflexivity.
  Qed.

  Lemma gather_jops'_1:
    forall i,
    gather_jops' i (1%nat) = jops_of i.
  Proof.
    intros i.
    unfold gather_jops', jops_of.
    destruct (i <? ajtable_numRow - 1) eqn: Hvalid; [|reflexivity].
    destruct (i + 1 <? ajtable_numRow - 1); rewrite Z.add_0_r;
    reflexivity.
  Qed.

  Lemma gather_jops_1:
    forall i,
    gather_jops i (i + 1) = jops_of i.
  Proof.
    intros i.
    rewrite gather_jops'_unwrap by lia.
    replace (Z.to_nat (i + 1 - i)) with 1%nat by lia.
    rewrite gather_jops'_1.
    reflexivity.
  Qed.

  Lemma gather_jops'_head:
    forall i n,
    gather_jops' i (S n) = jops_of i + gather_jops' (i + 1) n.
  Proof.
    intros i n.
    destruct (i <? ajtable_numRow - 1) eqn: Hi_range.
    - unfold jops_of.
      simpl.
      rewrite Hi_range.
      reflexivity.
    - unfold jops_of.
      simpl.
      rewrite Hi_range.
      destruct n as [|n].
      + rewrite gather_jops'_0.
        reflexivity.
      + simpl.
        assert (i + 1 <? ajtable_numRow - 1 = false) as Hnext_range by lia.
        rewrite Hnext_range.
        reflexivity.
  Qed.

  Lemma gather_jops'_tail:
    forall i n,
    gather_jops' i (S n) = gather_jops' i n + jops_of (i + Z.of_nat n).
  Proof.
    intros i n. generalize i. clear i.
    induction n as [|n IHn].
    - (* n = 0 *)
      intros i.
      rewrite gather_jops'_1.
      rewrite gather_jops'_0.
      simpl.
      rewrite Z.add_0_r. rewrite Z.add_0_l.
      reflexivity.
    - (* n = S n' *)
      intros i.
      rewrite gather_jops'_head by lia.
      generalize (IHn (i + 1)). intros Hind.
      rewrite Hind.
      rewrite gather_jops'_head by lia.
      replace (i + Z.of_nat (S n)) with (i + 1 + Z.of_nat n) by lia.
      rewrite Z.add_assoc.
      reflexivity.
  Qed.

  Lemma gather_jops'_invalid_i:
    forall i n,
    i >= ajtable_numRow ->
    gather_jops' i n = 0.
  Proof.
    intros i n Hi.
    destruct n as [|n].
    - rewrite gather_jops'_0.
      reflexivity.
    - simpl.
      replace (i <? ajtable_numRow - 1) with false by lia.
      reflexivity.
  Qed.

  Lemma jops_of_disabled:
    forall i,
    ajtable_values enabled_cell i = 0 ->
    jops_of i = 0.
  Proof.
    intros i Hdisabled.
    unfold jops_of.
    rewrite Hdisabled.
    destruct (i <? ajtable_numRow - 1); reflexivity.
  Qed.

  Lemma jops_of_out_of_range:
    forall i,
    ajtable_values enabled_cell i = 1 ->
    min_eid > entry_id (ajtable_values entry_cell i) \/ max_eid <= entry_id (ajtable_values entry_cell i) ->
    jops_of i = 0.
  Proof.
    intros i Henable Hrange.
    unfold jops_of.
    rewrite Henable.
    remember (entry_id (ajtable_values entry_cell i)) as eid.
    destruct Hrange as [Hlow | Hhigh].
    - replace (min_eid <=? eid) with false by lia.
      rewrite andb_false_l.
      destruct (i <? ajtable_numRow - 1) eqn: Hi_range; reflexivity.
    - replace (eid <? max_eid) with false by lia.
      rewrite andb_false_r.
      destruct (i <? ajtable_numRow - 1) eqn: Hi_range; reflexivity.
  Qed.

  Lemma jops_of_static:
    forall i,
    ajtable_values static_bit_cell i = 1 ->
    jops_of i = 0.
  Proof.
    intros i Hstatic.
    unfold jops_of.
    rewrite Hstatic.
    remember (entry_id (ajtable_values entry_cell i)) as eid.
    destruct (i <? ajtable_numRow - 1) eqn: Hi_range; [|reflexivity].
    destruct (ajtable_values enabled_cell i =? 1) eqn: Henable.
    destruct (min_eid <=? eid) eqn: Hmin; [|reflexivity].
    destruct (eid <? max_eid) eqn: Hmax; [|reflexivity].
    rewrite Bool.andb_true_l.
    reflexivity.
    reflexivity.
  Qed.

  Lemma jops_of_non_static:
    forall i,
    i < ajtable_numRow - 1 ->
    ajtable_values enabled_cell i = 1 ->
    min_eid <= entry_id (ajtable_values entry_cell i) < max_eid ->
    ajtable_values static_bit_cell i = 0 ->
    jops_of i = 1.
  Proof.
    intros i Hi Henable Heid Hstatic.
    unfold jops_of.
    rewrite Henable, Hstatic.
    replace (i <? ajtable_numRow - 1) with true by lia.
    remember (entry_id (ajtable_values entry_cell i)) as eid.
    replace (min_eid <=? eid) with true by lia.
    replace (eid <? max_eid) with true by lia.
    rewrite Bool.andb_true_r.
    simpl.
    reflexivity.
  Qed.

  Lemma jops_of_nonnegative:
    forall i,
    0 <= jops_of i.
  Proof.
    intros i.
    unfold jops_of.
    remember (entry_id (ajtable_values entry_cell i)) as eid.
    destruct (i <? ajtable_numRow - 1) eqn: Hi_range; [|lia].
    destruct (ajtable_values enabled_cell i =? 1); [|lia].
    destruct (ajtable_values static_bit_cell i =? 1).
    - destruct (min_eid <=? eid); simpl; [|lia];
      destruct (eid <? max_eid); lia.
    - destruct (min_eid <=? eid); simpl; [|lia];
      destruct (eid <? max_eid); lia.
  Qed.

  Lemma jops_of_upper_bound:
    forall i,
    jops_of i <= 1.
  Proof.
    intros i.
    unfold jops_of.
    remember (entry_id (ajtable_values entry_cell i)) as eid.
    destruct (i <? ajtable_numRow - 1) eqn: Hi_range; [|lia].
    destruct (ajtable_values enabled_cell i =? 1); [|lia].
    destruct (min_eid <=? eid); destruct (eid <? max_eid); simpl; [|lia|lia|lia].
    destruct (ajtable_values static_bit_cell i =? 1) eqn: Hstatic;
    simpl in Hstatic;
    rewrite Hstatic;
    lia.
  Qed.

  Lemma jops_of_range:
    forall i,
    0 <= jops_of i <= 1.
  Proof.
    split.
    - apply jops_of_nonnegative.
    - apply jops_of_upper_bound.
  Qed.

  Lemma jops_of_0_implies:
    forall i,
    0 <= i ->
    jops_of i = 0 ->
    i >= ajtable_numRow - 1 \/
    ajtable_values enabled_cell i = 0 \/
    min_eid > entry_id (ajtable_values entry_cell i) \/
    max_eid <= entry_id (ajtable_values entry_cell i) \/
    ajtable_values static_bit_cell i = 1.
  Proof.
    intros i Hi Hjops.
    unfold jops_of in Hjops.
    remember (entry_id (ajtable_values entry_cell i)) as eid.
    destruct (i <? ajtable_numRow - 1) eqn: Hi_range.
    - right.
      destruct (ajtable_values enabled_cell i =? 1) eqn: Henable.
      + right.
        destruct (min_eid <=? eid) eqn: Hmin; [|lia]; right.
        destruct (eid <? max_eid) eqn: Hmax; [|lia]; right.
        destruct (ajtable_values static_bit_cell i =? 1) eqn: Hstatic.
        * lia.
        * simpl in Hjops; lia.
      + left.
        rewrite Z.eqb_neq in Henable.
        pose proof enable_is_bit i Hi.
        lia.
    - left.
      lia.
  Qed.

  Lemma jops_of_1_implies:
    forall i,
    0 <= i ->
    jops_of i = 1 ->
    i < ajtable_numRow - 1 /\
    ajtable_values enabled_cell i = 1 /\
    min_eid <= entry_id (ajtable_values entry_cell i) < max_eid /\
    ajtable_values static_bit_cell i = 0.
  Proof.
    intros i Hi Hjops.
    unfold jops_of in Hjops.
    remember (entry_id (ajtable_values entry_cell i)) as eid.
    repeat split.
    - destruct (i <? ajtable_numRow - 1) eqn: Hi_range; lia.
    - destruct (ajtable_values enabled_cell i =? 1) eqn: Henable; [lia|].
      destruct (i <? ajtable_numRow - 1) eqn: Hi_range; inversion Hjops.
    - destruct (i <? ajtable_numRow - 1); [|lia].
      destruct (ajtable_values enabled_cell i =? 1) eqn: Henable; [|lia].
      destruct (min_eid <=? eid) eqn: Hmin; [lia|].
      rewrite Bool.andb_false_l in Hjops.
      inversion Hjops.
    - destruct (i <? ajtable_numRow - 1); [|lia].
      destruct (ajtable_values enabled_cell i =? 1) eqn: Henable; [|lia].
      destruct (eid <? max_eid) eqn: Hmax; [lia|].
      rewrite Bool.andb_false_r in Hjops.
      inversion Hjops.
    - destruct (i <? ajtable_numRow - 1); [|lia].
      destruct (ajtable_values enabled_cell i =? 1) eqn: Henable; [|lia].
      destruct (ajtable_values static_bit_cell i =? 1) eqn: Hstatic; 
        simpl in Hjops.
      + destruct ((min_eid <=? eid) && (eid <? max_eid));
        inversion Hjops.
      + pose proof static_is_bit' i ltac:(lia) as Hstatic'.
        lia.
  Qed.

  Lemma gather_jops'_bound:
    forall i n,
    gather_jops' i n <= Z.of_nat n.
  Proof.
    intros i n.
    generalize i. clear i.
    induction n as [|n IHn]; intros i.
    - (* n = 0 *)
      rewrite gather_jops'_0.
      simpl.
      lia.
    - (* n = S n' *)
      rewrite gather_jops'_tail by lia.
      replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
      pose proof (jops_of_upper_bound (i + Z.of_nat n)) as Hbound.
      pose proof (IHn i) as Hind.
      lia.
  Qed.

  Lemma gather_jops_invalid_range:
    forall from to,
    from >= to ->
    gather_jops from to = 0.
  Proof.
    intros from to Hrange.
    unfold gather_jops.
    rewrite Coqlib.Z_to_nat_neg by lia.
    simpl.
    destruct (from <? ajtable_numRow - 1) eqn: Hfrom; reflexivity.
  Qed.

  Lemma gather_jops_nonnegative : forall i j,
    0 <= gather_jops i j.
  Proof.
    intros i j.
    assert (j <= i \/ i < j) as [Hle | Hgt] by lia.
    - pose proof (gather_jops_invalid_range i j ltac:(lia)) as Hinvalid.
      rewrite Hinvalid.
      lia.
    - pose proof (gather_jops'_unwrap i j) as Hunwrap.
      rewrite Hunwrap.
      remember (Z.to_nat (j - i)) as n.
      generalize n i. clear i j n Hgt Hunwrap Heqn.
      induction n as [|n IHn]; intros i.
      + (* n = 0 *)
        simpl.
        destruct (i <? ajtable_numRow - 1) eqn: Hi_range; [|lia].
        lia.
      + (* n = S n' *)
        rewrite gather_jops'_tail by lia.
        pose proof (jops_of_nonnegative (i + Z.of_nat n)) as Hnonneg.
        generalize (IHn i). intros Hnext.
        lia.
  Qed.

  Lemma gather_jops_append : forall i j k,
      i <= j <= k ->
      gather_jops i k = (gather_jops i j) + gather_jops j k.
  Proof.
    intros i j k Hjk.
    pose proof (Z_segment_as_nat i j k Hjk) as (m & n & Hj & Hk).
    rewrite Hj, Hk.
    rewrite !gather_jops_unwrap by lia.
    rewrite <- Z.add_assoc.
    rewrite <- Nat2Z.inj_add.
    rewrite gather_jops_unwrap by lia.
    generalize i m. clear i m j k Hjk Hj Hk.
    induction n as [|n IHn]; intros i m.
    - (* n = 0 *)
      rewrite gather_jops'_0.
      rewrite Z.add_0_r. rewrite Nat.add_0_r.
      reflexivity.
    - (* n = S n' *)
      replace (m + S n)%nat with (S (m + n))%nat by lia.
      rewrite !gather_jops'_tail by lia.
      rewrite IHn by lia.
      rewrite Nat2Z.inj_add.
      rewrite !Z.add_assoc.
      reflexivity.
  Qed.

  Lemma gather_jops_bound:
    forall i j,
      i <= j ->
      gather_jops i j <= (j - i).
  Proof.
    intros i j Hij.
    rewrite gather_jops'_unwrap by lia.
    remember (Z.to_nat (j - i)) as n.
    replace ((j - i)) with (Z.of_nat (Z.to_nat (j - i))) by (apply Z2Nat.id; lia).
    rewrite <- Heqn.
    apply gather_jops'_bound.
  Qed.

  Lemma invalid_eid_range: forall eid,
    min_eid >= max_eid ->
    min_eid <= eid < max_eid ->
    False.
  Proof.
    intros until eid. intros Hrange Hinvalid.
    lia.
  Qed.

  Lemma invalid_eid_range_bool: forall eid,
    min_eid >= max_eid ->
    (min_eid <=? eid) && (eid <? max_eid) = false.
  Proof.
    intros until eid. intros Hrange.
    destruct (min_eid <=? eid) eqn: Hmin;
    destruct (eid <? max_eid) eqn: Hmax.
    - lia.
    - rewrite andb_false_r. reflexivity.
    - rewrite andb_false_l. reflexivity.
    - lia.
  Qed.

  Lemma jops_invalid_eid: forall i j,
    min_eid >= max_eid ->
    gather_jops i j = 0.
  Proof.
    intros until j. intros Hrange.
    unfold gather_jops. remember (Z.to_nat (j - i)) as n.
    generalize n i. clear i j n Heqn.
    induction n as [|n IHn]; intros i.
    - rewrite gather_jops'_0.
      reflexivity.
    - rewrite gather_jops'_tail by lia.
      rewrite IHn by lia.
      rewrite Z.add_0_l.
      unfold jops_of.
      rewrite invalid_eid_range_bool by lia.
      destruct (i + Z.of_nat n <? ajtable_numRow - 1); [|reflexivity].
      destruct (ajtable_values enabled_cell (i + Z.of_nat n) =? 1); reflexivity.
  Qed.

  End gather.

  Definition rest_of (i: Z) :=
    if i <? ajtable_numRow - 1 then
      if ajtable_values enabled_cell i =? 1
      then
        encode_jops 1 1 - ajtable_values static_bit_cell i
      else 0
    else 0.

  Fixpoint gather_rest' (n: nat) :=
    match n with
    | O => 0
    | S O => 0
    | S n' =>
      rest_of (ajtable_numRow - Z.of_nat (S n')) + gather_rest' n'
    end.

  Definition gather_rest (i: Z) :=
    gather_rest' (Z.to_nat (ajtable_numRow - i)).

  Definition call_of (i: Z) :=
    if i <? ajtable_numRow - 1 then
      if ajtable_values enabled_cell i =? 1
      then
        1 - ajtable_values static_bit_cell i
      else 0
    else 0.

  Fixpoint gather_call_of' (n: nat) :=
    match n with
    | O => 0
    | S O => 0
    | S n' => call_of (ajtable_numRow - Z.of_nat n) + gather_call_of' n'
    end.

  Definition gather_call_of (i: Z) :=
    gather_call_of' (Z.to_nat (ajtable_numRow - i)).

  Lemma jops_split_range : forall min_eid max_eid a b c,
    a <= b <= c ->
    gather_jops min_eid max_eid a c =
      gather_jops min_eid max_eid a b + gather_jops min_eid max_eid b c.
  Proof.
    intros until c. intros Hrange.
    apply gather_jops_append; lia.
  Qed.

  Lemma jops_of_split_eid: forall min_eid mid_eid max_eid i,
    min_eid <= mid_eid <= max_eid ->
    jops_of min_eid mid_eid i + jops_of mid_eid max_eid i = jops_of min_eid max_eid i.
  Proof.
    intros until i. intros Hrange.
    unfold jops_of.
    remember (entry_id (ajtable_values entry_cell i)) as eid.
    destruct (i <? ajtable_numRow - 1) eqn: Hi_range; [|reflexivity].
    destruct (ajtable_values enabled_cell i =? 1) eqn: Henable; [|reflexivity].
    assert (eid < mid_eid \/ mid_eid <= eid) as [Hlow | Hhigh] by lia.
    - assert (eid <? mid_eid = true) as Hlow' by lia.
      assert (mid_eid <=? eid = false) as Hlow'' by lia.
      destruct (min_eid <=? eid) eqn: Hmin;
      destruct (eid <? max_eid) eqn: Hmax;
      destruct (ajtable_values static_bit_cell i =? 1) eqn: Hstatic;
      try rewrite !Hlow', !Hlow''; simpl; try lia.
    - assert (mid_eid <=? eid = true) as Hhigh' by lia.
      assert (eid <? mid_eid = false) as Hhigh'' by lia.
      destruct (min_eid <=? eid) eqn: Hmin;
      destruct (eid <? max_eid) eqn: Hmax;
      destruct (ajtable_values static_bit_cell i =? 1) eqn: Hstatic;
      try rewrite !Hhigh', !Hhigh''; simpl; try lia.
  Qed.

  Lemma jops_split_eid': forall min_eid mid_eid max_eid i n,
    min_eid <= mid_eid <= max_eid ->
     gather_jops' min_eid mid_eid i n + gather_jops' mid_eid max_eid i n = gather_jops' min_eid max_eid i n.
  Proof.
    intros until n. intros Hrange.
    induction n as [|n IHn].
    - rewrite !gather_jops'_0. reflexivity.
    - rewrite !gather_jops'_tail by lia.
      rewrite <- IHn.
      rewrite <- (jops_of_split_eid min_eid mid_eid max_eid ((i + Z.of_nat n)) Hrange).
      rewrite !Z.add_assoc.
      lia.
  Qed.

  Lemma jops_split_eid: forall min_eid mid_eid max_eid i j,
    min_eid <= mid_eid <= max_eid ->
    gather_jops min_eid mid_eid i j + gather_jops mid_eid max_eid i j = gather_jops min_eid max_eid i j.
  Proof.
    intros until j. intros Hrange.
    assert (j < i \/ i <= j)  as [Hinvalid | Hvalid] by lia.
    - rewrite !gather_jops_invalid_range by lia.
      lia.
    - assert (exists n, j = i + Z.of_nat n) as [n Hn].
      {
        exists (Z.to_nat (j - i)).
        lia.
      }
      rewrite Hn.
      rewrite !gather_jops_unwrap by lia.
      rewrite jops_split_eid' by lia.
      reflexivity.
  Qed.

  Lemma gather_jops_le_numRows:
    forall min_eid max_eid i j,
      i <= j <= ajtable_numRow ->
      gather_jops min_eid max_eid i j <= gather_jops min_eid max_eid i ajtable_numRow.
  Proof.
    intros until j. intros Hrange.
    pose proof (gather_jops_append min_eid max_eid i j ajtable_numRow ltac:(lia)) as Happend.
    pose proof (gather_jops_nonnegative min_eid max_eid j ajtable_numRow) as Hnonneg.
    rewrite Happend.
    lia.
  Qed.

  (**
   * Rest and Gather rest
   *)
  Lemma gather_rest_terminates:
    gather_rest (ajtable_numRow - 1) = 0.
  Proof.
    unfold gather_rest.
    replace (Z.to_nat (ajtable_numRow - (ajtable_numRow - 1))) with 1%nat by lia.
    simpl.
    reflexivity.
  Qed.
  
  Lemma gather_rest_cons':
    forall n,
      gather_rest' (S n) = rest_of (ajtable_numRow - Z.of_nat (S n)) + gather_rest' n.
  Proof.
    intros n.
    destruct n.
    - replace (Z.of_nat 1) with 1 by lia.
      simpl.
      unfold rest_of.
      assert (ajtable_numRow - 1 <? ajtable_numRow - 1 = false) as Hinvalid by lia.
      rewrite Hinvalid.
      lia.
    - simpl.
      reflexivity.
  Qed.

  Lemma gather_rest_cons:
    forall i,
      i < ajtable_numRow ->
      gather_rest i = rest_of i + gather_rest (i + 1).
  Proof.
    intros i Hi.
    unfold gather_rest.
    remember ajtable_numRow as N.
    remember (Z.to_nat (N - (i + 1))) as n.
    assert (0 <= n)%nat as Hn by lia.
    assert (Z.to_nat (N - i) = S n) as Hsn.
    {
      rewrite Heqn.
      replace (N - (i + 1)) with (N - i - 1) by lia.
      replace (Z.to_nat (N - i - 1)) with (Z.to_nat (N - i) - 1)%nat by lia.
      remember (Z.to_nat (N - i)) as n'.
      destruct n'; [lia|].
      replace (S n' - 1)%nat with n' by lia.
      reflexivity.
    }
    assert (i = N - Z.of_nat (S n)) as Hi'.
    {
      rewrite <- Hsn.
      rewrite Z2Nat.id by lia.
      lia.
    }
    rewrite Hsn.
    rewrite Hi'.
    rewrite HeqN.
    apply gather_rest_cons'.
  Qed.

  Lemma ajtable_rest_jops_terminates:
    ajtable_values rest_cell (ajtable_numRow - 1) = 0.
  Proof.
    unfold ajtable_numRow.
    unfold ajtable_values.
    replace (JtableOffsetMax * (jtable_numRow / JtableOffsetMax - 1)) with
      (JtableOffsetMax * (jtable_numRow / JtableOffsetMax) - JtableOffsetMax) by
      lia.
    rewrite <- Z_div_exact_2.
    - apply rest_jops_terminates.
    - pose proof jtable_offset_max_pos.
      lia.
    - apply numRow_parity.
  Qed.

  Lemma gather_rest_is_rest_cell:
    forall i,
      0 <= i < ajtable_numRow ->
      gather_rest i = ajtable_values rest_cell i.
  Proof.
    intros i Hi.
    remember (Z.to_nat (ajtable_numRow - i)) as n.
    assert (i = ajtable_numRow - Z.of_nat n) as Hn.
    {
      rewrite Heqn.
      rewrite Z2Nat.id by lia.
      lia.
    }
    subst i.
    generalize n Hi. clear n Hi Heqn.
    induction n as [|n IHn]; intros Hi.
    - (* n = 0 *)
      simpl in Hi.
      rewrite !Z.sub_0_r in Hi.
      lia.
    - (* S n' *)
      assert (n = 0 \/ 0 < n)%nat as [Hn0 | Hnpos] by lia.
      + (* n = 0 *)
        rewrite Hn0. replace (Z.of_nat 1) with 1 by lia.
        rewrite ajtable_rest_jops_terminates.
        rewrite gather_rest_terminates.
        reflexivity.
      + (* 0 < n *)
        replace (ajtable_numRow - Z.of_nat (S n)) with (ajtable_numRow - Z.of_nat n - 1) by lia.
        remember (ajtable_numRow - Z.of_nat n) as i.
        destruct (ajtable_values enabled_cell (i - 1) =? 1) eqn: Henable.
        + (* enable *)
          rewrite rest_jops_change_enabled by lia.
          rewrite gather_rest_cons by lia.
          replace (i - 1 + 1) with i by lia.
          unfold rest_of.
          assert (i - 1 <? ajtable_numRow - 1 = true) as Hvalid by lia.
          rewrite Hvalid.
          rewrite Henable.
          rewrite IHn.
          + lia.
          + rewrite Heqi.
            split.
            * lia.
            * lia.
        + (* disable *)
          assert (ajtable_values enabled_cell (i - 1) = 0) as Hdisable.
          {
            apply Z.eqb_neq in Henable.
            pose proof (enable_is_bit (i - 1) ltac:(lia)) as [He0 | He1].
            + lia.
            + lia.
          }
          rewrite rest_jops_change_disabled by lia.
          rewrite gather_rest_cons by lia.
          replace (i - 1 + 1) with i by lia.
          unfold rest_of.
          assert (i - 1 <? ajtable_numRow - 1 = true) as Hvalid by lia.
          rewrite Hvalid.
          rewrite Hdisable.
          assert (0 =? 1 = false) as H01 by lia.
          rewrite H01.
          rewrite Z.add_0_l.
          rewrite IHn.
          * lia.
          * lia.
  Qed.

  Lemma call_of_encoded_jops_is_call_of:
    forall i,
      0 <= i ->
      call_of_encoded_jops (rest_of i) = call_of i.
  Proof.
    intros i Hi.
    unfold call_of, call_of_encoded_jops, rest_of.
    pose proof (enable_is_bit i ltac:(lia)) as Henable.
    pose proof (static_is_bit' i) as Hstatic.
    destruct (i <? ajtable_numRow - 1) eqn: Hvalid;
    destruct (ajtable_values enabled_cell i =? 1) eqn: Henable';
    destruct (0 =? 1 - ajtable_values static_bit_cell i) eqn: Hstatic';
    try (simpl; reflexivity).
    - assert (ajtable_values static_bit_cell i = 1) as Hstatic'' by lia.
      rewrite Hstatic''.
      simpl.
      rewrite encode_jops_sub_1.
      apply Z_land_shiftl_ones_0; unfold JOPS_SEPARATE; lia.
    - assert (ajtable_values static_bit_cell i = 0) as Hstatic'' by lia.
      rewrite Hstatic''.
      rewrite !Z.sub_0_r.
      rewrite encode_jops_1.
      reflexivity.
  Qed.

  Lemma rest_of_nonneg:
    forall i,
      0 <= i ->
      0 <= rest_of i.
  Proof.
    intros i Hi.
    unfold rest_of.
    destruct (i <? ajtable_numRow - 1) eqn: Hvalid;
    destruct (ajtable_values enabled_cell i =? 1) eqn: Henable;
      try reflexivity;
      try apply encode_jops_sub_static_nonneg; lia.
  Qed.

  Lemma gather_rest'_nonneg:
    forall n,
      Z.of_nat n <= ajtable_numRow ->
      0 <= gather_rest' n.
  Proof.
    intros n Hn.
    induction n as [|n IHn].
    - simpl. lia.
    - rewrite gather_rest_cons'.
      assert (Z.of_nat n + 1 <= ajtable_numRow) as Hn' by lia.
      replace (ajtable_numRow - Z.of_nat (S n)) with (ajtable_numRow - Z.of_nat n - 1) by lia.
      assert (0 <= ajtable_numRow - Z.of_nat n - 1) as Hn'' by lia.
      pose proof (rest_of_nonneg (ajtable_numRow - Z.of_nat n - 1) Hn'') as Hnonneg.
      assert (Z.of_nat n <= ajtable_numRow) as Hn''' by lia.
      lia.
  Qed.

  Lemma rest_of_upper_bound:
    forall i,
      0 <= i ->
      rest_of i <= encode_jops 1 1.
  Proof.
    intros i Hi.
    unfold rest_of.
    destruct (i <? ajtable_numRow - 1) eqn: Hvalid;
    destruct (ajtable_values enabled_cell i =? 1) eqn: Henable;
      try apply encode_jops_1_nonneg.
    pose proof (static_is_bit' i Hi) as [Hstatic | Hstatic]; rewrite Hstatic.
    - rewrite Z.sub_0_r.
      lia.
    - lia.
  Qed.

  Lemma gather_rest'_upper_bound: forall n,
    Z.of_nat n <= ajtable_numRow ->
    gather_rest' n <= 
      encode_jops (Z.of_nat n) (Z.of_nat n). 
  Proof.
    intros n Hn.
    pose proof ajtable_numRow_upper_bound as Hbound.
    pose proof ajtable_numRow_nonneg as Hnonneg.
    induction n as [|n IHn].
    - simpl.
      rewrite encode_jops_0.
      reflexivity.
    - specialize (IHn ltac:(lia)).
      rewrite gather_rest_cons'.
      replace (ajtable_numRow - Z.of_nat (S n)) with
        (ajtable_numRow - Z.of_nat n - 1) by lia.
      pose proof (rest_of_upper_bound (ajtable_numRow - Z.of_nat n - 1) 
        ltac:(lia)) as Hbound'.
      replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
      rewrite <- encode_jops_add by lia.
      lia.
  Qed.

  Lemma gather_rest_upper_bound:
    forall i,
      0 <= i < ajtable_numRow ->
      gather_rest i <= encode_jops (ajtable_numRow - i) (ajtable_numRow - i).
  Proof.
    intros i Hi.
    unfold gather_rest.
    remember (Z.to_nat (ajtable_numRow - i)) as n.
    assert (ajtable_numRow - i = Z.of_nat n) as Hn by lia.
    rewrite Hn.
    apply gather_rest'_upper_bound.
    lia.
  Qed.

  Lemma gather_rest_0_upper_bound:
    gather_rest 0 < 2 ^ (2 * JOPS_SEPARATE).
  Proof.
    pose proof jops_separate_pos as Hsep.
    pose proof ajtable_numRow_upper_bound as Hbound.
    pose proof ajtable_numRow_nonneg as Hnonneg.
    assert (ajtable_numRow = 0 \/ 0 < ajtable_numRow) as [H0 | Hpos] by lia.
    - unfold gather_rest.
      rewrite H0.
      simpl.
      lia.
    - pose proof (gather_rest_upper_bound 0 ltac:(lia)) as Hbound'.
      rewrite !Z.sub_0_r in Hbound'.
      pose proof encode_jops_of_upper_bound as Hjops.
      lia.
  Qed.

  Lemma gather_rest_nonneg:
    forall i,
      0 <= i < ajtable_numRow ->
      0 <= gather_rest i.
  Proof.
    intros i Hi.
    unfold gather_rest.
    remember (Z.to_nat (ajtable_numRow - i)) as n.
    assert (0 <= ajtable_numRow - i) as Hn by lia.
    assert (Z.of_nat n <= ajtable_numRow) as Hn'.
    {
      rewrite Heqn.
      rewrite Z2Nat.id by lia.
      lia.
    }
    apply gather_rest'_nonneg; lia.
  Qed.

  Lemma rest_of_cases:
    forall i,
    0 <= i ->
    rest_of i = 0 \/
    rest_of i = encode_jops 1 0 \/
    rest_of i = encode_jops 1 1.
  Proof.
    intros i Hi.
    unfold rest_of.
    destruct (i <? ajtable_numRow - 1) eqn: Hvalid; [|left; lia];
    destruct (ajtable_values enabled_cell i =? 1) eqn: Henable; [|left; lia];
    pose proof (static_is_bit' i Hi) as [Hstatic | Hstatic]; rewrite Hstatic.
    - right; right.
      rewrite Z.sub_0_r.
      reflexivity.
    - right; left.
      rewrite encode_jops_sub_1.
      rewrite jops_encode_unwrap by (unfold JOPS_SEPARATE; lia).
      rewrite Z.lor_0_r.
      reflexivity.
  Qed.

  (**
   * Call of and Gather call
   *)
  Lemma call_of_encoded_jops_add:
    forall e1 e2,
      0 <= e1 ->
      0 <= e2 ->
      e1 mod 2 ^ JOPS_SEPARATE + e2 mod 2 ^ JOPS_SEPARATE < 2 ^ JOPS_SEPARATE ->
      call_of_encoded_jops (e1 + e2) = call_of_encoded_jops e1 + call_of_encoded_jops e2.
  Proof.
    intros e1 e2 He1 He2 Hbound.
    unfold call_of_encoded_jops.
    pose proof jops_separate_pos as Hsep.
    rewrite !Z.land_ones by lia.
    rewrite Z.add_mod by lia.
    rewrite Z.mod_small.
    - reflexivity.
    - split; [|lia].
      apply Z.add_nonneg_nonneg;
      apply Z.mod_pos_bound; lia.
  Qed.

  Lemma call_of_rest_upper_bound:
    forall i,
      0 <= i ->
      call_of_encoded_jops (rest_of i) <= 1.
  Proof.
    intros i Hi.
    rewrite call_of_encoded_jops_is_call_of by lia.
    unfold call_of.
    destruct (i <? ajtable_numRow - 1) eqn: Hvalid; [|lia];
    destruct (ajtable_values enabled_cell i =? 1) eqn: Henable; [|lia].
    pose proof (static_is_bit' i Hi) as [Hstatic | Hstatic]; rewrite Hstatic;
    lia.
  Qed.

  Lemma call_of_encoded_jops_is_mod:
    forall enc,
      call_of_encoded_jops enc = enc mod 2 ^ JOPS_SEPARATE.
  Proof.
    intros enc.
    unfold call_of_encoded_jops.
    pose proof jops_separate_pos as Hsep.
    rewrite Z.land_ones by lia.
    reflexivity.
  Qed.

  Lemma call_of_gather_rest'_upper_bound:
    forall n,
      Z.of_nat n <= ajtable_numRow ->
      call_of_encoded_jops (gather_rest' n) <= Z.of_nat n.
  Proof.
    intros n Hn.
    induction n as [|n IHn].
    - (* n = 0 *)
      simpl. reflexivity.
    - (* S n' *)
      specialize (IHn ltac:(lia)).
      rewrite gather_rest_cons'.
      replace (ajtable_numRow - Z.of_nat (S n)) with (ajtable_numRow - Z.of_nat n - 1) by lia.
      rewrite call_of_encoded_jops_add.
      + remember (ajtable_numRow - Z.of_nat n) as i.
        pose proof (call_of_rest_upper_bound (i - 1) ltac:(lia)) as Hrest.
        replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
        lia.
      + apply rest_of_nonneg.
        lia.
      + apply gather_rest'_nonneg.
        lia.
      + remember (ajtable_numRow - Z.of_nat n) as i.
        assert (0 <= i) as Hi by lia.
        assert (0 <= i - 1) as Hi' by lia.
        pose proof (rest_of_upper_bound (i - 1) Hi') as Hrest.
        pose proof (call_of_rest_upper_bound (i - 1) Hi') as Hcall_rest.
        rewrite <- call_of_encoded_jops_is_mod.
        rewrite <- call_of_encoded_jops_is_mod.
        pose proof (ajtable_numRow_upper_bound) as Hbound.
        lia.
  Qed.

  Lemma call_of_gather_rest_upper_bound:
    forall i,
      0 <= i < ajtable_numRow ->
      call_of_encoded_jops (gather_rest i) <= (ajtable_numRow - i).
  Proof.
    intros i Hi.
    unfold gather_rest.
    remember (Z.to_nat (ajtable_numRow - i)) as n.
    assert (ajtable_numRow - i = Z.of_nat n) as Hn by lia.
    rewrite Hn.
    apply call_of_gather_rest'_upper_bound.
    lia.
  Qed.

  Lemma call_of_gather_rest'_nonneg:
    forall n,
      Z.of_nat n <= ajtable_numRow ->
      0 <= call_of_encoded_jops (gather_rest' n).
  Proof.
    intros n Hn.
    pose proof gather_rest'_nonneg n Hn as Hrest.
    unfold call_of_encoded_jops.
    apply Z.land_nonneg.
    left. assumption.
  Qed.

  Lemma call_of_gather_rest_nonneg:
    forall i,
      0 <= i < ajtable_numRow ->
      0 <= call_of_encoded_jops (gather_rest i).
  Proof.
    intros i Hi.
    unfold gather_rest.
    remember (Z.to_nat (ajtable_numRow - i)) as n.
    assert (ajtable_numRow - i = Z.of_nat n) as Hn by lia.
    apply call_of_gather_rest'_nonneg.
    lia.
  Qed.

  Lemma call_of_gather_rest_range:
    forall i,
      0 <= i < ajtable_numRow ->
      0 <= call_of_encoded_jops (gather_rest i) <= ajtable_numRow.
  Proof.
    intros i Hi.
    split; [apply call_of_gather_rest_nonneg; lia|].
    pose proof call_of_gather_rest_upper_bound i Hi as Hbound.
    lia.
  Qed.

  Lemma call_of_encoded_rest_cons':
    forall n,
      Z.of_nat n < ajtable_numRow ->
      call_of_encoded_jops (gather_rest' (S n)) = call_of (ajtable_numRow - Z.of_nat (S n)) + call_of_encoded_jops (gather_rest' n).
  Proof.
    intros n Hn.
    destruct n.
    - replace (Z.of_nat 1) with 1 by lia.
      simpl.
      unfold call_of.
      replace (ajtable_numRow - 1 <? ajtable_numRow - 1) with false by lia.
      reflexivity.
    - remember (S n) as n'.
      assert (0 < n')%nat as Hnpos by lia.
      pose proof (gather_rest'_upper_bound (S n') ltac:(lia)) as Hbound.
      pose proof (call_of_gather_rest_range (Z.of_nat (S n'))) as Hrange.
      assert (Z.of_nat (S n') = ajtable_numRow \/ Z.of_nat (S n') < ajtable_numRow)
        as [Hn' | Hn'] by lia.
      + (* S n' = N *)
        assert (ajtable_numRow - Z.of_nat (S n') = 0) as Hn'' by lia.
        rewrite gather_rest_cons'.
        rewrite Hn''.
        assert (Z.of_nat n' = ajtable_numRow - 1) as Hn''' by lia.
        assert (n' = Z.to_nat ajtable_numRow - 1)%nat as Hn'eq by lia.
        pose proof jops_separate_pos as Hsep.
        pose proof rest_of_nonneg 0 ltac:(lia) as Hnonneg.
        pose proof gather_rest'_nonneg n' ltac:(lia) as Hnonneg'.
        rewrite call_of_encoded_jops_add; [|lia|lia|].
        * rewrite call_of_encoded_jops_is_call_of by lia.
          reflexivity.
        * pose proof call_of_rest_upper_bound 0 ltac:(lia) as Hbound'.
          rewrite <- !call_of_encoded_jops_is_mod.
          pose proof call_of_gather_rest'_upper_bound n' ltac:(lia) as Hbound''.
          assert (Z.of_nat n' < ajtable_numRow) as Hn'bound by lia.
          pose proof ajtable_numRow_upper_bound as Hjops.
          lia.
      + (* S n' < N *)
        specialize (Hrange ltac:(lia)).
        pose proof (gather_rest_cons' n') as Hcons.
        rewrite Hcons.
        replace (ajtable_numRow - Z.of_nat (S n')) with (ajtable_numRow - Z.of_nat n' - 1) by lia.
        remember (ajtable_numRow - Z.of_nat n') as i'.
        assert (0 <= i') as Hi' by lia.
        assert (0 <= i' - 1) as Hi'' by lia.
        pose proof (rest_of_nonneg (i' - 1) Hi'') as Hnonneg.
        pose proof (gather_rest'_nonneg n' ltac:(lia)) as Hnonneg'.
        pose proof jops_separate_pos as Hsep.
        rewrite call_of_encoded_jops_add; [|lia|lia|].
        + rewrite call_of_encoded_jops_is_call_of by lia.
          reflexivity.
        + assert (ajtable_numRow - Z.of_nat (S n') = i' - 1) as Hi''' by lia.
          rewrite Hi''' in Hcons.
          assert (rest_of (i' - 1) mod 2 ^ JOPS_SEPARATE <= 1) as Hrest.
          {
            pose proof (call_of_rest_upper_bound (i' - 1) Hi'') as Hrest.
            rewrite <- call_of_encoded_jops_is_mod.
            assumption.
          }
          assert (gather_rest' n' mod 2 ^ JOPS_SEPARATE <= Z.of_nat n') as Hrestn'.
          {
            pose proof (call_of_gather_rest'_upper_bound n' ltac:(lia)) as Hbound'.
            unfold call_of_encoded_jops in Hbound'.
            rewrite Z.land_ones in Hbound' by lia.
            lia.
          }
          pose proof ajtable_numRow_upper_bound as Hjops.
          lia.
  Qed.

  Lemma call_of_0:
      forall i,
      ajtable_numRow - 1 <= i ->
      call_of i = 0.
  Proof.
    intros i Hi.
    unfold call_of.
    assert (i <? ajtable_numRow - 1 = false) as Hinvalid by lia.
    rewrite Hinvalid.
    reflexivity.
  Qed.

  Lemma jops_of_le_call_of_core:
    forall i,
      0 <= i ->
      (if ajtable_values static_bit_cell i =? 1 then 0 else 1) <=
      1 - ajtable_values static_bit_cell i.
  Proof.
    intros i Hi.
    destruct (ajtable_values static_bit_cell i =? 1) eqn: Hstatic.
    - apply Z.eqb_eq in Hstatic. rewrite Hstatic. lia.
    - apply Z.eqb_neq in Hstatic.
      pose proof static_is_bit' i Hi as Hstatic'.
      lia.
  Qed.

  Lemma gather_call_of'_cons:
    forall n,
    gather_call_of' (S n) = call_of (ajtable_numRow - Z.of_nat (S n)) + gather_call_of' n.
  Proof.
    intros n.
    destruct n.
    - simpl. rewrite call_of_0 by lia. lia.
    - remember (S n) as n'.
      assert (0 < n')%nat as Hnpos by lia.
      simpl.
      rewrite Heqn'.
      reflexivity.
  Qed.
  
  Lemma gather_call_of'_is_call_of_encoded_gather_rest':
    forall n,
      Z.of_nat n <= ajtable_numRow ->
      gather_call_of' n = call_of_encoded_jops (gather_rest' n).
  Proof.
    intros n Hn.
    induction n as [|n IHn].
    - simpl. reflexivity.
    - destruct n.
      + simpl. reflexivity.
      + remember (S n) as n'.
        assert (0 < n')%nat as Hnpos by lia.
        rewrite call_of_encoded_rest_cons' by lia.
        rewrite gather_call_of'_cons.
        assert (Z.of_nat n' <= ajtable_numRow) as Hn' by lia.
        specialize (IHn Hn').
        rewrite <- IHn.
        reflexivity.
  Qed.

  Lemma gather_call_of_is_call_of_encoded_gather_rest:
    forall i,
      0 <= i < ajtable_numRow ->
      gather_call_of i = call_of_encoded_jops (gather_rest i).
  Proof.
    intros i Hi.
    unfold gather_call_of.
    remember (Z.to_nat (ajtable_numRow - i)) as n.
    assert (ajtable_numRow - i = Z.of_nat n) as Hn by lia.
    unfold gather_rest.
    rewrite Hn.
    rewrite Nat2Z.id by lia.
    apply gather_call_of'_is_call_of_encoded_gather_rest'.
    lia.
  Qed.

  Lemma jops_of_le_call_of:
    forall min_eid max_eid i,
      0 <= i < ajtable_numRow - 1 ->
      jops_of min_eid max_eid i <= call_of i.
  Proof.
    intros min_eid max_eid i Hi.
    unfold jops_of, call_of.
    assert (i <? ajtable_numRow - 1 = true) as Hvalid by lia.
    rewrite Hvalid.
    destruct (ajtable_values enabled_cell i =? 1) eqn: Henable; [|lia].
    remember (entry_id (ajtable_values entry_cell i)) as eid.
    pose proof static_is_bit' i ltac:(lia) as Hstatic.
    assert (eid < min_eid \/ min_eid <= eid < max_eid \/ max_eid <= eid) 
      as [Hmin | [Hmid | Hmax]] 
      by lia.
    - assert (min_eid <=? eid = false) as Hr by lia.
      rewrite Hr.
      rewrite Bool.andb_false_l.
      lia.
    - assert (min_eid <=? eid = true) as Hr by lia.
      assert (eid <? max_eid = true) as Hr' by lia.
      rewrite Hr, Hr'.
      rewrite Bool.andb_true_l.
      apply jops_of_le_call_of_core.
      lia.
    - assert (eid <? max_eid = false) as Hr by lia.
      rewrite Hr.
      rewrite Bool.andb_false_r.
      lia.
  Qed.

  Lemma gather_jops'_le_gather_call_of':
    forall min_eid max_eid (n: nat),
      0 < Z.of_nat n <= ajtable_numRow ->
      gather_jops' min_eid max_eid (ajtable_numRow - Z.of_nat n) n
      <= gather_call_of' n.
  Proof.
    intros min_eid max_eid n Hn.
    induction n as [|n IHn].
    - rewrite gather_jops'_0.
      simpl.
      reflexivity.
    - assert (n = 0 \/ 0 < n)%nat as [Hn0 | Hnpos] by lia.
      + rewrite Hn0.
        rewrite gather_jops'_1.
        replace (Z.of_nat 1) with 1 by lia.
        rewrite jops_of_last.
        simpl.
        reflexivity.
      + assert (0 < Z.of_nat n <= ajtable_numRow) as Hn' by lia.
        specialize (IHn Hn').
        rewrite gather_call_of'_cons by lia.
        rewrite gather_jops'_head by lia.
        remember (ajtable_numRow - Z.of_nat n) as i.
        assert (ajtable_numRow - Z.of_nat (S n) = i - 1) as Hisub1 by lia.
        rewrite Hisub1.
        replace (i - 1 + 1) with i by lia.
        assert (jops_of min_eid max_eid (i - 1) <= call_of (i - 1)) as Hbound_i.
        {
          apply jops_of_le_call_of.
          lia.
        }
        lia.
  Qed.

  Lemma gather_jops'_le_gather_call_of'_0:
    forall min_eid max_eid,
      gather_jops' min_eid max_eid (ajtable_numRow) 0
      <= gather_call_of' 0.
  Proof.
    intros.
    simpl.
    replace (ajtable_numRow <? ajtable_numRow - 1) with false by lia.
    reflexivity.
  Qed.

  Lemma gather_jops'_le_gather_call_of'':
    forall min_eid max_eid (n: nat),
      0 <= Z.of_nat n <= ajtable_numRow ->
      gather_jops' min_eid max_eid (ajtable_numRow - Z.of_nat n) n
      <= gather_call_of' n.
  Proof.
    intros min_eid max_eid n Hn.
    assert (n = 0 \/ 0 < n)%nat as [Hn0 | Hnpos] by lia.
    - rewrite Hn0.
      replace (Z.of_nat 0) with 0 by lia.
      rewrite Z.sub_0_r.
      apply gather_jops'_le_gather_call_of'_0.
    - apply gather_jops'_le_gather_call_of'.
      lia.
  Qed.

  Lemma gather_jops_relate_gather_call_of:
    forall min_eid max_eid i,
      0 <= i <= ajtable_numRow ->
      gather_jops min_eid max_eid i ajtable_numRow <= gather_call_of i.
  Proof.
    intros min_eid max_eid i Hi.
    unfold gather_jops, gather_call_of.
    remember (Z.to_nat (ajtable_numRow - i)) as n.
    assert (i = ajtable_numRow - Z.of_nat n) as Hn by lia.
    rewrite Hn.
    apply gather_jops'_le_gather_call_of''.
    lia.
  Qed.

  Lemma rest_jops_bound' : forall min_eid max_eid i,
    0 <= i < ajtable_numRow ->
    gather_jops min_eid max_eid i ajtable_numRow
      <= call_of_encoded_jops (ajtable_values rest_cell i).
  Proof.
    intros until i. intros Hi.
    rewrite <- gather_rest_is_rest_cell by lia.
    rewrite <- gather_call_of_is_call_of_encoded_gather_rest by lia.
    apply gather_jops_relate_gather_call_of.
    lia.
  Qed.

  (* The right side of the jops column is meant to count call instructions,
     and we extract it with the Z.land. 
     In order to show that the counter doesn't overflow, we need to know that the number of
     rows are less than the common range. *)
  Lemma rest_jops_bound : forall min_eid max_eid i j,
    0 <= i ->
    i <= j < ajtable_numRow ->
    gather_jops min_eid max_eid i j
      <=  Z.land (ajtable_values rest_cell i) (Z.ones JOPS_SEPARATE).
  Proof.
    intros until j. intros Hi Hij.
    pose proof gather_jops_le_numRows min_eid max_eid i j ltac:(lia) as Hmono.
    assert (call_of_encoded_jops (ajtable_values rest_cell i) = 
      Z.land (ajtable_values rest_cell i) (Z.ones JOPS_SEPARATE)) 
      as Hrest
      by (unfold call_of_encoded_jops; reflexivity).
    rewrite <- Hrest.
    pose proof rest_jops_bound' min_eid max_eid i ltac:(lia) as Hbound.
    lia.
  Qed.

  (* Number of call jops at a particular id. *)
  Definition jops_at eid  := 
    gather_jops eid (eid+1) 0 ajtable_numRow.

  (* Number of call jops that happen in a particular range of ids. *)
  Definition cum_jops from to :=
        gather_jops from to 0 ajtable_numRow.

  Lemma jops_invalid_eid': forall eid i j,
    gather_jops eid eid i j = 0.
  Proof.
    intros until j.
    pose proof (jops_invalid_eid eid eid i j ltac:(lia)) as Hinvalid.
    assumption.
  Qed.

  Lemma cum_jops_tail: forall eid_from eid_to,
    eid_from <= eid_to ->
    cum_jops eid_from (eid_to + 1) =
      cum_jops eid_from eid_to + jops_at eid_to.
  Proof.
    intros eid_from eid_to Hrange.
    unfold cum_jops, jops_at.
    rewrite (jops_split_eid eid_from eid_to (eid_to + 1) 0 ajtable_numRow) by lia.
    reflexivity.
  Qed.

  (* This lemma shows cum_jops is correctly defined. *)
  Theorem cum_jops_cons : forall eid to,
      0 <= eid < to ->
      cum_jops eid to =
        cum_jops (eid + 1) to
        + jops_at eid.
  Proof.
    intros eid to Hrange.
    unfold cum_jops, jops_at.
    rewrite Z.add_comm.
    rewrite (jops_split_eid eid (eid + 1) to 0 ajtable_numRow) by lia.
    reflexivity.
  Qed.

  Lemma ajtable_enable_terminates:
    ajtable_values enabled_cell (ajtable_numRow - 1) = 0.
  Proof.
    simpl.
    replace (JtableOffsetMax * (ajtable_numRow - 1) + JtableOffsetEnable)
      with (JtableOffsetMax * ajtable_numRow - JtableOffsetMax + JtableOffsetEnable) by lia.
    unfold ajtable_numRow.
    rewrite Z.mul_comm.
    rewrite <- Z_div_mul.
    - apply enable_terminates.
    - unfold JtableOffsetMax; lia.
    - apply numRow_parity.
  Qed.

  Lemma rest_out_of_range:
    ajtable_values rest_cell ajtable_numRow = 0.
  Proof.
    pose proof ajtable_rest_jops_terminates as Hterm.
    pose proof ajtable_enable_terminates as Henable.
    pose proof ajtable_numRow_lower_bound as Hnonneg.
    assert (0 < STATIC_FRAME_ENTRY_NUMBER) as Hsn by (unfold STATIC_FRAME_ENTRY_NUMBER; lia).
    replace ajtable_numRow with ((ajtable_numRow - 1) + 1) by lia.
    rewrite <- rest_jops_change_disabled by lia.
    assumption.
  Qed.

  (* This theorem proves that the rest_jops column is correct. *)
  Theorem rest_jops_correct : forall from to,
      cum_jops from to <= Z.land (ajtable_values rest_cell 0) (Z.ones JOPS_SEPARATE).
  Proof.
    intros.
    unfold cum_jops.
    pose proof ajtable_numRow_lower_bound as Hlb.
    assert (0 < STATIC_FRAME_ENTRY_NUMBER) as Hsn by (unfold STATIC_FRAME_ENTRY_NUMBER; lia).
    rewrite (gather_jops_append from to 0 (ajtable_numRow - 1) ajtable_numRow) by lia.
    assert (gather_jops from to (ajtable_numRow - 1) ajtable_numRow = 0) as Hterm.
    {
      unfold gather_jops.
      replace (Z.to_nat (ajtable_numRow - (ajtable_numRow - 1))) with 1%nat by lia.
      rewrite gather_jops'_1.
      rewrite jops_of_last.
      reflexivity.
    }
    rewrite Hterm.
    rewrite Z.add_0_r.
    apply rest_jops_bound; lia.
  Qed.

  Lemma jops_at_frame_id_not_static:
    forall i entry frame_id,
      0 <= i < ajtable_numRow - 1 ->
      ajtable_values enabled_cell i = 1 ->
      ajtable_values static_bit_cell i = 0 ->
      ajtable_values entry_cell i = entry ->
      entry_id entry = frame_id ->
      jops_at frame_id >= 1.
  Proof.
    intros until frame_id. intros Hi Henable Hstatic Hentry Hframe_id.
    unfold jops_at.
    pose proof (gather_jops_append frame_id (frame_id + 1) 0 i ajtable_numRow 
      ltac:(lia)) as Hlow.
    pose proof (gather_jops_append frame_id (frame_id + 1) i (i + 1) ajtable_numRow 
      ltac:(lia)) as Hhigh.
    rewrite Hhigh in Hlow.
    clear Hhigh.
    rewrite !Z.add_assoc in Hlow.
    pose proof (gather_jops_nonnegative frame_id (frame_id + 1) 0 i)
      as H0i.
    pose proof (gather_jops_nonnegative frame_id (frame_id + 1) (i + 1) ajtable_numRow)
      as Hin.
    pose proof (gather_jops_1 frame_id (frame_id + 1) i) as Hentry'.
    assert (jops_of frame_id (frame_id + 1) i >= 1) as Hjops.
    {
      unfold jops_of.
      replace (i <? ajtable_numRow - 1) with true by lia.
      rewrite Henable.
      rewrite Hstatic.
      rewrite <- Hentry in Hframe_id.
      rewrite Hframe_id.
      replace (frame_id <=? frame_id) with true by lia.
      replace (frame_id <? frame_id + 1) with true by lia.
      rewrite Bool.andb_true_r.
      simpl.
      lia.
    }
    rewrite Hlow.
    lia.
  Qed.

  Lemma contrapositive: forall (P Q: Prop),
    (P -> Q) -> (~Q -> ~P).
  Proof.
    intros P Q H H' P'.
    apply H in P'.
    contradiction.
  Qed.

  Lemma entry_id_0_is_not_static:
    forall i,
      0 <= i ->
      entry_id (ajtable_values entry_cell i) <> 0 ->
      STATIC_FRAME_ENTRY_NUMBER <= i.
  Proof.
    intros i Hi Hentry.
    assert (ajtable_values static_bit_cell i = 0) as Hstatic.
    {
      pose proof static_is_bit' i ltac:(lia) as [Hstatic | Hstatic]; [assumption|].
      exfalso.
      apply Hentry.
      apply static_entries_id_zero.
      assumption.
    }
    destruct (static_entries_first i) as [_ Hentry'].
    pose proof contrapositive (i < STATIC_FRAME_ENTRY_NUMBER) 
      (ajtable_values static_bit_cell i = 1)
      as Hcontra.
    apply Hcontra in Hentry'; [|lia].
    lia.
  Qed.

  Lemma static_is_0_behead:
    forall i,
      STATIC_FRAME_ENTRY_NUMBER <= i ->
      ajtable_values static_bit_cell i = 0.
  Proof.
    intros i Hi.
    unfold STATIC_FRAME_ENTRY_NUMBER in Hi.
    assert (0 <= i) as Hi' by lia.
    pose proof static_is_bit' i ltac:(lia) as Hstatic.
    assert (i < STATIC_FRAME_ENTRY_NUMBER -> False) as Hbehead 
      by (unfold STATIC_FRAME_ENTRY_NUMBER; lia).
    assert (ajtable_values static_bit_cell i = 1 -> False) as Hstatic'.
    {
      intros Hfalse.
      apply Hbehead.
      apply static_entries_first.
      assumption.
    }
    lia.
  Qed.

  Lemma frame_id_is_0_head:
    forall i,
      0 <= i < STATIC_FRAME_ENTRY_NUMBER ->
      entry_id (ajtable_values entry_cell i) = 0.
  Proof.
    intros i Hi.
    unfold STATIC_FRAME_ENTRY_NUMBER in Hi.
    assert (ajtable_values static_bit_cell i = 1) as Hstatic.
    {
      apply static_entries_first.
      unfold STATIC_FRAME_ENTRY_NUMBER; lia.
    }
    pose proof static_entries_id_zero i Hstatic as Hentry_id.
    assumption.
  Qed.

  Lemma frame_id_is_pos_behead:
    forall i,
      STATIC_FRAME_ENTRY_NUMBER <= i < ajtable_numRow ->
      ajtable_values enabled_cell i = 1 ->
      0 < entry_id (ajtable_values entry_cell i).
  Proof.
    intros i Hi Henable.
    pose proof ajtable_frame_id_is_positive i Henable as Hpos.
    pose proof static_is_0_behead i ltac:(lia) as Hstatic.
    lia.
  Qed.

  Lemma jops_at_frame_id_numRows:
    forall i,
      i = ajtable_numRow - 1 ->
      ajtable_values enabled_cell i = 1 ->
      False.
  Proof.
    intros i Hi Henable.
    rewrite Hi in Henable.
    rewrite ajtable_enable_terminates in Henable.
    lia.
  Qed.

  Lemma jops_at_frame_id:
    forall i entry frame_id,
      STATIC_FRAME_ENTRY_NUMBER <= i < ajtable_numRow ->
      ajtable_values enabled_cell i = 1 ->
      ajtable_values entry_cell i = entry ->
      entry_id entry = frame_id ->
      jops_at frame_id >= 1.
  Proof.
    intros i entry frame_id Hi Henable Hentry Hframe.
    assert (0 <= i) as Hi'.
    {
      unfold STATIC_FRAME_ENTRY_NUMBER in Hi.
      lia.
    }
    assert (STATIC_FRAME_ENTRY_NUMBER <= i < ajtable_numRow - 1
      \/ i = ajtable_numRow - 1) 
      as [Hhigh | Hlast] 
      by lia.
    - pose proof static_is_0_behead i ltac:(lia) as Hstatic.
      apply (jops_at_frame_id_not_static i entry frame_id); lia.
    - pose proof jops_at_frame_id_numRows i ltac:(lia) Henable.
      lia.
  Qed.

  (* This lemma shows every call entry is counted. *)
  Theorem jtable_call_ops : forall frame_id last_frame_id callee_fid fid iid,
      0 < frame_id < common ->
      0 <= last_frame_id < common ->
      0 <= callee_fid < common ->
      0 <= fid < common ->
      0 <= iid < common ->
      JTableModel.in_jtable (encode_frame_table_entry
                               frame_id last_frame_id callee_fid fid iid) ->
      jops_at frame_id >= 1.
  Proof.
    intros until iid. intros Hframe Hlast Hcallee Hfid Hiid (i & Hi & Hentry).
    simpl in Hentry.
    remember (encode_frame_table_entry frame_id last_frame_id callee_fid fid iid)
      as entry.
    rewrite sel_spec in Hentry.
    destruct (Z.eq_dec (i mod JtableOffsetMax) 0) as [Hsel | Hnonsel].
    - (* sel *)
      rewrite Z.mul_1_r in Hentry.
      assert (exists a, i = JtableOffsetMax * a) as [a Ha].
      {
        exists (i / JtableOffsetMax).
        rewrite <- Z_div_exact_full_2; [lia|..|lia].
        apply jtable_offset_max_nonzero.
      }
      assert (a = i / JtableOffsetMax) as Ha'.
      {
        rewrite Ha.
        rewrite Z.mul_comm.
        rewrite Z.div_mul.
        - reflexivity.
        - apply jtable_offset_max_nonzero.
      }
      assert (0 <= a < ajtable_numRow) as Ha''.
      {
        rewrite Ha'.
        pose proof (jtable_offset_max_pos) as Hpos.
        split.
        - apply Z.div_pos; lia.
        - unfold ajtable_numRow.
          apply Z.div_lt_upper_bound; [lia|].
          + rewrite <- Z_div_exact_2.
            * lia.
            * lia.
            * apply numRow_parity.
      }
      rewrite Ha in Hentry.
      assert (entry_id entry = frame_id) as Hrame_id.
      {
        rewrite Heqentry.
        apply entry_id_spec; lia.
      }
      pose proof (frame_id_has_entry entry frame_id ltac:(lia) Hrame_id) as Hentry'.
      rewrite <- Hentry in Hentry'.
      pose proof (entry_nonzero_enabled a ltac:(lia)) as Henabled.
      simpl in Henabled.
      specialize (Henabled Hentry').
      assert (ajtable_values enabled_cell a = 1) as Henabled'.
      {
        simpl. assumption.
      }
      assert (ajtable_values entry_cell a = entry) as Hentry''.
      {
        simpl. lia.
      }
      assert (0 <= a < STATIC_FRAME_ENTRY_NUMBER \/ STATIC_FRAME_ENTRY_NUMBER <= a < ajtable_numRow)
        as [Hlow | Hhigh] by lia.
      + assert (0 < frame_id) as Hframe_id_pos by lia.
        assert (0 = frame_id) as Hframe_id_0.
        {
          rewrite <- Hrame_id.
          symmetry.
          rewrite <- Hentry''.
          apply (frame_id_is_0_head a ltac:(lia)).
        }
        lia.
      + pose proof (jops_at_frame_id a entry frame_id
          ltac:(lia) Henabled' Hentry'' Hrame_id) 
          as Hjops.
      assumption.
    - (* nonsel *)
      assert (entry = 0) as Hentry' by lia.
      assert (entry_id entry = frame_id) as Hrame_id.
      {
        rewrite Heqentry.
        apply entry_id_spec; lia.
      }
      pose proof (frame_id_has_entry entry frame_id ltac:(lia) Hrame_id) as Hentry''.
      lia.
  Qed.

  Corollary jtable_no_ops : forall frame_id last_frame_id callee_fid fid iid,
      0 < frame_id < common ->
      0 <= last_frame_id < common ->
      0 <= callee_fid < common ->
      0 <= fid < common ->
      0 <= iid < common ->
      JTableModel.in_jtable (encode_frame_table_entry
                                frame_id last_frame_id callee_fid fid iid) ->
      jops_at frame_id = 0 ->
      False.
  Proof.
    intros.
    pose proof (jtable_call_ops frame_id last_frame_id callee_fid fid iid 
    ltac:(lia) ltac:(assumption) ltac:(assumption) 
    ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hjops'.
    lia.
  Qed.

  Theorem jops_at_nonnegative : forall frame_id,
      jops_at frame_id >= 0.
  Proof.
    intros frame_id.
    unfold jops_at.
    pose proof gather_jops_nonnegative frame_id (frame_id + 1) 0 ajtable_numRow as Hnonneg.
    lia.
  Qed.

  Theorem cum_jops_nonnegative  : forall from to,
      0 <= cum_jops from to.
  Proof.
    intros from to.
    unfold cum_jops.
    pose proof gather_jops_nonnegative from to 0 ajtable_numRow as Hnonneg.
    lia.
  Qed.

  Lemma jops_of_empty_range:
    forall eid i,
      jops_of eid eid i = 0.
  Proof.
    intros eid i.
    unfold jops_of.
    destruct (i <? ajtable_numRow - 1) eqn: Hvalid; [|lia].
    destruct (ajtable_values enabled_cell i =? 1) eqn: Henable; [|lia].
    remember (entry_id (ajtable_values entry_cell i)) as eid'.
    assert (eid' < eid \/ eid <= eid') as [Hlow | Hhigh] by lia.
    - assert (eid <=? eid' = false) as Hr by lia.
      rewrite Hr.
      rewrite Bool.andb_false_l.
      lia.
    - assert (eid' <? eid = false) as Hr by lia.
      rewrite Hr.
      rewrite Bool.andb_false_r.
      lia.
  Qed.

  Lemma gather_jops'_empty_range:
    forall eid i n,
      gather_jops' eid eid i n = 0.
  Proof.
    intros eid i n. generalize i. clear i.
    induction n as [|n IHn]; intros i.
    - rewrite gather_jops'_0. reflexivity.
    - rewrite gather_jops'_head.
      rewrite jops_of_empty_range.
      rewrite (IHn (i + 1)).
      lia.
  Qed.

  Lemma gather_jops_empty_range:
    forall eid i j,
      gather_jops eid eid i j = 0.
  Proof.
    intros eid i j.
    unfold gather_jops.
    remember (Z.to_nat (j - i)) as n.
    apply gather_jops'_empty_range.
  Qed.

  Theorem cum_jops_empty_range : forall i,
      cum_jops i i = 0.
  Proof.
    intros i.
    unfold cum_jops.
    rewrite gather_jops_empty_range.
    reflexivity.
  Qed.
  

  Lemma gather_jops'_eid_0:
    forall i n,
      STATIC_FRAME_ENTRY_NUMBER <= i < ajtable_numRow ->
      gather_jops' 0 1 i n = 0.
  Proof.
    intros i n Hi.
    induction n as [|n IHn].
    - rewrite gather_jops'_0. reflexivity.
    - rewrite gather_jops'_tail by lia.
      rewrite IHn.
      assert (i + Z.of_nat n < ajtable_numRow \/ i + Z.of_nat n >= ajtable_numRow)
        as [Hlow | Hhigh] 
        by lia.
      + unfold jops_of.
        destruct (i + Z.of_nat n <? ajtable_numRow - 1); [|lia].
        destruct (ajtable_values enabled_cell (i + Z.of_nat n) =? 1) eqn: Henable; [|lia].
        assert (ajtable_values enabled_cell (i + Z.of_nat n) = 1) as Henable' by lia.
        pose proof frame_id_is_pos_behead (i + Z.of_nat n) ltac:(lia) Henable' as Hpos.
        remember (entry_id (ajtable_values entry_cell (i + Z.of_nat n))) as eid.
        assert ((eid <? 1) = false) as Hinvalid_eid by lia.
        rewrite Hinvalid_eid.
        rewrite Bool.andb_false_r.
        reflexivity.
      + pose proof jops_of_invalid_i 0 1 (i + Z.of_nat n) ltac:(lia) as Hinvalid.
        rewrite Hinvalid.
        reflexivity.
  Qed.

  Lemma gather_jops'_nonneg:
    forall min_eid max_eid i n,
      0 <= gather_jops' min_eid max_eid i n.
  Proof.
    intros min_eid max_eid i n.
    induction n as [|n IHn].
    - rewrite gather_jops'_0. reflexivity.
    - rewrite gather_jops'_tail by lia.
      pose proof jops_of_nonnegative min_eid max_eid (i + Z.of_nat n) as Hnonneg.
      lia.
  Qed.

  Lemma gather_jops'_unique_eid:
    forall eid n,
      gather_jops' eid (eid + 1) 0 n = 1 ->
      exists m,
        (m < n)%nat /\
        gather_jops' eid (eid + 1) 0 m = 0 /\
        jops_of eid (eid + 1) (Z.of_nat m) = 1 /\
        gather_jops' eid (eid + 1) (Z.of_nat m + 1) (n - m - 1) = 0.
    Proof.
      intros eid n Hjops.
      induction n as [|n IHn].
      - simpl in Hjops. destruct (0 <? ajtable_numRow - 1); lia.
      - rewrite gather_jops'_tail in Hjops by lia.
        rewrite Z.add_0_l in Hjops by lia.
        pose proof gather_jops'_nonneg eid (eid + 1) 0 n as Hnonneg.
        pose proof jops_of_range eid (eid + 1) (Z.of_nat n) as Hjops'.
        assert (
          (gather_jops' eid (eid + 1) 0 n = 1 /\ 
           jops_of eid (eid + 1) (Z.of_nat n) = 0) \/
          (gather_jops' eid (eid + 1) 0 n = 0 /\
           jops_of eid (eid + 1) (Z.of_nat n) = 1))
          as [[Hbetail Htail] | [Hbetail Htail]]
          by lia.
        + specialize (IHn Hbetail).
          destruct IHn as [m [Hmn [Hmleft [Hm1 Hmright]]]].
          exists m.
          split; [lia|].
          split; [lia|].
          split; [lia|].
          replace (S n - m - 1)%nat with (S (n - m - 1))%nat by lia.
          rewrite gather_jops'_tail by lia.
          rewrite Hmright.
          replace (Z.of_nat m + 1 + Z.of_nat (n - m - 1))
            with (Z.of_nat n) by lia.
          rewrite Htail.
          reflexivity.
        + exists n.
          split; [lia|].
          split; [lia|].
          split; [lia|].
          replace (S n - n - 1)%nat with 0%nat by lia.
          rewrite gather_jops'_0.
          reflexivity.
  Qed.

  Lemma gather_jops_unique_eid:
    forall eid j,
      gather_jops eid (eid + 1) 0 j = 1 ->
      exists i,
        i < j /\
        gather_jops eid (eid + 1) 0 i = 0 /\
        jops_of eid (eid + 1) i = 1 /\
        gather_jops eid (eid + 1) (i + 1) j = 0.
    Proof.
      intros eid j Hjops.
      unfold gather_jops in Hjops.
      rewrite Z.sub_0_r in Hjops.
      remember (Z.to_nat j) as n.
      pose proof gather_jops'_unique_eid eid n ltac:(lia) as Hunique.
      destruct Hunique as [m [Hmn [Hmleft [Hm1 Hmright]]]].
      remember (Z.of_nat m) as i.
      exists i.
      split; [lia|].
      split.
      - rewrite gather_jops'_unwrap by lia.
        replace  (Z.to_nat (i - 0)) with m by lia.
        assumption.
      - split; [lia|].
        rewrite gather_jops'_unwrap by lia.
        replace (Z.to_nat (j - (i + 1))) with (n - m - 1)%nat by lia.
        assumption.
    Qed.

  Lemma jops_at_frame_id_exactly_1_implies':
    forall eid,
      jops_at eid = 1 ->
      exists i,
        i < ajtable_numRow /\
        gather_jops eid (eid + 1) 0 i = 0 /\
        jops_of eid (eid + 1) i = 1 /\
        gather_jops eid (eid + 1) (i + 1) ajtable_numRow = 0.
  Proof.
    intros eid Hjops.
    unfold jops_at in Hjops.
    pose proof gather_jops_unique_eid
      eid ajtable_numRow Hjops
      as Hunique.
    assumption.
  Qed.

  Lemma gather_jops'_static:
    forall min_eid max_eid i n,
      i < STATIC_FRAME_ENTRY_NUMBER ->
      i + Z.of_nat n < STATIC_FRAME_ENTRY_NUMBER ->
      gather_jops' min_eid max_eid i n = 0.
  Proof.
    intros min_eid max_eid i n Hi Hn.
    induction n as [|n IHn].
    - rewrite gather_jops'_0. reflexivity.
    - rewrite gather_jops'_tail by lia.
      rewrite IHn by lia.
      assert (ajtable_values static_bit_cell (i + Z.of_nat n) = 1) as Hstatic.
      {
        apply static_entries_first; lia.
      }
      pose proof jops_of_static min_eid max_eid (i + Z.of_nat n) ltac:(lia) as Hjops.
      rewrite Hjops.
      reflexivity.
  Qed.

  Lemma gather_jops_static:
    forall min_eid max_eid i j,
      j < STATIC_FRAME_ENTRY_NUMBER ->
      gather_jops min_eid max_eid i j = 0.
  Proof.
    intros min_eid max_eid i j Hj.
    assert (i < j \/ j <= i) as [Hlow | Hhigh] by lia.
    - unfold gather_jops.
      remember (Z.to_nat (j - i)) as n.
      apply gather_jops'_static; lia.
    - rewrite gather_jops_invalid_range by lia.
      reflexivity.
  Qed.

  Lemma jops_at_frame_id_exactly_1_implies:
    forall eid,
      jops_at eid = 1 ->
      exists i,
        STATIC_FRAME_ENTRY_NUMBER <= i < ajtable_numRow /\
        gather_jops eid (eid + 1) 0 i = 0 /\
        jops_of eid (eid + 1) i = 1 /\
        gather_jops eid (eid + 1) (i + 1) ajtable_numRow = 0.
  Proof.
    intros eid Hjops.
    pose proof jops_at_frame_id_exactly_1_implies' eid Hjops as Hunique.
    destruct Hunique as [i [Hirange [Hileft [Hi1 Hiright]]]].
    exists i.
    split; [|lia].
    split; [|lia].
    assert (i < STATIC_FRAME_ENTRY_NUMBER \/ STATIC_FRAME_ENTRY_NUMBER <= i) as [Hlow |] 
      by lia;
      [|lia].
    assert (ajtable_values static_bit_cell i = 1) as Hstatic.
    {
      apply static_entries_first; lia.
    }
    pose proof jops_of_static eid (eid + 1) i ltac:(lia) as Hjops'.
    rewrite Hi1 in Hjops'.
    inversion Hjops'.
  Qed.

End gather_jops.

Lemma entry_unique_static_absurd : forall eid,
  eid <> 0 ->
  forall i,
    0 <= i < STATIC_FRAME_ENTRY_NUMBER ->
    ajtable_values enabled_cell i = 1 ->
    entry_id (ajtable_values entry_cell i) = eid ->
    False.
Proof.
  intros eid Hneq i Hi Henabled Hentry.
  assert (eid = 0) as Heid.
  {
    pose proof frame_id_is_0_head i ltac:(lia) as Hframe_id.
    rewrite Hentry in Hframe_id.
    assumption.
  }
  contradiction.
Qed.

Lemma gather_jops'_0_enable_absurd:
  forall eid i k n,
    STATIC_FRAME_ENTRY_NUMBER <= i ->
    i + Z.of_nat n < ajtable_numRow ->
    i <= k < i + Z.of_nat n ->
    gather_jops' eid (eid + 1) i n = 0 ->
    ajtable_values enabled_cell k = 1 ->
    entry_id (ajtable_values entry_cell k) = eid ->
    False.
Proof.
  intros eid i k n Hi Hn Hik Hjops Henabled.
  generalize dependent i.
  generalize dependent k.
  induction n as [|n IHn]; intros k Henable i Hi Hn Hik Hjops Hentry.
  - lia.
  - rewrite gather_jops'_tail in Hjops by lia.
    pose proof gather_jops'_nonneg eid (eid + 1) i n as Hnonneg.
    pose proof jops_of_range eid (eid + 1) (i + Z.of_nat n) as Hjops'.
    assert (gather_jops' eid (eid + 1) i n = 0) as Hgather by lia.
    assert (jops_of eid (eid + 1) (i + Z.of_nat n) = 0) as Hjops'' by lia.
    assert (k < i + Z.of_nat n \/ k = i + Z.of_nat n) as [Hik' | Hik'] by lia.
    + specialize (IHn k Henable i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      exact IHn.
    + rewrite <- Hik' in Hjops''.
      unfold jops_of in Hjops''.
      pose proof static_is_0_behead k ltac:(lia) as Hstatic.
      destruct (k <? ajtable_numRow - 1) eqn: Hvalid; [|lia].
      rewrite Henable in Hjops''.
      rewrite Hentry in Hjops''.
      rewrite Hstatic in Hjops''.
      simpl in Hjops''.
      replace ((eid <=? eid) && (eid <? eid + 1)) with true in Hjops'' by lia.
      inversion Hjops''.
Qed.

Lemma gather_jops_0_enable_absurd:
  forall eid i k j,
    STATIC_FRAME_ENTRY_NUMBER <= i ->
    j < ajtable_numRow ->
    i <= k < j ->
    gather_jops eid (eid + 1) i j = 0 ->
    ajtable_values enabled_cell k = 1 ->
    entry_id (ajtable_values entry_cell k) = eid ->
    False.
Proof.
  intros eid i k j Hi Hj Hik Hjops Henabled Hentry.
  unfold gather_jops in Hjops.
  remember (Z.to_nat (j - i)) as n.
  assert (i + Z.of_nat n = j) as Hn by lia.
  pose proof gather_jops'_0_enable_absurd eid i k n Hi ltac:(lia) ltac:(lia) Hjops Henabled Hentry.
  exact H.
Qed.

Lemma gather_jops_0_split:
  forall min_eid max_eid i j k,
    i <= j <= k ->
    gather_jops min_eid max_eid i k = 0 ->
    gather_jops min_eid max_eid i j = 0 /\
    gather_jops min_eid max_eid j k = 0.
Proof.
  intros min_eid max_eid i j k Hij Hjops.
  rewrite gather_jops_append with (j:=j) in Hjops by lia.
  pose proof gather_jops_nonnegative min_eid max_eid i j as Hnonneg.
  pose proof gather_jops_nonnegative min_eid max_eid j k as Hnonneg'.
  lia.
Qed.

Lemma entry_unique_non_static : forall eid,
  jops_at eid <= 1 ->
  forall i j,
    STATIC_FRAME_ENTRY_NUMBER <= i < ajtable_numRow ->
    ajtable_values enabled_cell i = 1 ->
    entry_id (ajtable_values entry_cell i) = eid ->
    STATIC_FRAME_ENTRY_NUMBER <= j < ajtable_numRow ->
    ajtable_values enabled_cell j = 1 ->
    entry_id (ajtable_values entry_cell j) = eid ->
    i = j.
Proof.
  intros eid Hjops i j Hi Henabled_i Hentry_i Hj Henabled_j Hentry_j.
  assert (jops_at eid = 1) as Heid.
  {
    pose proof jops_at_frame_id i (ajtable_values entry_cell i) eid
      ltac:(lia) Henabled_i ltac:(lia) Hentry_i as Hjops_i.
      lia.
  }
  pose proof jops_at_frame_id_exactly_1_implies eid ltac:(lia) as Hexactly_1.
  destruct Hexactly_1 as [k [Hkrange [Hkleft [Hk1 Hkright]]]].
  assert (0 < STATIC_FRAME_ENTRY_NUMBER) 
    as Hstatic_entries 
    by (unfold STATIC_FRAME_ENTRY_NUMBER; lia).
  pose proof gather_jops_0_split eid (eid + 1) 0 STATIC_FRAME_ENTRY_NUMBER k
    ltac:(lia) Hkleft as [Hkleft_l Hleft_r].
  assert (k = ajtable_numRow - 1 \/ k < ajtable_numRow - 1) 
    as [Hklast | Hkrange']
    by lia.
  - pose proof jops_of_last eid (eid + 1) as Hklast'.
    rewrite Hklast in Hk1.
    rewrite Hk1 in Hklast'.
    inversion Hklast'.
  - pose proof gather_jops_0_split eid (eid + 1) (k + 1) (ajtable_numRow - 1) ajtable_numRow
      ltac:(lia) Hkright as [Hkright_l Hkright_r].
    assert (i = k \/ i <> k) as [Hik | Hik] by lia;
    assert (j = k \/ j <> k) as [Hjk | Hjk] by lia.
    + rewrite Hik, Hjk. reflexivity.
    + subst i.
      assert (j < k \/ k < j) as [Hjk' | Hjk'] by lia.
      * pose proof gather_jops_0_enable_absurd eid STATIC_FRAME_ENTRY_NUMBER j k
        ltac:(lia) ltac:(lia) ltac:(lia) Hleft_r Henabled_j Hentry_j.
        lia.
      * assert (j = ajtable_numRow - 1 \/ j < ajtable_numRow - 1) 
        as [Hjlast | Hjrange]
        by lia.
        --  pose proof ajtable_enable_terminates as Hterminates.
            rewrite Hjlast in Henabled_j.
            rewrite Hterminates in Henabled_j.
            inversion Henabled_j.
        --  pose proof gather_jops_0_enable_absurd eid (k + 1) j (ajtable_numRow - 1)
              ltac:(lia) ltac:(lia) ltac:(lia) Hkright_l Henabled_j Hentry_j.
            lia.
    + subst j.
      assert (i < k \/ k < i) as [Hik' | Hik'] by lia.
      * pose proof gather_jops_0_enable_absurd eid STATIC_FRAME_ENTRY_NUMBER i k
        ltac:(lia) ltac:(lia) ltac:(lia) Hleft_r Henabled_i Hentry_i.
        lia.
      * assert (i = ajtable_numRow - 1 \/ i < ajtable_numRow - 1) 
        as [Hi_last | Hi_range]
        by lia.
        --  pose proof ajtable_enable_terminates as Hterminates.
            rewrite Hi_last in Henabled_i.
            rewrite Hterminates in Henabled_i.
            inversion Henabled_i.
        --  pose proof gather_jops_0_enable_absurd eid (k + 1) i (ajtable_numRow - 1)
              ltac:(lia) ltac:(lia) ltac:(lia) Hkright_l Henabled_i Hentry_i.
            lia.
    + assert (i < k \/ k < i) as [Hik' | Hik'] by lia.
      * pose proof gather_jops_0_enable_absurd eid STATIC_FRAME_ENTRY_NUMBER i k
        ltac:(lia) ltac:(lia) ltac:(lia) Hleft_r Henabled_i Hentry_i.
        lia.
      * assert (i = ajtable_numRow - 1 \/ i < ajtable_numRow - 1) 
        as [Hi_last | Hi_range]
        by lia.
        --  pose proof ajtable_enable_terminates as Hterminates.
            rewrite Hi_last in Henabled_i.
            rewrite Hterminates in Henabled_i.
            inversion Henabled_i.
        --  pose proof gather_jops_0_enable_absurd eid (k + 1) i (ajtable_numRow - 1)
              ltac:(lia) ltac:(lia) ltac:(lia) Hkright_l Henabled_i Hentry_i.
            lia.
  Qed.

(* This is the main nontrivial result, which we use to prove the correctness of the return operation. *)
Lemma entry_unique : forall eid,
  eid <> 0 ->
  jops_at eid <= 1 ->
  forall i j,
    0 <= i < ajtable_numRow ->
    ajtable_values enabled_cell i = 1 ->
    entry_id (ajtable_values entry_cell i) = eid ->
    0 <= j < ajtable_numRow ->
    ajtable_values enabled_cell j = 1 ->
    entry_id (ajtable_values entry_cell j) = eid ->
    i = j.
Proof.
  intros eid Heid Hjops i j Hi Henabled_i Hentry_i Hj Henabled_j Hentry_j.
  assert (STATIC_FRAME_ENTRY_NUMBER <= i < ajtable_numRow
    \/ i < STATIC_FRAME_ENTRY_NUMBER) as Hi_split by lia.
  assert (STATIC_FRAME_ENTRY_NUMBER <= j < ajtable_numRow
    \/ j < STATIC_FRAME_ENTRY_NUMBER) as Hj_split by lia.
  destruct Hi_split as [Hi_static | Hi_non_static];
  destruct Hj_split as [Hj_static | Hj_non_static].
  - apply entry_unique_non_static with (eid:=eid); lia.
  - pose proof entry_unique_static_absurd eid Heid j ltac:(lia) Henabled_j Hentry_j.
    contradiction.
  - pose proof entry_unique_static_absurd eid Heid i ltac:(lia) Henabled_i Hentry_i.
    contradiction.
  - pose proof entry_unique_static_absurd eid Heid i ltac:(lia) Henabled_i Hentry_i.
    contradiction.
Qed.

Lemma in_jtable_implies:
  forall {eid next_id cfid fid iid i},
    0 < eid < common ->
    0 <= next_id < common ->
    0 <= cfid < common ->
    0 <= fid < common ->
    0 <= iid < common ->
    0 <= i < jtable_numRow ->
    value jtable data_col (i + JtableOffsetEntry) * value jtable sel_col i 
        = encode_frame_table_entry eid next_id cfid fid iid ->
    exists i',
      i' = i / JtableOffsetMax /\
      0 <= i' < ajtable_numRow /\
      ajtable_values entry_cell i' > 0 /\
      ajtable_values enabled_cell i' = 1 /\
      ajtable_values entry_cell i' = encode_frame_table_entry eid next_id cfid fid iid /\
      entry_id (ajtable_values entry_cell i') = eid.
Proof.
  intros eid next_id cfid fid iid i Heid Hnext_id Hcfid Hfid Hiid Hi Hentry.
  remember (encode_frame_table_entry eid next_id cfid fid iid) as entry.
  exists (i / JtableOffsetMax).
  split; [lia|].
  remember (i / JtableOffsetMax) as i'.
  pose proof numRow_parity as Hparity.
  pose proof jtable_offset_max_pos as Hjops_pos.
  assert (0 <= i' < ajtable_numRow) as Hi'.
  {
    subst i'. 
    unfold ajtable_numRow.
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; [lia|].
      rewrite <- Z_div_exact_2; lia.
  }
  split; [lia|].
  assert (entry_id entry = eid) as Hentry_i_id.
  {
    rewrite Heqentry.
    apply entry_id_spec; lia.
  }
  assert (entry > 0) as Hentry_i_pos.
  {
    apply (frame_id_has_entry entry eid); lia.
  }
  assert (i mod JtableOffsetMax = 0) as Hentry_i_mod.
  {
    pose proof sel_spec i as Hsel.
    destruct (Z.eq_dec (i mod JtableOffsetMax) 0) as [Hmod | Hnmod]; [assumption|].
    simpl in Hentry.
    rewrite Hsel in Hentry.
    lia.
  }
  assert (value jtable sel_col i = 1) as Hsel.
  {
    pose proof sel_spec i as Hsel.
    rewrite Hentry_i_mod in Hsel.
    simpl in Hsel.
    assumption.
  }
  rewrite Hsel in Hentry.
  rewrite Z.mul_1_r in Hentry.
  assert (ajtable_values entry_cell i' = entry) as Hentry_i.
  {
    subst i'.
    simpl.
    rewrite <- Z_div_exact_2; [|lia|lia].
    simpl in Hentry.
    assumption.
  }
  split; [lia|].
  assert (ajtable_values enabled_cell i' = 1) as Henabled.
  {
    apply entry_nonzero_enabled; lia.
  }
  split; [lia|].
  rewrite Hentry_i.
  split; lia.
Qed.

Lemma sel_col_bit : forall i,
    0 <= i ->
    jtable_values sel_col i  = 0
  \/
    exists j, i = JtableOffsetMax * j /\ jtable_values sel_col (JtableOffsetMax * j) = 1.
Proof.
  intros i Hrange.
  rewrite (sel_spec i).
  destruct (Z.eq_dec (i mod JtableOffsetMax) 0) as [e|e].
  - right.
    apply Z_mod_exists_mul in e.
    2: { unfold JtableOffsetMax; lia. }
    destruct e as [j Hj].
    exists j.
    split; [lia|].
    rewrite sel_spec, Z_mul_mod_l.
    reflexivity.
  - left.
    reflexivity.
Qed.

Lemma encode_zero_next_id : forall {id next_id cfid fid iid},
    0 = encode_frame_table_entry id next_id cfid fid iid  ->
    0 <= id < common ->
    0 <= next_id < common ->
    0 <= cfid < common ->
    0 <= fid < common ->
    0 <= iid < common ->
    next_id = 0.
Proof.
  intros id next_id cfid fid iid Hin
            Hid_common Hnext_id_common Hcfid_common Hfid_common Hiid_common.
  replace 0 with (encode_frame_table_entry 0 0 0 0 0) in Hin.
    2: {
      unfold encode_frame_table_entry.
      rewrite !Z.mul_0_l.
      rewrite Zmod_0_l.
      reflexivity.
    }
    apply encode_frame_table_entry_inj in Hin; try lia.
Qed.

Corollary in_jtable_unique : forall {eid next_id next_id' cfid cfid' fid fid' iid iid'},
  jops_at eid <= 1 ->
  in_jtable (encode_frame_table_entry eid next_id  cfid  fid  iid) ->
  in_jtable (encode_frame_table_entry eid next_id' cfid' fid' iid') ->
  0 < eid < common ->
  0 <= next_id < common ->
  0 <= next_id' < common ->
  0 <= cfid < common ->
  0 <= cfid' < common ->
  0 <= fid < common ->
  0 <= fid' < common ->
  0 <= iid < common ->
  0 <= iid' < common ->
  (next_id=next_id' /\ cfid=cfid' /\ fid=fid' /\ iid=iid').
Proof.
  intros eid next_id next_id' cfid cfid' fid fid' iid iid' 
    Hjops Hin1 Hin2 Heid Hnext_id Hnext_id' Hcfid Hcfid' Hfid Hfid' Hiid Hiid' .
  destruct Hin1 as [i [Hi Hentry_i]].
  destruct Hin2 as [j [Hj Hentry_j]].
  pose proof in_jtable_implies Heid Hnext_id Hcfid Hfid Hiid Hi Hentry_i as Hin1'.
  pose proof in_jtable_implies Heid Hnext_id' Hcfid' Hfid' Hiid' Hj Hentry_j as Hin2'.
  destruct Hin1' as (i' & Hi' & Hi'range & Hentry_i_pos & Henabled_i & Hencode_i & Hentry_i_id).
  destruct Hin2' as (j' & Hj' & Hj'range & Hentry_j_pos & Henabled_j & Hencode_j & Hentry_j_id).
  pose proof entry_unique eid ltac:(lia) Hjops i' j' Hi'range Henabled_i Hentry_i_id Hj'range Henabled_j Hentry_j_id as Hunique.
  assert (encode_frame_table_entry eid next_id cfid fid iid = 
          encode_frame_table_entry eid next_id' cfid' fid' iid') as Hencode.
  {
    rewrite Hunique in Hencode_i.
    rewrite Hencode_i in Hencode_j.
    assumption.
  }
  pose proof encode_frame_table_entry_inj 
    eid eid next_id next_id' cfid cfid' fid fid' iid iid' 
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) Hencode
    as Heq.
  destruct Heq as (Heqeid & Heqnext_id & Heqcfid & Heqfid & Heqiid).
  repeat split; lia.
Qed.

Lemma id_zero_entries : forall {id next_id cfid fid iid},
    in_jtable (encode_frame_table_entry id next_id cfid fid iid) ->
    0 <= id < common ->
    0 <= next_id < common ->
    0 <= cfid < common ->
    0 <= fid < common ->
    0 <= iid < common ->
    id = 0 ->
    next_id = 0.
Proof.
  intros id next_id cfid fid iid Hin
         Hid_common Hnext_id_common Hcfid_common Hfid_common Hiid_common Hid_Zero.
  unfold in_jtable in Hin.
  destruct Hin as [i [Hrange Hin]].
  simpl in Hin.
  destruct (sel_col_bit i ltac:(lia)) as [Hsel | Hsel].
  - rewrite Hsel in *.
    rewrite Z.mul_0_r in Hin.
    apply (encode_zero_next_id Hin); lia.
  - destruct Hsel as [j [Hj Hsel]].
    rewrite Hj in *.
    rewrite Hsel in Hin.
    rewrite Z.mul_1_r in Hin.
    change (jtable_values data_col (JtableOffsetMax * j + JtableOffsetEntry))
      with (ajtable_values entry_cell j) in Hin.
    clear Hj Hsel.
    assert (Hj_nonneg : 0 <= j).
    {
      unfold JtableOffsetMax in Hrange.
      lia.
    }
    destruct (static_is_bit' j Hj_nonneg) as [Hstatic | Hstatic].
    + destruct (enable_is_bit j Hj_nonneg) as [Henabled | Henabled].
      * rewrite disabled_entry_zero in Hin by lia.
        apply (encode_zero_next_id Hin); lia.
      * assert (Hnonzero:= ajtable_frame_id_is_positive j Henabled Hstatic).
        rewrite Hin in Hnonzero.
        rewrite entry_id_spec in Hnonzero; lia.
    + assert (H := ajtable_static_entries_next_id_zero j Hstatic).
      rewrite Hin in H.
      rewrite next_entry_id_spec in H; lia.
Qed.
