(* This file contains some generic results about the behavior of the
integer functions (bitwise AND, OR, etc).  *)

Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Wasm.numerics.

Require Import Shared.

(* Same definition as in WasmCert *)
Definition popcnt (x: Z) :=
  (Z.of_nat
     (seq.count (fun b : eqtype.Equality.sort eqtype.bool_eqType => eqtype.eq_op b true)
        (Wasm_int.Int64.power_index_to_bits Wasm_int.Int64.wordsize
           (Zbits.Z_one_bits Wasm_int.Int64.wordsize x 0)))).

(* Shared lemmas about integers. *)

Lemma lor_xI:
  forall x,
  Z.pos x~1 = Z.lor (Z.pos x * 2) 1.
Proof.
  intros.
  replace (Z.pos x~1) with (Z.pos x * 2 + 1) by lia.
  assert (Z.land (Z.pos x * 2) 1 = 0) as Hxor.
  {
    replace 2 with (2 ^ 1) by reflexivity.
    rewrite <- Z.shiftl_mul_pow2; [|lia].
    Z.bitwise.
    reflexivity.
  }
  rewrite Z.add_nocarry_lxor; [|assumption].
  rewrite Z.lxor_lor; [|assumption].
  reflexivity.
Qed.

Lemma lor_xO:
  forall x,
  Z.pos x~0 = Z.pos x * 2.
Proof.
  intros. lia.
Qed.

Lemma testbit_xI':
  forall (x: positive) (i: Z) b,
    0 <= i ->
    Z.testbit (Z.pos x) i = b ->
    Z.testbit (Z.pos x~1) (i + 1) = b /\
    Z.testbit (Z.pos x~1) 0 = true.
Proof.
  intros x i b Hi H.
  pose proof (lor_xI x) as Hdecomp.
  split.
  - rewrite Hdecomp.
    rewrite Z.lor_spec.
    assert (i + 1 = 0 \/ i + 1 > 0) as [H'|H'] by lia.
    + lia.
    + replace 2 with (2 ^ 1) by lia.
      replace ((i + 1)) with (1 + i) by lia.
      rewrite Z.mul_pow2_bits_add; [|lia].
      rewrite H.
      replace (1) with (1 mod 2 ^ 1) at 1 by reflexivity.
      rewrite Z.mod_pow2_bits_high; [|lia].
      rewrite Bool.orb_false_r.
      reflexivity.
  - rewrite Hdecomp.
    rewrite Z.lor_spec.
    assert (Z.testbit 1 0 = true) as H1.
    {
      unfold Z.testbit.
      reflexivity.
    }
    rewrite H1.
    rewrite Bool.orb_true_r.
    reflexivity.
Qed.

Lemma testbit_xI:
  forall (x: positive) (i: Z),
    0 <= i ->
    Z.testbit (Z.pos x~1) (i + 1) = Z.testbit (Z.pos x) i.
Proof.
  intros until i. intros Hi.
  remember (Z.testbit (Z.pos x) i) as b. symmetry in Heqb.
  apply testbit_xI' in Heqb; [|assumption].
  destruct Heqb as [H _].
  assumption.
Qed.

Lemma testbit_xI'':
  forall (x: positive) (i: Z),
    1 <= i ->
    Z.testbit (Z.pos x~1) i = Z.testbit (Z.pos x) (i - 1).
Proof.
  intros until i. intros Hi.
  assert (i = i - 1 + 1) as H by lia.
  rewrite H.
  rewrite testbit_xI; [|lia].
  replace ((i - 1 + 1 - 1)) with (i - 1) by lia.
  reflexivity.
Qed.

Lemma testbit_xI_0:
  forall x,
  Z.testbit (Z.pos x~1) 0 = true.
Proof.
  intros.
  pose proof (lor_xI x) as Hdecomp.
  rewrite Hdecomp.
  rewrite Z.lor_spec.
  assert (Z.testbit 1 0 = true) as H1 by (unfold Z.testbit; reflexivity).
  rewrite H1.
  rewrite Bool.orb_true_r.
  reflexivity.
Qed.

Lemma testbit_xO':
  forall (x: positive) (i: Z) b,
    0 <= i ->
    Z.testbit (Z.pos x) i = b ->
    Z.testbit (Z.pos x~0) (i + 1) = b /\
    Z.testbit (Z.pos x~0) 0 = false.
Proof.
  intros until b. intros Hi Hb.
  assert (Z.pos x~0 = Z.pos x * 2) as Hdecomp by lia.
  rewrite Hdecomp.
  split.
  - replace 2 with (2 ^ 1) by lia.
    replace (i + 1) with (1 + i) by lia.
    rewrite Z.mul_pow2_bits_add; [|lia].
    assumption.
  - replace 2 with (2 ^ 1) by lia.
    rewrite Z.mul_pow2_bits_low; [|lia].
    reflexivity.
Qed.  

Lemma testbit_xO:
  forall (x: positive) (i: Z),
    0 <= i ->
    Z.testbit (Z.pos x~0) (i + 1) = Z.testbit (Z.pos x) i.
Proof.
  intros until i. intros Hi.
  remember (Z.testbit (Z.pos x) i) as b. symmetry in Heqb.
  apply testbit_xO' in Heqb; [|assumption].
  destruct Heqb as [H _].
  assumption.
Qed.

Lemma testbit_xO'':
  forall (x: positive) (i: Z),
    1 <= i ->
    Z.testbit (Z.pos x~0) i = Z.testbit (Z.pos x) (i - 1).
Proof.
  intros until i. intros Hi.
  assert (i = i - 1 + 1) as H by lia.
  rewrite H.
  rewrite testbit_xO; [|lia].
  replace ((i - 1 + 1 - 1)) with (i - 1) by lia.
  reflexivity.
Qed.

Lemma testbit_xO_0:
  forall x,
  Z.testbit (Z.pos x~0) 0 = false.
Proof.
  intros.
  pose proof (lor_xO x) as Hdecomp.
  rewrite Hdecomp.
  replace 2 with (2 ^ 1) by lia.
  rewrite Z.mul_pow2_bits_low; [|lia].
  reflexivity.
Qed.

Lemma xI_bound: forall x n,
  0 <= n ->
  0 <= Z.pos x < 2^n -> 0 <= Z.pos x~1 < 2^(n + 1).
Proof.
  intros x n Hn Hx.
  split; [lia|].
  replace (Z.pos x~1) with (Z.pos x * 2 + 1) by lia.
  assert (Z.pos x * 2 < 2 ^ n * 2) as Hx' by lia.
  rewrite Z.pow_add_r; [|lia|lia].
  rewrite Z.pow_1_r.
  lia.
Qed.

Lemma xO_bound: forall x n,
  0 <= n ->
  0 <= Z.pos x < 2^n -> 0 <= Z.pos x~0 < 2^(n + 1).
Proof.
  intros x n Hn Hx.
  split; [lia|].
  replace (Z.pos x~0) with (Z.pos x * 2) by lia.
  assert (Z.pos x * 2 < 2 ^ n * 2) as Hx' by lia.
  rewrite Z.pow_add_r; [|lia|lia].
  rewrite Z.pow_1_r.
  lia.
Qed.

Lemma bound_spec_n_l : forall x n,
  0 <= n ->
  0 <= x < 2^n -> (forall k,  n <= k -> Z.testbit x k = false).
Proof.
  destruct x as [|x|x].
  - intros n Hn H k Hk. rewrite Z.bits_0. reflexivity.
  - induction x.
    + intros n Hn Hx k Hk.
      assert (n = 0 \/ n > 0) as [Hn'|Hn'] by lia.
      * subst n.
        lia.
      * rewrite testbit_xI''; [|lia].
        assert (0 <= n - 1) as Hn'' by lia.
        assert (0 <= Z.pos x < 2 ^ (n - 1)) as Hx'.
        {
          split; [lia|].
          replace (Z.pos x~1) with (Z.pos x * 2 + 1) in Hx by lia.
          assert (Z.pos x * 2 < 2 ^ n) as Hx'' by lia.
          replace (n) with (n - 1 + 1) in Hx'' by lia.
          rewrite Z.pow_add_r in Hx''; [|lia|lia].
          rewrite Z.pow_1_r in Hx''.
          lia.
        }
        eapply (IHx (n - 1) Hn'' Hx' (k - 1)); try eassumption.
        lia.
    + intros n Hn Hx k Hk.
      assert (n = 0 \/ n > 0) as [Hn'|Hn'] by lia.
      * subst n.
        lia.
      * rewrite testbit_xO''; [|lia].
        assert (0 <= n - 1) as Hn'' by lia.
        assert (0 <= Z.pos x < 2 ^ (n - 1)) as Hx'.
        {
          split; [lia|].
          replace (Z.pos x~0) with (Z.pos x * 2) in Hx by lia.
          assert (Z.pos x * 2 < 2 ^ n) as Hx'' by lia.
          replace (n) with (n - 1 + 1) in Hx'' by lia.
          rewrite Z.pow_add_r in Hx''; [|lia|lia].
          rewrite Z.pow_1_r in Hx''.
          lia.
        }
        eapply (IHx (n - 1) Hn'' Hx' (k - 1)); try eassumption.
        lia.
    + intros n Hn Hx k Hk.
      assert (n = 0 \/ n > 0) as [Hn'|Hn'] by lia.
      * subst n. lia.
      * rewrite Z.bits_above_log2; [reflexivity|lia|].
        simpl. lia.
  - lia.
Qed.

Lemma negb_false_inv:
  forall b,
  negb b = false -> b = true.
Proof. intros. destruct b; auto. Qed.

Lemma negb_true_inv:
  forall b,
  negb b = true -> b = false.
Proof. intros. destruct b; auto. Qed.

Lemma testbit_Zneg_true':
  forall x,
    exists n, forall k, n < k -> Z.testbit (Z.neg x) k = true.
Proof.
  intros x.
  pose proof (Z.bits_iff_neg_ex (Z.neg x)) as H.
  assert (Z.neg x < 0) as Hx by lia.
  apply H in Hx.
  eapply Hx.
Qed.

Lemma testbit_Zneg_true:
  forall x,
    exists n, forall k, n <= k -> Z.testbit (Z.neg x) k = true.
Proof.
  intros x.
  pose proof (testbit_Zneg_true' x) as H.
  destruct H as [n H].
  exists (n + 1).
  intros k Hk.
  apply H.
  lia.
Qed.

Lemma testbit_Zneg_true_n:
  forall x,
    exists n, Z.testbit (Z.neg x) n = true.
Proof.
  intros x.
  pose proof (testbit_Zneg_true x) as H.
  destruct H as [n H].
  exists n.
  apply H.
  lia.
Qed.

Lemma zero_spec:
  forall x,
    (forall n, 0 <= n -> Z.testbit x n = false) ->
    x = 0.
Proof.
  intros x H.
  Z.bitwise.
  apply (H m).
  assumption.
Qed.

Lemma one_spec:
  Z.testbit 1 0 = true.
Proof. reflexivity. Qed.

Lemma bound_spec_n_r : forall x n,
  0 <= n ->
  0 <= x ->
  (forall k,  n <= k -> Z.testbit x k = false) -> 0 <= x < 2^n.
Proof.
  destruct x as [|x|x].
  - intros n Hn Hx H. lia.
  - induction x.
    + intros n Hn Hx H.
      assert (n = 0 \/ n > 0) as [Hn'|Hn'] by lia.
      * subst n.
        specialize (H 0).
        rewrite testbit_xI_0 in H.
        discriminate H; reflexivity.
      * split; [lia|].
        replace (Z.pos x~1) with (Z.pos x * 2 + 1) by lia.
        replace (n) with (n - 1 + 1) by lia.
        replace (2 ^ (n - 1 + 1)) with (2 ^ (n - 1) * 2) by (rewrite Z.pow_add_r; lia).
        assert (Z.pos x * 2 < 2 ^ (n - 1) * 2) as H'.
        {
          apply Z.mul_lt_mono_pos_r; [lia|].
          eapply (IHx (n - 1)); [lia|lia|].
          intros k Hk.
          specialize (H (k + 1)).
          rewrite testbit_xI in H; [|lia].
          apply H.
          lia.
        }
        lia.
    + intros n Hn Hx H.
      assert (n = 0 \/ n > 0) as [Hn'|Hn'] by lia.
      * subst n.
        assert (Z.pos x~0 = 0) as Hx'.
        {
          apply zero_spec in H. assumption.
        }
        rewrite Hx'. lia.
      * split; [lia|].
        replace (Z.pos x~0) with (Z.pos x * 2) by lia.
        replace (n) with (n - 1 + 1) by lia.
        replace (2 ^ (n - 1 + 1)) with (2 ^ (n - 1) * 2) by (rewrite Z.pow_add_r; lia).
        apply Z.mul_lt_mono_pos_r; [lia|].
        eapply (IHx (n - 1)); [lia|lia|].
        intros k Hk.
        specialize (H (k + 1)).
        rewrite testbit_xO in H; [|lia].
        apply H.
        lia.
    + intros n Hn Hx H.
      assert (n = 0 \/ n > 0) as [Hn'|Hn'] by lia.
      * subst n. specialize (H 0).
        rewrite one_spec in H.
        discriminate H.
        reflexivity.
      * replace 1 with (1 ^ n) by (apply Z.pow_1_l; lia).
        split; [lia|].
        apply Z.pow_lt_mono_l; lia.
  - lia.
Qed.

Lemma bound_spec_n : forall x n,
  0 <= n ->
  0 <= x ->
  0 <= x < 2^n <-> (forall k,  n <= k -> Z.testbit x k = false).
Proof.
  split.
  - eapply bound_spec_n_l; eauto.
  - eapply bound_spec_n_r; eauto.
Qed.

Lemma bound_spec : forall x,
  0 <= x ->
  0 <= x < 256 <-> (forall k,  8 <= k -> Z.testbit x k = false).
Proof.
  intros x Hx.
  eapply (bound_spec_n x 8); eauto.
  lia.
Qed.

Lemma lor_bound_r:
  forall n m x y,
    0 <= n <= m ->
    0 <= x < 2 ^ n ->
    0 <= y < 2 ^ m ->
    0 <= Z.lor x y < 2 ^ m.
Proof.
  intros until y.
  intros Hnm Hx Hy.
  generalize Hx Hy.
  do 2 (rewrite bound_spec_n; [|lia|lia]).
  rewrite bound_spec_n; [|lia|].
  intros Hx' Hy' i Hi.
  rewrite Z.lor_spec.
  specialize (Hx' i).
  specialize (Hy' i).
  rewrite Hx'; [|lia].
  rewrite Hy'; [|lia].
  lia.
  apply Z.lor_nonneg.
  split; lia.
Qed.

Lemma lor_bound_l:
  forall n m x y,
    0 <= n <= m ->
    0 <= x < 2 ^ m ->
    0 <= y < 2 ^ n ->
    0 <= Z.lor x y < 2 ^ m.
Proof.
  intros until y.
  intros Hnm Hx Hy.
  generalize Hx Hy.
  do 2 (rewrite bound_spec_n; [|lia|lia]).
  rewrite bound_spec_n; [|lia|].
  intros Hx' Hy' i Hi.
  rewrite Z.lor_spec.
  specialize (Hx' i).
  specialize (Hy' i).
  rewrite Hx'; [|lia].
  rewrite Hy'; [|lia].
  lia.
  apply Z.lor_nonneg.
  split; lia.
Qed.

Lemma lor_bound_n:
  forall n x y,
    0 <= n ->
    0 <= x < 2 ^ n ->
    0 <= y < 2 ^ n ->
    0 <= Z.lor x y < 2 ^ n.
Proof.
  intros until y.
  intros Hn Hx Hy.
  generalize Hx Hy.
  do 2 (rewrite bound_spec_n; [|lia|lia]).
  rewrite bound_spec_n; [|lia|].
  intros Hx' Hy' i Hi.
  rewrite Z.lor_spec.
  specialize (Hx' i).
  specialize (Hy' i).
  rewrite Hx'; [|lia].
  rewrite Hy'; [|lia].
  lia.
  apply Z.lor_nonneg.
  split; lia.
Qed.

Lemma land_bound_n:
  forall n x y,
    0 <= n ->
    0 <= x < 2 ^ n ->
    0 <= y < 2 ^ n ->
    0 <= Z.land x y < 2 ^ n.
Proof.
  intros until y.
  intros Hn Hx Hy.
  generalize Hx Hy.
  do 2 (rewrite bound_spec_n; [|lia|lia]).
  rewrite bound_spec_n; [|lia|].
  intros Hx' Hy' i Hi.
  rewrite Z.land_spec.
  specialize (Hx' i).
  specialize (Hy' i).
  rewrite Hx'; [|lia].
  rewrite Hy'; [|lia].
  lia.
  apply Z.land_nonneg.
  left; lia.
Qed.

Lemma lxor_bound_n:
  forall n x y,
    0 <= n ->
    0 <= x < 2 ^ n ->
    0 <= y < 2 ^ n ->
    0 <= Z.lxor x y < 2 ^ n.
Proof.
  intros until y.
  intros Hn Hx Hy.
  generalize Hx Hy.
  do 2 (rewrite bound_spec_n; [|lia|lia]).
  rewrite bound_spec_n; [|lia|].
  intros Hx' Hy' i Hi.
  rewrite Z.lxor_spec.
  specialize (Hx' i).
  specialize (Hy' i).
  rewrite Hx'; [|lia].
  rewrite Hy'; [|lia].
  rewrite Bool.xorb_false_l. reflexivity.
  apply Z.lxor_nonneg.
  split; lia.
Qed.

Lemma int64_modulus_pos:
  0 < Wasm_int.Int64.modulus.
Proof.
  unfold Wasm_int.Int64.modulus.
  unfold Wasm_int.Int64.wordsize.
  unfold Integers.Wordsize_64.wordsize.
  rewrite two_power_nat_equiv.
  lia.
Qed.

Lemma int64_modulus_eq:
  Wasm_int.Int64.modulus = 2 ^ 64.
Proof.
  unfold Wasm_int.Int64.modulus.
  unfold Wasm_int.Int64.wordsize.
  unfold Integers.Wordsize_64.wordsize.
  rewrite two_power_nat_equiv.
  reflexivity.
Qed.

Lemma m1_lt_is_0_le:
  forall x,
    -1 < x <-> 0 <= x.
Proof.
  intros x.
  split; intros H; lia.
Qed.

Lemma land_bound {a b} :
  0 <= a < 256 ->
  0 <= b < 256 ->
  0 <= Z.land a b < 256.
Proof.
  pose proof (land_bound_n 8 a b) as H.
  apply H; lia.
Qed.

Lemma lxor_bound {a b} :
  0 <= a < 256 ->
  0 <= b < 256 ->
  0 <= Z.lxor a b < 256.
Proof.
  pose proof (lxor_bound_n 8 a b) as H.
  apply H; lia.
Qed.

Lemma lor_bound {a b} :
  0 <= a < 256 ->
  0 <= b < 256 ->
  0 <= Z.lor a b < 256.
Proof.
  pose proof (lor_bound_n 8 a b) as H.
  apply H; lia.
Qed.

Lemma land_bound64 {a b} :
  -1 < a <  Wasm_int.Int64.modulus ->
  -1 < b <  Wasm_int.Int64.modulus ->
  -1 < Z.land a b < Wasm_int.Int64.modulus.
Proof.
  pose proof (int64_modulus_pos) as Hmod.
  pose proof (land_bound_n 64 a b) as H.
  rewrite int64_modulus_eq.
  rewrite !m1_lt_is_0_le.
  apply H; lia.
Qed.

Lemma lxor_bound64 {a b} :
  -1 < a <  Wasm_int.Int64.modulus ->
  -1 < b <  Wasm_int.Int64.modulus ->
  -1 < Z.lxor a b < Wasm_int.Int64.modulus.
Proof.
  pose proof (int64_modulus_pos) as Hmod.
  pose proof (lxor_bound_n 64 a b) as H.
  rewrite int64_modulus_eq.
  rewrite !m1_lt_is_0_le.
  apply H; lia.
Qed.

Lemma lor_bound64 {a b} :
  -1 < a <  Wasm_int.Int64.modulus ->
  -1 < b <  Wasm_int.Int64.modulus ->
  -1 < Z.lor a b < Wasm_int.Int64.modulus.
Proof.
  pose proof (int64_modulus_pos) as Hmod.
  pose proof (lor_bound_n 64 a b) as H.
  rewrite int64_modulus_eq.
  rewrite !m1_lt_is_0_le.
  apply H; lia.
Qed.


    Lemma plus_lor_helper : forall a b,
        0 <= a < 256 ->
        Z.land a (Z.shiftl b 8) = 0.
    Proof.
      intros a b abound.
      apply Zbits.equal_same_bits. intros k kbound.
      rewrite Z.land_spec.
      rewrite Z.bits_0.
      destruct (Z.lt_decidable k 8) as [H|H].
      - rewrite Z.shiftl_spec_low by auto.
        rewrite Bool.andb_false_r.
        reflexivity.
      - pose proof (bound_spec a) as Ha.
        destruct Ha as [Ha _]. lia.
        rewrite Ha by lia.
        rewrite Bool.andb_false_l.
        reflexivity.
    Qed.        

    Lemma plus_lor : forall a b,
        0 <= a < 256 ->
        a + Z.shiftl b 8 = Z.lor a (Z.shiftl b 8).
    Proof.
      intros a b abound.
      rewrite Z.add_nocarry_lxor by (auto using plus_lor_helper).
      rewrite Z.lxor_lor by (auto using plus_lor_helper).
      reflexivity.
    Qed.

    Lemma plus_lor_helper_n : forall n a b,
        0 <= n ->
        0 <= a < 2^n ->
        Z.land a (Z.shiftl b n) = 0.
    Proof.
      intros n a b nbound abound.
      apply Zbits.equal_same_bits. intros k kbound.
      rewrite Z.land_spec.
      rewrite Z.bits_0.
      destruct (Z.lt_decidable k n) as [H|H].
      - rewrite Z.shiftl_spec_low by auto.
        rewrite Bool.andb_false_r.
        reflexivity.
      - pose proof (bound_spec_n a n) as Ha.
        destruct Ha as [Ha _]. lia. lia.
        rewrite Ha by lia.
        rewrite Bool.andb_false_l.
        reflexivity.
    Qed.   

    Lemma plus_lor_n : forall n a b,
        0 <= n ->
        0 <= a < 2^n ->
        a + Z.shiftl b n = Z.lor a (Z.shiftl b n).
    Proof.
      intros n a b nbound abound.
      rewrite Z.add_nocarry_lxor by (auto using plus_lor_helper_n).
      rewrite Z.lxor_lor by (auto using plus_lor_helper_n).
      reflexivity.
    Qed.
    
    Lemma land_compose : forall a b x y,
        0 <= a < 256 ->
        0 <= x < 256 ->
        Z.land (Z.lor a (Z.shiftl b 8))
               (Z.lor x (Z.shiftl y 8))
        = Z.lor (Z.land a x) (Z.shiftl (Z.land b y) 8).
    Proof.
      intros a b x y a_bound x_bound.
      rewrite Z.shiftl_land.
      apply Zbits.equal_same_bits.
      intros k krange.
      rewrite !Z.land_spec.
      rewrite !Z.lor_spec.
      rewrite !Z.land_spec.
      destruct (Z.testbit a k) eqn:?; destruct (Z.testbit (Z.shiftl b 8) k) eqn:?;
        destruct (Z.testbit x k) eqn:?; destruct (Z.testbit (Z.shiftl y 8) k) eqn:?; simpl; auto.
      - destruct (Z.lt_decidable k 8) as [H|H].
        + rewrite Z.shiftl_spec_low in Heqb3 by auto.
          congruence.
        + pose proof (bound_spec a) as Ha.
          destruct Ha as [Ha _]. lia.
          rewrite Ha  in Heqb0 by lia.
          congruence.
      -  destruct (Z.lt_decidable k 8) as [H|H].
        + rewrite Z.shiftl_spec_low in Heqb1 by auto.
          congruence.
        + pose proof (bound_spec x) as Hx.
          destruct Hx as [Hx _]. lia.
          rewrite Hx  in Heqb2 by lia.
          congruence.
    Qed.

    Lemma lxor_compose : forall a b x y,
        0 <= a < 256 ->
        0 <= x < 256 ->
        Z.lxor (Z.lor a (Z.shiftl b 8))
               (Z.lor x (Z.shiftl y 8))
        = Z.lor (Z.lxor a x) (Z.shiftl (Z.lxor b y) 8).
    Proof.
      intros a b x y a_bound x_bound.
      rewrite Z.shiftl_lxor.
      apply Zbits.equal_same_bits.
      intros k krange.
      rewrite !Z.lxor_spec.
      rewrite !Z.lor_spec.
      rewrite !Z.lxor_spec.
      pose proof (bound_spec a) as Ha. destruct Ha as [Ha _]. lia.
      pose proof (bound_spec x) as Hx. destruct Hx as [Hx _]. lia.
      destruct (Z.testbit a k) eqn:?; destruct (Z.testbit (Z.shiftl b 8) k) eqn:?;
        destruct (Z.testbit x k) eqn:?; destruct (Z.testbit (Z.shiftl y 8) k) eqn:?; simpl; auto.
      - destruct (Z.lt_decidable k 8) as [H|H].
        + rewrite Z.shiftl_spec_low in * by auto.
          congruence.
        + rewrite Ha in * by lia.
          rewrite Hx  in * by lia.
          congruence.
      -  destruct (Z.lt_decidable k 8) as [H|H].
        + rewrite Z.shiftl_spec_low in * by auto.
          congruence.
        + rewrite Ha in * by lia.
          rewrite Hx in * by lia.
          congruence.
      -  destruct (Z.lt_decidable k 8) as [H|H].
        + rewrite Z.shiftl_spec_low in * by auto.
          congruence.
        + rewrite Ha in * by lia.
          rewrite Hx in * by lia.
          congruence.
      -  destruct (Z.lt_decidable k 8) as [H|H].
        + rewrite Z.shiftl_spec_low in * by auto.
          congruence.
        + rewrite Ha in * by lia.
          rewrite Hx in * by lia.
          congruence.
      -  destruct (Z.lt_decidable k 8) as [H|H].
        + rewrite Z.shiftl_spec_low in * by auto.
          congruence.
        + rewrite Ha in * by lia.
          rewrite Hx  in * by lia.
          congruence.
      -  destruct (Z.lt_decidable k 8) as [H|H].
        + rewrite Z.shiftl_spec_low in * by auto.
          congruence.
        + rewrite Ha in * by lia.
          rewrite Hx in * by lia.
          congruence.
    Qed.

    Lemma lor_compose : forall a b x y,
        0 <= a < 256 ->
        0 <= x < 256 ->
        Z.lor (Z.lor a (Z.shiftl b 8))
               (Z.lor x (Z.shiftl y 8))
        = Z.lor (Z.lor a x) (Z.shiftl (Z.lor b y) 8).
    Proof.
      intros a b x y a_bound x_bound.
      rewrite Z.shiftl_lor.
      apply Zbits.equal_same_bits.
      intros k krange.
      rewrite !Z.lor_spec.
      destruct (Z.testbit a k) eqn:?; destruct (Z.testbit (Z.shiftl b 8) k) eqn:?;
        destruct (Z.testbit x k) eqn:?; destruct (Z.testbit (Z.shiftl y 8) k) eqn:?; simpl; auto.
    Qed.

    Lemma land_ones_high : forall x n,
        0 <= n ->
        Z.land (Z.shiftl x n) (Z.ones n) = 0.
    Proof.
      intros.
      apply IntegerFunctions.zero_spec.
      intros b Hb.
      rewrite Z.land_spec.
      destruct (Z_le_gt_dec n b).
      -
        rewrite Z.shiftl_spec_high by lia.
        rewrite Z.ones_spec_high by lia.
        rewrite Bool.andb_comm.
        reflexivity.
      - rewrite Z.ones_spec_low by lia.
        rewrite Z.shiftl_spec_low by lia.
        reflexivity.
    Qed.

Lemma not_is_true : forall b,  ~ is_true b <-> b = false.
Proof.
  destruct b; unfold is_true; simpl.
  - split; auto; congruence.
  - split; auto; congruence.
Qed.

Section power_index_to_bits_leading_zeros.
  Context (y : nat) (l : list Z).
  Hypothesis Hnin : forall y', (y < y')%nat -> ~ In (Z.of_nat y') l.
  Hypothesis Hin : In (Z.of_nat y) l.
  
  Lemma power_index_to_bits_leading_zeros : forall (c : nat),
      Wasm_int.Int64.power_index_to_bits (c + S y) l
      = repeat false c ++ true :: Wasm_int.Int64.power_index_to_bits y l.
  Proof.
    induction c.
    - simpl.
      rewrite <- (@common.List_In_in_mem common.Z_eqType (Z.of_nat y) l) in Hin.
      unfold is_true in Hin.
      simpl in Hin.
      rewrite Hin.
      reflexivity.
    - simpl.
      specialize (Hnin (c + S y)).
      specialize (Hnin (ltac:(lia))).
      rewrite <- (@common.List_In_in_mem common.Z_eqType (Z.of_nat (c + S y)) l) in Hnin.
      rewrite not_is_true in Hnin.
      simpl in Hnin.
      rewrite Hnin.
      rewrite IHc.
      reflexivity.
  Qed.
End power_index_to_bits_leading_zeros.    

Lemma find_leading_zeros : forall (c: nat) (l: list bool),
    seq.find (fun b : eqtype.Equality.sort eqtype.bool_eqType => eqtype.eq_op b true)
      (repeat false c ++ true :: l)
    = c.
Proof.
  induction c.
  - simpl; intros; reflexivity.
  - simpl; intros.
    rewrite IHc.
    reflexivity.
Qed.


Lemma Zdiv_mul_mono: forall z,
    0 <= z ->
    z / 2 * 2 <= z.
Proof.
  intros z Hrange.
  cut (0 <= z - z / 2 * 2).
  lia.
  rewrite <- Zmod_eq by lia.
  apply Z_mod_lt.
  lia.
Qed.
  
Lemma one_bits_top_bit1' : forall n x y i z,
    0 <= y < Z.of_nat n ->
    0 <= z < 2^y ->
    x = 2^y + z ->
    In (y+i) (Zbits.Z_one_bits n x i).
Proof.
  induction n.
  - intros x y i z Hy_range Hz_range Hx.
    simpl in Hy_range. lia.
  -  intros x y i z Hy_range Hz_range Hx.
     simpl.
     destruct (Z.eq_dec y 0).
     + rewrite e in *. change (2^0) with 1 in *.
        assert (x=1) by lia.
        clear Hx. subst.
        simpl.
        eauto.
     + replace y with ((y-1)+1) in * by lia. 
      rewrite (Zdiv2_odd_eqn x) in Hx.
      rewrite (Zdiv2_odd_eqn z) in Hx.

      assert (Hoddness: Z.odd x = Z.odd z).
      {
        replace ( 2 ^ (y - 1 + 1) + (2 * Z.div2 z + (if Z.odd z then 1 else 0)))
          with  ((2 ^ (y - 1 + 1) + 2 * Z.div2 z) + (if Z.odd z then 1 else 0)) in Hx by lia.
        rewrite Z.pow_add_r in Hx by lia.
        replace (2 ^ (y - 1) * 2 ^ 1 + 2 * Z.div2 z)
          with  (2*(2 ^ (y - 1) + Z.div2 z)) in Hx by lia.
        assert (Hc: Z.odd( 2 * Z.div2 x + (if Z.odd x then 1 else 0)) = Z.odd (2 * (2 ^ (y - 1) + Z.div2 z) + (if Z.odd z then 1 else 0))) by congruence.
        rewrite Z.add_comm in Hc.
        rewrite (Z.add_comm _ (if Z.odd z then 1 else 0)) in Hc.
        rewrite !Z.odd_add_mul_2 in Hc.
        destruct (Z.odd x); destruct (Z.odd z); simpl in Hc; congruence.
      }        
      rewrite <- Hoddness in Hx. clear Hoddness.
      assert (Hx' : 2 * Z.div2 x = 2 ^ (y - 1 + 1) + 2 * Z.div2 z) by lia. clear Hx.
      rewrite Z.pow_add_r in Hx' by lia.
      replace (2 ^ (y - 1) * 2 ^ 1 + 2 * Z.div2 z) with (2 * (2 ^ (y - 1) + Z.div2 z)) in Hx' by lia.
      assert (Hx : Z.div2 x = (2 ^ (y - 1) + Z.div2 z)) by lia. clear Hx'.
      replace (y - 1 + 1 + i) with (y - 1 + (i+1)) by lia.
      destruct (Z.odd x).
       * right.
         eapply IHn with (z := (Z.div2 z)).
         ** lia.
         ** split.
           *** apply Z.div2_nonneg; lia.
           *** apply Zmult_lt_reg_r with 2.
               lia.
               rewrite Zdiv2_div.
               replace (2 ^ (y - 1) * 2) with (2 ^ (y - 1 +1)).
               2: { change 2 with (2^1) at 3.
                    rewrite <- Z.pow_add_r by lia.
                    reflexivity. }
               assert (Hblah := Zdiv_mul_mono z ltac:(lia)).
               lia.
         ** lia.
       * eapply IHn with (z := (Z.div2 z)).
         ** lia.
         ** split.
           *** apply Z.div2_nonneg; lia.
           *** apply Zmult_lt_reg_r with 2.
               lia.
               rewrite Zdiv2_div.
               replace (2 ^ (y - 1) * 2) with (2 ^ (y - 1 +1)).
               2: { change 2 with (2^1) at 3.
                    rewrite <- Z.pow_add_r by lia.
                    reflexivity. }
               assert (Hblah := Zdiv_mul_mono z ltac:(lia)).
               lia.
         ** lia.
Qed.

Lemma one_bits_top_bit1 : forall n x y z,
    0 <= y < Z.of_nat n ->
    0 <= z < 2^y ->
    x = 2^y + z ->
    In y (Zbits.Z_one_bits n x 0).
Proof.
  intros.
  replace y with (y+0) by lia.
  eapply one_bits_top_bit1'; eauto.
Qed.

Lemma odd_nonzero : forall x,
    0 <= x ->
    Z.odd x = true -> 1 <= x.
Proof.
  intros x Hrange Hodd.
  destruct (Z.eq_dec x 0).
  - subst. simpl in *. congruence.
  - lia.
Qed.

Lemma Z_one_bits_range':
  forall (n : nat) (x j i : Z), In i (Zbits.Z_one_bits n x j) -> j <= i.
Proof.
  induction n.
  - simpl.
    intros.
    tauto.
  - simpl. intros.
    destruct (Z.odd x).
    + destruct H as [H | H].
      * subst.  lia.
      * specialize (IHn (Z.div2 x) (j+1) i H). lia.
    + specialize (IHn (Z.div2 x) (j+1) i H). lia.
Qed.


Lemma shift_once : forall x s,
   (Z.shiftl x (Z.succ (Z.of_nat s))) = 2 * (Z.shiftl x (Z.of_nat s)).
Proof.
  intros x s.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  replace (Z.succ (Z.of_nat s)) with (1 + Z.of_nat s) by lia.
  rewrite Zpower_exp by lia.
  lia.
Qed.  

Opaque Z.of_nat.

Lemma one_bits_shift : forall (n s : nat) (x i :Z),
    Zbits.Z_one_bits (s+n) (Z.shiftl x (Z.of_nat s)) i = Zbits.Z_one_bits n x (Z.of_nat s + i).
Proof.
  induction s; intros.
  - reflexivity.
  - Opaque Z.of_nat.
    simpl.
    rewrite Nat2Z.inj_succ.
    rewrite shift_once.
    replace (Z.odd (2 * Z.shiftl x (Z.of_nat s))) with false.
    2: {
      rewrite Z.odd_mul.
      rewrite Z.odd_2.
      reflexivity.
    }
    replace (Z.div2 (2 * Z.shiftl x (Z.of_nat s))) with (Z.shiftl x (Z.of_nat s)).
    2: {
      clear IHs.
      generalize  (Z.shiftl x (Z.of_nat s)).
      intros z.
      rewrite Zdiv2_div.
      rewrite Z.mul_comm.
      rewrite Z.div_mul by lia.
      lia.
    }
    rewrite IHs.
    replace  (Z.succ (Z.of_nat s) + i) with (Z.of_nat s + (i + 1)) by lia.
    reflexivity.
Qed.

Lemma testbit_div2 : forall x b,
   0 <= b ->
   Z.testbit x (b+1) = Z.testbit (Z.div2 x) b.
Proof.
  intros x b Hrange.
  replace (b+1) with (Z.succ b) by lia.
  destruct (Zeven_odd_dec x) as [Heven |Hodd].
  - rewrite (Zeven_div2 x Heven).
    rewrite Z.testbit_even_succ by lia.
    rewrite <- (Zeven_div2 x Heven).
    reflexivity.
  - rewrite (Zodd_div2 x Hodd).
    rewrite Z.testbit_odd_succ by lia.
    rewrite <- (Zodd_div2 x Hodd).
    reflexivity.
Qed.
  
Lemma one_bits_testbit : forall n b x i,
     0 <= b < Z.of_nat n -> 
    In (b+i) (Zbits.Z_one_bits n x i) <-> Z.testbit x b = true. 
Proof.
  induction n.
  - intros. lia. (* from H *)
  - intros.
    simpl in *.
    destruct (Z.eq_dec b 0).
    + subst.
      simpl.
      destruct (Z.odd x) eqn:Hodd.
      * simpl. tauto.
      * split; [|congruence].
        intros Hin.
        assert (Hle := Z_one_bits_range' _ _ _ _ Hin).
        lia.
    + destruct (Z.odd x). (* Same reasoning in both branches, but we need to simplify the if. *)
      * specialize (IHn (b-1) (Z.div2 x) (i+1) ltac:(lia)).
        replace b with ((b-1)+1) by lia.
        rewrite testbit_div2 by lia.
        replace ((b - 1 + (i + 1))) with (b+i) in IHn by lia.
        split.
        ** destruct 1; [lia|].
           replace ((b - 1 + 1 + i)) with (b+i) in H0 by lia.
           rewrite IHn in H0.
           auto.
        ** rewrite <- IHn.          
           replace ((b - 1 + 1 + i)) with (b+i) by lia.
           intros H0.
           right.
           auto.
      * specialize (IHn (b-1) (Z.div2 x) (i+1) ltac:(lia)).
        replace b with ((b-1)+1) by lia.
        rewrite testbit_div2 by lia.
        replace ((b - 1 + (i + 1))) with (b+i) in IHn by lia.
        split.
        ** replace ((b - 1 + 1 + i)) with (b+i)  by lia.
           rewrite IHn.
           auto.
        ** rewrite <- IHn.          
           replace ((b - 1 + 1 + i)) with (b+i) by lia.
           auto.
Qed.


Lemma popcnt_step : forall n x,
    0 <= Z.of_nat n < Z.of_nat Wasm_int.Int64.wordsize ->    
    (ssrnat.nat_of_bool
       (@eqtype.eq_op eqtype.bool_eqType
          (ssrbool.in_mem (Z.of_nat n) 
                       (@ssrbool.mem  Z (seq.seq_predType common.Z_eqType)
          (Zbits.Z_one_bits Wasm_int.Int64.wordsize x 0))) true))
    = if (Z.testbit x (Z.of_nat n)) then 1%nat else 0%nat.

Proof.
  intros n x Hrange.
  destruct (ssrbool.in_mem (Z.of_nat n) (@ssrbool.mem   Z (seq.seq_predType common.Z_eqType) (Zbits.Z_one_bits Wasm_int.Int64.wordsize x 0)))
    eqn: Hin.
  - change Z with  (eqtype.Equality.sort common.Z_eqType) in *.
    rewrite  (@common.List_In_in_mem common.Z_eqType (Z.of_nat n)  (Zbits.Z_one_bits Wasm_int.Int64.wordsize x 0)) in Hin.
    replace (Z.of_nat n) with (Z.of_nat n + 0) in Hin by lia.
    rewrite one_bits_testbit in Hin by assumption.
    rewrite Hin.
    reflexivity.
  - change Z with  (eqtype.Equality.sort common.Z_eqType) in *.
    rewrite <- not_is_true in Hin.
    rewrite  (@common.List_In_in_mem common.Z_eqType (Z.of_nat n)  (Zbits.Z_one_bits Wasm_int.Int64.wordsize x 0)) in Hin.
    replace (Z.of_nat n) with (Z.of_nat n + 0) in Hin by lia.
    rewrite one_bits_testbit in Hin by assumption.
    rewrite (Bool.not_true_is_false _ Hin).
    reflexivity.
Qed.

Lemma one_bits_small : forall n m i b, 
 0 <= b < 2 ^ (Z.of_nat n) ->
 Zbits.Z_one_bits n b i = Zbits.Z_one_bits (n+m) b i.
Proof.
  induction n.
  - intros m i b Hrange.
    simpl.
    change ( 2 ^ Z.of_nat 0) with 1 in Hrange.
    replace b with 0 by lia.
    rewrite Zbits.Z_one_bits_zero.
    reflexivity.
  - intros m i b Hrange.
    simpl.
    assert (Hrange' :  0 <= (Z.div2 b) < 2 ^ Z.of_nat n).
    {
      replace (Z.of_nat (S n)) with (1+ Z.of_nat n) in Hrange by lia.
      rewrite Z.pow_add_r in Hrange by lia.
      change ( 2 ^ 1) with 2 in Hrange.
      rewrite Zdiv2_div.
      split.
      - apply Z_div_nonneg_nonneg; lia.
        apply Z.div_lt_upper_bound; lia.
    }
    destruct (Z.odd b).
    + rewrite (IHn m (i+1) (Z.div2 b) Hrange').
      reflexivity.
    + rewrite (IHn m (i+1) (Z.div2 b) Hrange').
      reflexivity.
Qed.    

Lemma size_filter : forall  (n : Z),
    0 <= n ->
    forall (l : list Z),
    seq.size (seq.filter (fun b : Z => ((0 <=? b) && (b <? n+1))%bool) l)
    =
    (seq.size (seq.filter (fun b : Z => (b =? n)%bool)%Z l)
    + seq.size (seq.filter (fun b : Z => ((0 <=? b) && (b <? n))%bool)%Z l))%nat.
Proof.
  intros n Hrange.
  induction l.
  - reflexivity.
  - destruct (Z.eq_dec a n).
    + subst.
      simpl.
      replace (n =? n) with true by (rewrite Z.eqb_refl; reflexivity).
      rewrite Zle_imp_le_bool by lia.
      rewrite Z.ltb_irrefl.
      rewrite Zaux.Zlt_bool_true by lia.
      simpl.
      rewrite IHl.
      reflexivity.
    + simpl.
      replace (a =? n) with false.
      2: {
        symmetry.
        rewrite Z.eqb_neq.
        lia.
      }
      replace (a <? n + 1) with (a <? n).
      2: {
        destruct  (a <? n) eqn:H.
        - rewrite Z.ltb_lt in H.
          symmetry.
          rewrite Z.ltb_lt.
          lia.
        - rewrite Z.ltb_ge in H.
          symmetry.
          rewrite Z.ltb_ge.          
          lia.
      }
      destruct ((0 <=? a) && (a <? n))%bool.
      * simpl.
        rewrite IHl.
        lia.
      * rewrite IHl.
        lia.
Qed.


Lemma one_bits_nodup : forall n y i,
  (forall x, (seq.size (seq.filter (fun b : Z => (b =? x)%Z) (Zbits.Z_one_bits n y i))
              = if (@ssrbool.in_mem Z x (@ssrbool.mem Z (seq.seq_predType common.Z_eqType) (Zbits.Z_one_bits n y i))) then 1%nat else 0%nat)).
Proof.
  induction n.
  - intros. reflexivity.
  - intros.  
    simpl.
    destruct (Z.odd y).
    + simpl.
      destruct (Z.eq_dec i x).
      * subst.
        rewrite Z.eqb_refl.
        simpl.
        rewrite IHn.
        replace  (ssrbool.in_mem x (@ssrbool.mem  Z (seq.seq_predType common.Z_eqType) (Zbits.Z_one_bits n (Z.div2 y) (x + 1))))
          with false.
        2: {
          symmetry.
          rewrite <- not_is_true.
          rewrite (@common.List_In_in_mem common.Z_eqType x (Zbits.Z_one_bits n (Z.div2 y) (x + 1))).
          intros H.
          apply Z_one_bits_range' in H.
          lia.
        }

        replace ( ssrbool.in_mem x (@ssrbool.mem Z (seq.seq_predType common.Z_eqType)  (x :: Zbits.Z_one_bits n (Z.div2 y) (x + 1)))) with true.
        2: {
          symmetry.
          apply seq.mem_head.
        }
        reflexivity.
      * replace ( i =? x) with false.
        2: { symmetry.
             rewrite Z.eqb_neq.
             lia. }
        rewrite IHn.

        change Z with (eqtype.Equality.sort common.Z_eqType).
        rewrite (@seq.in_cons common.Z_eqType i (Zbits.Z_one_bits n (Z.div2 y) (i + 1)) x).
        replace (@eqtype.eq_op common.Z_eqType x i) with false.
        2: {
          unfold  eqtype.eq_op.
          simpl.
          destruct  (Coqlib.zeq x i). congruence. reflexivity.
        }
        reflexivity.
    + rewrite IHn.
      reflexivity.
Qed.      

Lemma popcnt_is_length_helper : forall l,
  (forall x, (seq.size (seq.filter (fun b : Z => (b =? x)%Z) l)
   = if (@ssrbool.in_mem Z x (@ssrbool.mem Z (seq.seq_predType common.Z_eqType) l)) then 1%nat else 0%nat)) ->  
  forall n,
    seq.count (fun b : eqtype.Equality.sort eqtype.bool_eqType => eqtype.eq_op b true)
       (Wasm_int.Int64.power_index_to_bits n l) =  (seq.size (seq.filter (fun b => Z.leb 0 b && Z.ltb b (Z.of_nat n)) l))%bool.
Proof.
  intros l Hnodup.
  induction n.
  - simpl.
    rewrite common.filter_none.
    + reflexivity.
    + apply seq.allT.
      intros x.
      destruct (0 <=? x) eqn:Hlt.
      * rewrite Z.leb_le in Hlt.
        replace  (x <? Z.of_nat 0) with false.
        2: {
          symmetry.
          apply Zaux.Zlt_bool_false.
          lia.
        }
        simpl.
        constructor.
      * simpl.
        constructor.
  - simpl.
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite size_filter by lia.
    change ((eqtype.Equality.sort eqtype.bool_eqType)) with bool in IHn.
    rewrite IHn.
    rewrite Hnodup.
    destruct (@ssrbool.in_mem Z (Z.of_nat n) (@ssrbool.mem Z (seq.seq_predType common.Z_eqType) l)).
    + simpl. reflexivity.
    + reflexivity.
Qed.   

Lemma popcnt_is_length_helper2 : forall n i j x,
  j <= i -> 
  seq.size (seq.filter (fun b => ((j <=? b) && (b <? i+Z.of_nat n))%bool) (Zbits.Z_one_bits n x i))
    =
  length (Zbits.Z_one_bits n x i).
Proof.
  induction n.
  - reflexivity.
  - simpl.
    intros.
    specialize (IHn (i+1) (j) (Z.div2 x) ltac:(lia)).
    replace (i + 1 + Z.of_nat n) with (i + Z.of_nat (S n)) in IHn by lia.          
    destruct (Z.odd x).
    + simpl.
      rewrite Zle_imp_le_bool by lia.
      rewrite Zaux.Zlt_bool_true by lia.
      simpl.
      rewrite IHn.
      reflexivity.
    + rewrite IHn.
      reflexivity.      
Qed.    
      
Lemma popcnt_is_length : forall x, 
 popcnt x = Z.of_nat (List.length (Zbits.Z_one_bits Wasm_int.Int64.wordsize x 0)).
Proof.
  unfold popcnt.
  intros x.
  f_equal.
  change  Wasm_int.Int64.wordsize  with (64%nat).
  rewrite popcnt_is_length_helper.
  2: {
    apply one_bits_nodup.
  }
  replace (Z.of_nat 64) with (0 + Z.of_nat 64) by lia.
  rewrite (popcnt_is_length_helper2) by lia. 
  reflexivity.
Qed.

Lemma one_bits_length_index : forall n x i j,
    length (Zbits.Z_one_bits n x i) = length (Zbits.Z_one_bits n x j).
Proof.
  induction n.
  - reflexivity.
  - simpl. intros.
    destruct (Z.odd x); simpl; rewrite (IHn _ (i+1) (j+1)); reflexivity.
Qed.

Lemma popcnt_shiftl8 : forall b, 
 0 <= b < 2 ^ 56 ->
 popcnt b = popcnt (Z.shiftl b 8).
Proof.
  intros b Hrange.
  rewrite !popcnt_is_length.
  change ( Wasm_int.Int64.wordsize ) with (64%nat).
  change  (Zbits.Z_one_bits 64 b 0) with  (Zbits.Z_one_bits (56+8) b 0).
  rewrite <- (one_bits_small (56%nat) 8 0 b Hrange).
  change (64%nat) with ((8+56) %nat).
  change (Z.shiftl b 8) with (Z.shiftl b (Z.of_nat 8)).
  rewrite one_bits_shift.
  rewrite (one_bits_length_index _ _ _  (Z.of_nat 8 + 0)).
  reflexivity.
Qed.
      
Lemma of_nat_add : forall (a b c:nat),
    (a = b + c)%nat <-> Z.of_nat a = Z.of_nat b + Z.of_nat c.
Proof.    
split; lia.
Qed.

Lemma popcnt_compose_lor' :
  forall x y : Z,
    Z.land x y = 0 ->
    forall n,
      (n <=  Wasm_int.Int64.wordsize)%nat ->
    (seq.count (fun b : eqtype.Equality.sort eqtype.bool_eqType => eqtype.eq_op b true)
       (Wasm_int.Int64.power_index_to_bits n
          (Zbits.Z_one_bits Wasm_int.Int64.wordsize (Z.lor x y) 0))) =
    ((seq.count (fun b : eqtype.Equality.sort eqtype.bool_eqType => eqtype.eq_op b true)
       (Wasm_int.Int64.power_index_to_bits n
          (Zbits.Z_one_bits Wasm_int.Int64.wordsize x 0))) +
    (seq.count (fun b : eqtype.Equality.sort eqtype.bool_eqType => eqtype.eq_op b true)
       (Wasm_int.Int64.power_index_to_bits n
          (Zbits.Z_one_bits Wasm_int.Int64.wordsize y 0)))) %nat.
Proof.
  intros x y Hland.
  induction n.
  - intros.
    simpl.
    lia.
  - Opaque Zbits.Z_one_bits.
    simpl.
    intros Hbound.

    rewrite !popcnt_step by lia.

    rewrite Z.lor_spec.
    destruct (Z.testbit x (Z.of_nat n)) eqn:Hxbit;
    destruct (Z.testbit y (Z.of_nat n)) eqn:Hybit.
    + (* impossible by Hland. *)
      assert (Hland' : (Z.testbit x (Z.of_nat n) && Z.testbit y (Z.of_nat n) = true)%bool).
      {
        rewrite Hxbit, Hybit; reflexivity.
      }
      rewrite <- Z.land_spec in Hland'.
      rewrite Hland in Hland'.
      rewrite Z.bits_0 in Hland'.
      congruence.
    + simpl.
      rewrite ssrnat.add0n.
      rewrite ssrnat.add1n.
      f_equal.
      apply IHn.
      lia.
    + simpl.
      rewrite !ssrnat.add0n.
      rewrite !ssrnat.add1n.
      (* No idea why "rewrite" could not do this: *)
     replace ((ssrnat.addn 1
          (@seq.count bool (fun b : bool => @eqtype.eq_op eqtype.bool_eqType b true)
             (Wasm_int.Int64.power_index_to_bits n (Zbits.Z_one_bits Wasm_int.Int64.wordsize y 0))))%nat)
       with
       ((S
          (@seq.count bool (fun b : bool => @eqtype.eq_op eqtype.bool_eqType b true)
             (Wasm_int.Int64.power_index_to_bits n (Zbits.Z_one_bits Wasm_int.Int64.wordsize y 0))))%nat).
     2:{ reflexivity. }

(*Set Printing Implicit. *)
     replace ( (@seq.count bool (fun b : bool => @eqtype.eq_op eqtype.bool_eqType b true)
     (Wasm_int.Int64.power_index_to_bits n (Zbits.Z_one_bits Wasm_int.Int64.wordsize x 0)) +
   S
     (@seq.count bool (fun b : bool => @eqtype.eq_op eqtype.bool_eqType b true)
        (Wasm_int.Int64.power_index_to_bits n (Zbits.Z_one_bits Wasm_int.Int64.wordsize y 0))))%nat)
       with (S (@seq.count bool (fun b : bool => @eqtype.eq_op eqtype.bool_eqType b true)
     (Wasm_int.Int64.power_index_to_bits n (Zbits.Z_one_bits Wasm_int.Int64.wordsize x 0)) +
     (@seq.count bool (fun b : bool => @eqtype.eq_op eqtype.bool_eqType b true)
        (Wasm_int.Int64.power_index_to_bits n (Zbits.Z_one_bits Wasm_int.Int64.wordsize y 0))))%nat)
       by lia.
     f_equal.
     apply IHn.
     lia.
    + simpl.
      rewrite !ssrnat.add0n.
      apply IHn.
      lia.
Qed.
      
Lemma popcnt_compose_lor :
  forall x y,
    Z.land x y = 0 ->
    popcnt (Z.lor x y) = popcnt x + popcnt y.
Proof.
  intros x y Hland.
  unfold popcnt.
  rewrite <- of_nat_add.
  apply popcnt_compose_lor'; auto; lia.
Qed.

Lemma popcnt_compose :  forall a b,
    0 <= a < 256 ->
    0 <= b < 2^56 ->
    popcnt (Z.lor a (Z.shiftl b 8)) = popcnt a + popcnt b.
Proof.
  intros a b Ha_range Hb_range.
  rewrite popcnt_compose_lor by (auto using  plus_lor_helper).
  rewrite <- popcnt_shiftl8 by auto.
  reflexivity.
Qed.
