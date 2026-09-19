(* Copyright (C) CertiK 2024-2026 *)

From Coq Require Import Arith ZArith NArith Nnat Psatz List Znumtheory ZBits.
From Flocq Require Import Zaux.
From mathcomp.ssreflect Require Import seq ssreflect eqtype.

(* Notation overridden of mathcomp to Coq *)
Set Warnings "-notation-overridden".
From mathcomp.ssreflect Require Import ssrnat ssrbool ssrfun.
Set Warnings "+notation-overridden".

From mathcomp Require Import lra zify.

Require Import CommonSeq.

(** * ssr <-> Coq adaptation
  Lemmas used to provide compatibility between ssr and Coq libraries.
*)

Lemma ssrnat_nat_add:
  forall a b, (a + b)%coq_nat = (a + b)%nat.
Proof.
  intros.
  lia.
Qed.

Lemma ssrnat_nat_sub:
  forall a b, (a - b)%coq_nat = (a - b)%nat.
Proof.
  intros.
  lia.
Qed.

Lemma ssrnat_nat_mul:
  forall a b, (a * b)%coq_nat = (a * b)%nat.
Proof.
  intros.
  lia.
Qed.

Lemma ssrnat_nat_N_id:
  forall n, ssrnat.nat_of_bin (N.of_nat n) = n.
Proof.
  intros.
  lia.
Qed.

Lemma N2nat_id:
  forall n, nat_of_bin n = N.to_nat n.
Proof.
  intros. lia.
Qed.

Lemma ssrnat_Z_N_nat:
  forall n,
    nat_of_bin (Z.to_N n) = Z.to_nat n.
Proof. lia. Qed.


(* numerics *)
Open Scope Z_scope.

Lemma Zof_nat_add_inj:
  forall (n m: nat),
    Z.of_nat n + Z.of_nat m = Z.of_nat (n + m).
Proof.
  intros n m.
  lia.
Qed.

Lemma two_power_n : forall n: Z, 
  n > 0 ->
  2 ^ n = two_power_pos (Z.to_pos n).
Proof.
  intros.
  rewrite two_power_pos_equiv.
  rewrite Z2Pos.id.
  reflexivity.
  lia.
Qed.

Lemma two_power_n' : forall (n: positive), 
  Z.pos n > 0 ->
  2 ^ (Z.pos n) = two_power_pos n.
Proof.
  intros.
  rewrite two_power_pos_equiv.
  reflexivity.
Qed.

Lemma two_power_nat_divide:
  forall (n m: nat),
    (n <= m)%nat ->
    (two_power_nat n | two_power_nat m)%Z.
Proof.
  intros until m. intros Hnm.
  repeat rewrite two_power_nat_equiv.
  assert (m = n + (m - n))%nat as Hm by lia.
  rewrite Hm.
  rewrite <- Zof_nat_add_inj.
  rewrite Z.pow_add_r; [|lia|lia].
  apply Z.divide_factor_l.
Qed.

Lemma mod_pow2_range:
  forall val n,
    0 <= n ->
    0 <= val ->
    val mod 2 ^ n < 2 ^ n.
Proof.
  intros until n. intros Hn Hval.
  apply Z_mod_lt.
  lia.
Qed.

Lemma mod_pow2_range':
  forall val n,
    0 <= n ->
    0 <= val ->
    val mod 2 ^ n <= 2 ^ n - 1.
Proof.
  intros until n. intros Hn Hval.
  pose proof (mod_pow2_range val n Hn Hval) as Hmod.
  lia.
Qed.

Lemma mod_sign:
  forall val n,
    0 < n ->
    0 <= val ->
    0 <= val mod n.
Proof.
  intros until n. intros Hn Hval.
  pose proof (Z.mod_pos_bound val n Hn) as Hmod.
  lia.
Qed.

Lemma shift_nat_1:
  forall (a: positive),
    (shift_nat 1 a = 2 * a)%positive.
Proof.
  intros a.
  unfold shift_nat.
  simpl.
  reflexivity.
Qed.

Lemma shiftr_1:
  forall (a: Z),
    (Z.shiftr a 1 = a / 2)%Z.
Proof.
  intros a.
  rewrite Z.shiftr_div_pow2; [|lia].
  replace (2 ^ 1)%Z with 2 by reflexivity.
  lia.
Qed.

Lemma two_power_nat_cons:
  forall (a: Z) (n: nat),
    two_power_nat (n.+1) = 2 * two_power_nat n.
Proof.
  intros.
  unfold two_power_nat.
  replace (n.+1) with (1 + n)%nat by lia.
  rewrite shift_nat_plus.
  rewrite shift_nat_1.
  lia.
Qed.

Lemma two_power_nat_gt0:
  forall (n: nat),
    (0 < two_power_nat n)%Z.
Proof.
  intros.
  rewrite two_power_nat_equiv.
  lia.
Qed.

Lemma mod_two_power_nat_cons:
  forall (a: Z) (n: nat),
    a mod two_power_nat (n.+1) = a mod 2 + 2 * ((a / 2) mod two_power_nat n).
Proof.
  intros a n.
  rewrite two_power_nat_cons.
  erewrite Z.rem_mul_r with (a:=a)(b:=2)(c:=two_power_nat n); eauto.
  - discriminate.
  - apply two_power_nat_gt0.
  - assumption.
Qed.

Lemma mod_mod_lt:
  forall (n: nat) a (m: nat),
    (0 < n < m)%nat ->
    a mod (two_power_nat m) mod (two_power_nat n) = a mod (two_power_nat n).
Proof.
  intros until m. intros Hnm.
  erewrite <- Zmod_div_mod; [reflexivity|..].
  - apply two_power_nat_gt0.
  - apply two_power_nat_gt0.
  - apply two_power_nat_divide.
    lia.
Qed.

Lemma two_power_nat_add:
  forall (n m: nat),
    two_power_nat (n + m) = two_power_nat n * two_power_nat m.
Proof.
  intros.
  repeat rewrite two_power_nat_equiv.
  rewrite <- Zof_nat_add_inj.
  rewrite Z.pow_add_r; lia.
Qed.

Lemma mod_two_power_nat_add:
  forall (a: Z) (n m: nat),
    a mod two_power_nat (m + n) = 
    a mod two_power_nat m + two_power_nat m * ((a / two_power_nat m) mod two_power_nat n).
Proof.
  intros until m.
  rewrite two_power_nat_add.
  erewrite Z.rem_mul_r with (a:=a)(b:=two_power_nat m)(c:=two_power_nat n); eauto.
  - pose proof (two_power_nat_gt0 m) as Hm.
    lia.
  - pose proof (two_power_nat_gt0 n) as Hn.
    lia.
Qed.

Lemma two_power_nat_byte:
  forall (n: nat),
    two_power_nat (8 * n) = 2 ^ (8 * Z.of_nat n).
Proof.
  intros.
  rewrite two_power_nat_equiv.
  lia.
Qed.

Lemma mod_two_power_nat_and_ones:
  forall (a: Z) (n: nat),
    a mod two_power_nat n = Z.land a (two_power_nat n - 1).
Proof.
  intros until n.
  rewrite two_power_nat_equiv.
  replace (2 ^ Z.of_nat n - 1)%Z with (Z.pred (2 ^ Z.of_nat n)) by reflexivity.
  rewrite <- Z.ones_equiv.
  rewrite Z.land_ones.
  reflexivity.
  lia.
Qed.

Lemma div_two_power_nat_shiftr:
  forall (a: Z) (n: nat),
    a / two_power_nat n = Z.shiftr a (Z.of_nat n).
Proof.
  intros until n.
  rewrite two_power_nat_equiv.
  rewrite Z.shiftr_div_pow2; lia.
Qed.

Lemma mul_two_power_nat_shiftl:
  forall (a: Z) (n: nat),
    a * two_power_nat n = Z.shiftl a (Z.of_nat n).
Proof.
  intros until n.
  rewrite two_power_nat_equiv.
  rewrite Z.shiftl_mul_pow2; lia.
Qed.

Lemma div2_range:
  forall val n,
    0 < n ->
    0 <= val < 2 ^ n ->
    0 <= val / 2 < 2 ^ (n - 1).
Proof.
  intros until n. intros Hn Hval.
  split.
  - apply Z.div_pos; lia.
  - assert (val = val mod 2^n).
    {
      rewrite Z.mod_small; lia.
    }
    rewrite H.
    rewrite Z.pow_sub_r; [|lia|lia].
    replace (2 ^ n) with (2 * 2 ^ (n - 1)).
    rewrite Zaux.Zdiv_mod_mult; [|lia|lia].
    replace (2 * 2 ^ (n - 1) / 2 ^ 1) with (2 ^ (n - 1)).
    apply Z.mod_pos_bound.
    - lia.
    - rewrite Z.pow_1_r.
      rewrite Z.mul_comm.
      rewrite Z_div_mult; [|lia].
      reflexivity.
    - rewrite <- Z.pow_succ_r; [|lia].
      replace (Z.succ (n - 1)) with n by lia.
      reflexivity.
Qed.

Lemma shiftr_range':
  forall (m: nat) val n,
    0 <= Z.of_nat m <= n ->
    0 <= val < 2 ^ n ->
    0 <= Z.shiftr val (Z.of_nat m) < 2 ^ (n - (Z.of_nat m)).
Proof.
  induction m.
  - intros until n. intros Hmn Hval.
    rewrite Z.shiftr_0_r.
    replace (n - Z.of_nat 0) with n by lia.
    assumption.
  - intros until n. intros Hmn Hval.
    replace (Z.of_nat m.+1) with (1 + Z.of_nat m)%Z by lia.
    rewrite <- Z.shiftr_shiftr; [|lia].
    replace ((n - (1 + Z.of_nat m))) with ((n - 1) - Z.of_nat m)%Z by lia.
    apply (IHm (Z.shiftr val 1) (n - 1)).
    + lia.
    + split.
      * apply Z.shiftr_nonneg. lia.
      * rewrite Z.shiftr_div_pow2; [|lia].
        rewrite Z.pow_1_r.
        apply div2_range; lia.
Qed.

Lemma shiftr_range:
  forall val m n,
    0 <= m <= n ->
    0 <= val < 2 ^ n ->
    0 <= Z.shiftr val m < 2 ^ (n - m).
Proof.
  intros until n. intros Hmn Hval.
  pose (m' := Z.to_nat m).
  assert (m = Z.of_nat m') as Hm by lia.
  rewrite !Hm.
  apply shiftr_range'; lia.
Qed.

Lemma mul2_range:
  forall val n,
    0 <= n ->
    0 <= val < 2 ^ n ->
    0 <= val * 2 < 2 ^ (n + 1).
Proof.
  intros until n. intros Hn Hval.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - rewrite Z.pow_add_r; [|lia|lia].
    apply Z.mul_lt_mono_pos_r; lia.
Qed.

Lemma shiftl_range':
  forall (m: nat) val n,
    0 <= n ->
    0 <= val < 2 ^ n ->
    0 <= Z.shiftl val (Z.of_nat m) < 2 ^ (n + (Z.of_nat m)).
Proof.
  induction m.
  - intros until n. intros Hn Hval.
    replace (Z.of_nat 0) with 0 by lia.
    rewrite Z.shiftl_0_r.
    replace (n + 0) with n by lia.
    assumption.
  - intros until n. intros Hn Hval.
    replace (Z.of_nat m.+1) with (Z.of_nat m + 1)%Z by lia.
    rewrite <- Z.shiftl_shiftl; [|lia].
    rewrite Z.shiftl_mul_pow2; [|lia].
    rewrite Z.pow_1_r.
    replace (n + (Z.of_nat m + 1)) with (n + Z.of_nat m + 1) by lia.
    apply mul2_range; [lia|].
    apply (IHm val n); eauto.
Qed.

Lemma shiftl_range:
  forall val m n,
    0 <= m ->
    0 <= n ->
    0 <= val < 2 ^ n ->
    0 <= Z.shiftl val m < 2 ^ (n + m).
Proof.
  intros until n. intros Hm Hn Hval.
  pose (m' := Z.to_nat m).
  assert (m = Z.of_nat m') as Hm' by lia.
  rewrite !Hm'.
  eapply shiftl_range'; eauto.
Qed.

Lemma ones_land_0:
  forall m n,
    0 <= m ->
    0 <= n ->
    Z.land (Z.shiftl (Z.ones m) n) (Z.ones n) = 0.
Proof.
  intros m n Hm Hn.
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

Lemma ones_land_0':
  forall m n,
    0 <= m ->
    0 <= n ->
    Z.land (2 ^ m * Z.ones n) (Z.ones m) = 0.
Proof.
  intros m n Hm Hn.
  rewrite Z.mul_comm.
  rewrite <- Z.shiftl_mul_pow2; [|lia].
  eapply ones_land_0; eauto.
Qed.

Lemma ones_lor:
  forall n m,
  0 <= m ->
  0 <= n ->
  Z.ones (m + n) = Z.lor (Z.ones m) (Z.shiftl (Z.ones n) m).
Proof.
  intros until m. intros Hm Hn.
  rewrite Z.ones_add; [|lia|lia].
  rewrite Z.add_nocarry_lxor.
  rewrite Z.lxor_lor.
  rewrite Z.shiftl_mul_pow2; [|lia].
  rewrite Z.lor_comm.
  rewrite Z.mul_comm.
  reflexivity.
  - eapply ones_land_0'; eauto.
  - eapply ones_land_0'; eauto.
Qed.

Lemma and_ones_shiftl:
  forall a n m,
    0 <= n ->
    0 <= m ->
    Z.land a (Z.shiftl (Z.ones n) m) = Z.shiftl (Z.land (Z.shiftr a m) (Z.ones n)) m.
Proof.
  intros until m. intros Hn Hm.
  apply Z.bits_inj'. intros i Hlen.
  rewrite Z.land_spec.
  rewrite Z.shiftl_spec; [|lia].
  rewrite Z.shiftl_spec; [|lia].
  rewrite Z.land_spec.
  assert (i < m \/ m <= i)%Z as Hmi by lia.
  destruct Hmi as [Hmi | Hmi].
  - erewrite Z.testbit_neg_r with (a:=Z.ones n)(n:=i-m); [|lia].
    rewrite !Bool.andb_false_r.
    reflexivity.
  - rewrite Z.shiftr_spec; [|lia].
    rewrite Z.sub_simpl_r.
    reflexivity.
Qed.

Require Import IntegerFunctions.

(** * Int (binary representation) related
    Lemmas related to binary representation of integers.
 *)

Lemma int128_decompose:
  forall val,
    0 <= val < 2 ^ 128 ->
    val = val mod 2 ^ 64 + 2 ^ 64 * Z.shiftr val 64.
Proof.
  intros val Hval.
  rewrite Z.mod_eq; [|lia].
  rewrite Z.shiftr_div_pow2; [|lia].
  rewrite Z.sub_add.
  reflexivity.
Qed.

Lemma int128_decompose_spec:
  forall val,
    0 <= val < 2 ^ 128 ->
    exists lo hi,
      val = lo + 2 ^ 64 * hi /\
      lo = val mod 2 ^ 64 /\
      hi = Z.shiftr val 64.
Proof.
  intros until val. intros Hval.
  exists (val mod 2 ^ 64), (Z.shiftr val 64).
  split; [|split; reflexivity].
  apply int128_decompose.
  assumption.
Qed.

Lemma int_decompose_m:
  forall val n m,
    0 <= val < 2 ^ n ->
    0 <= m < n ->
    val = val mod 2 ^ m + 2 ^ m * Z.shiftr val m.
Proof.
  intros until m. intros Hval Hm.
  rewrite Z.mod_eq; [|lia].
  rewrite Z.shiftr_div_pow2; [|lia].
  rewrite Z.sub_add.
  reflexivity.
Qed.

Lemma int_decompose_n:
  forall val n,
    0 <= n ->
    0 <= val < 2 ^ n ->
    val = val mod 2 ^ n + 2 ^ n * Z.shiftr val n.
Proof.
  intros until n. intros Hn Hval.
  rewrite Z.mod_small; [|lia].
  rewrite Z.shiftr_div_pow2; [|lia].
  rewrite Z.div_small; [|lia].
  lia.
Qed.

Lemma int_decompose:
  forall val n m,
    0 <= val < 2 ^ n ->
    0 <= m <= n ->
    val = val mod 2 ^ m + 2 ^ m * Z.shiftr val m.
Proof.
  intros until m. intros Hval Hm.
  assert (m < n \/ m = n)%Z as Hmn by lia.
  destruct Hmn as [Hmn | Hmn].
  - eapply int_decompose_m; eauto.
    lia.
  - eapply int_decompose_n; eauto.
    lia.
    subst m. lia.
Qed.

Lemma int_decompose':
  forall val n m,
    0 <= val < 2 ^ n ->
    0 <= m <= n ->
    val = val mod two_p m + (Z.shiftr val m) * two_p m.
Proof.
  intros until m. intros Hval Hm.
  erewrite int_decompose with (val:=val) (n:=n) (m:=m) at 1; eauto.
  rewrite two_p_equiv.
  lia.
Qed.

Lemma int_lor_decomp:
  forall val n m,
    0 <= m ->
    0 <= n ->
    val mod 2 ^ (m + n) = Z.lor (val mod 2 ^ m) ((Z.shiftr val m mod 2 ^ n) * 2 ^ m).
Proof.
  intros until m. intros Hm Hn.
  do 3 (rewrite <- Z.land_ones; [|lia]).
  rewrite <- Z.shiftl_mul_pow2; [|lia].
  rewrite <- and_ones_shiftl; eauto.
  rewrite <- Z.land_lor_distr_r.
  rewrite <- ones_lor; eauto.
Qed.

Lemma int_lor_decomp':
  forall val n m,
    0 <= m ->
    0 <= n ->
    0 <= val < 2 ^ (m + n) ->
    val = Z.lor (val mod 2 ^ m) ((Z.shiftr val m mod 2 ^ n) * 2 ^ m).
Proof.
  intros until m. intros Hm Hn [Hvall Hvalr].
  assert (val = val mod 2 ^ (m + n)) as Hvalmod.
  {
    rewrite Z.mod_small; lia.
  }
  erewrite Hvalmod at 1.
  apply int_lor_decomp; eauto.
Qed.

Lemma shiftl_land_0:
  forall n x y,
    0 <= n ->
    0 <= x < 2 ^ n ->
    Z.land x (Z.shiftl y n) = 0.
Proof.
  intros until y. intros Hn Hx.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec.
  rewrite Z.shiftl_spec; [|lia].
  rewrite Z.testbit_0_l.
  assert (i < n \/ n <= i)%Z as Hni by lia.
  destruct Hni as [Hni | Hni].
  - erewrite Z.testbit_neg_r with (n:=i-n); [|lia].
    rewrite Bool.andb_false_r.
    reflexivity.
  - assert (x = x mod 2^n) as Hx' by (rewrite Z.mod_small; lia).
    rewrite Hx'.
    rewrite Z.mod_pow2_bits_high; [|lia].
    rewrite Bool.andb_false_l.
    reflexivity.
Qed.

(** * bits abstraction
    Lemmas for bits abstraction: bitmask and bit-extraction.
*)
Definition bitmask n m val :=
  Z.land val (Z.shiftl (Z.ones m) n).

Definition bitextract n m val :=
  Z.shiftr (bitmask n m val) n.

Lemma bitmask_spec:
  forall n m val,
    0 <= n ->
    0 <= m ->
    0 <= val ->
    bitmask n m val = (Z.shiftr val n mod 2 ^ m) * 2 ^ n.
Proof.
  intros until val. intros Hn Hm Hval.
  unfold bitmask.
  rewrite <- Z.land_ones; [|lia].
  rewrite <- Z.shiftl_mul_pow2; [|lia].
  rewrite <- and_ones_shiftl; eauto.
Qed.

Lemma bitmask_spec':
  forall n m val,
    0 <= n ->
    0 <= m ->
    0 <= val ->
    bitmask n m val = (val / 2 ^ n mod 2 ^ m) * 2 ^ n.
Proof.
  intros until val. intros Hn Hm Hval.
  rewrite <- Z.shiftr_div_pow2; [|lia].
  apply bitmask_spec; eauto.
Qed.

Lemma bitmask0:
  forall n val,
    0 <= n ->
    0 <= val ->
    bitmask 0 n val = val mod 2 ^ n.
Proof.
  intros until val. intros Hn Hval.
  rewrite bitmask_spec; [|lia|lia|lia].
  rewrite Z.shiftr_0_r.
  replace (2^0) with 1 by lia.
  rewrite Z.mul_1_r.
  reflexivity.
Qed.

Lemma int_lor_decomp_bitmask:
  forall val n m,
    0 <= m ->
    0 <= n ->
    0 <= val ->
    bitmask 0 (m + n) val = Z.lor (bitmask 0 m val) (bitmask m n val).
Proof.
  intros until m. intros Hm Hn Hval.
  do 2 (rewrite bitmask0; [|lia|lia]).
  rewrite bitmask_spec; eauto.
  eapply int_lor_decomp; eauto.
Qed.

Lemma int_lor_decomp_bitmask':
  forall val n m,
    0 <= m ->
    0 <= n ->
    0 <= val < 2 ^ (m + n) ->
    val = Z.lor (bitmask 0 m val) (bitmask m n val).
Proof.
  intros until m. intros Hm Hn [Hvall Hvalr].
  rewrite bitmask0; eauto.
  rewrite bitmask_spec; eauto.
  eapply int_lor_decomp'; eauto.
Qed.

Lemma shiftl_1_n: forall n x,
  0 <= n ->
  x * Z.shiftl 1 n = Z.shiftl x n.
Proof.
  intros.
  rewrite Z.shiftl_mul_pow2; [|lia].
  rewrite Z.mul_assoc.
  rewrite Z.mul_1_r.
  rewrite <- Z.shiftl_mul_pow2 by lia.
  reflexivity.
Qed.

Lemma disjoint: forall a b n,
  0 <= n ->
  0 <= a < 2 ^ n ->
  Z.land a (b * Z.shiftl 1 n) = 0.
Proof.
  intros until n. intros Hn Ha.
  rewrite shiftl_1_n; [|lia].
  apply shiftl_land_0; lia.
Qed.

Lemma mod_eq: forall a b n,
  0 <= n ->
  a = b ->
  a mod 2 ^ n = b mod 2 ^ n.
Proof.
  intros until n. intros Hn Heq.
  rewrite Heq.
  reflexivity.
Qed.

Lemma shiftl_mod_add: forall a b n,
  0 <= n ->
  0 <= a < 2 ^ n ->
  (a + Z.shiftl b n) mod 2 ^ n = a.
Proof.
  intros until n. intros Hn Ha.
  rewrite Z.add_mod; [|lia].
  rewrite Z.shiftl_mul_pow2; [|lia].
  rewrite Z_mod_mult.
  rewrite Z.add_0_r.
  rewrite Z.mod_mod; [|lia].
  rewrite Z.mod_small; [|lia].
  reflexivity.
Qed.

Lemma shiftl_eq: forall b b' n,
  0 <= n ->
  Z.shiftl b n = Z.shiftl b' n ->
  b = b'.
Proof.
  intros until n. intros Hn Heq.
  repeat (rewrite Z.shiftl_mul_pow2 in Heq; [|lia]).
  apply Z.mul_cancel_r in Heq; lia.
Qed.

Lemma disjoint_inj_low: forall a a' b c n,
  0 <= n ->
  0 <= a < 2 ^ n ->
  0 <= a' < 2 ^ n ->
  a + Z.shiftl b n = a' + Z.shiftl c n ->
  a = a'.
Proof.
  intros until n. intros Hn Ha Ha' Heq.
  eapply mod_eq with (n:=n) in Heq; [|lia].
  do 2 (rewrite shiftl_mod_add in Heq; [|lia|lia]).
  assumption.
Qed.

Lemma disjoint_inj_high: forall a a' b b' n,
  0 <= n ->
  0 <= a < 2 ^ n ->
  0 <= a' < 2 ^ n ->
  a + Z.shiftl b n = a' + Z.shiftl b' n ->
  b = b'.
Proof.
  intros until n. intros Hn Ha Ha' Heq.
  pose proof (disjoint_inj_low a a' b b' n Hn Ha Ha' Heq) as H.
  rewrite H in Heq.
  assert (Z.shiftl b n = Z.shiftl b' n) as Heq' by lia.
  apply shiftl_eq in Heq'; lia.
Qed.

Lemma disjoint_inj: forall a a' b b' n,
  0 <= n ->
  0 <= a < 2 ^ n ->
  0 <= a' < 2 ^ n ->
  a + Z.shiftl b n = a' + Z.shiftl b' n ->
  a = a' /\ b = b'.
Proof.
  intros until n. intros Hn Ha Ha' Hcomp.
  pose proof (disjoint_inj_low a a' b b' n Hn Ha Ha' Hcomp) as Ha''.
  pose proof (disjoint_inj_high a a' b b' n Hn Ha Ha' Hcomp) as Hb''.
  apply (conj Ha'' Hb'').
Qed.

Lemma disjoint_inj': forall a a' b b' n,
  0 <= n ->
  0 <= a < 2 ^ n ->
  0 <= a' < 2 ^ n ->
  a + (b * Z.shiftl 1 n) = a' + (b' * Z.shiftl 1 n) ->
  a = a' /\ b = b'.
Proof.
  intros until n. intros Hn Ha Ha' Hcomp.
  do 2 (rewrite shiftl_1_n in Hcomp; [|lia]).
  apply disjoint_inj in Hcomp; lia.
Qed.

Lemma disjoint_inj_rev: forall a a' b b' n,
  0 <= n ->
  0 <= a < 2 ^ n ->
  0 <= a' < 2 ^ n ->
  Z.shiftl b n + a = Z.shiftl b' n + a' ->
  a = a' /\ b = b'.
Proof.
  intros until n. intros Hn Ha Ha' Hcomp.
  rewrite Z.add_comm in Hcomp.
  replace (Z.shiftl b' n + a') with (a' + Z.shiftl b' n) in Hcomp by lia.
  eapply disjoint_inj in Hcomp; lia.
Qed.

Lemma mul_r_lt: forall a b c,
  0 <= a ->
  0 <= b ->
  0 <= c ->
  a * c < b * c ->
  a < b * c.
Proof.
  intros until c. intros Ha Hb Hc Hlt.
  assert (c = 0 \/ c = 1 \/ c > 1) as Hc' by lia.
  destruct Hc' as [Hc' | [Hc' | Hc']].
  - rewrite Hc' in Hlt.
    lia.
  - rewrite Hc' in Hlt.
    rewrite !Z.mul_1_r in Hlt.
    lia.
  - apply Z.mul_lt_mono_pos_r in Hlt; [|lia].
    assert (b * 1 < b * c) as Hbc.
    {
      apply Z.mul_lt_mono_pos_l; lia.
    }
    rewrite Z.mul_1_r in Hbc.
    lia.
Qed.

Lemma disjoint_add_range: forall a b n m,
  0 <= n ->
  0 <= m ->
  0 <= a < 2 ^ n ->
  0 <= b < 2 ^ m ->
  0 <= a + Z.shiftl b n < 2 ^ (n + m).
Proof.
  intros until m. intros Hn Hm Ha Hb.
  split.
  - rewrite Z.shiftl_mul_pow2; [|lia].
    lia.
  - assert (0 <= Z.shiftl b n < 2 ^ (m + n)) as Hb'.
    {
      apply (shiftl_range b n m); lia.
    }
    assert (a < 2 ^ (n + m)) as Ha'.
    {
      rewrite Z.pow_add_r; [|lia|lia].
      apply mul_r_lt; [lia|lia|lia|].
      apply Z.mul_lt_mono_pos_r; lia.
    }
    pose proof (disjoint a b n Hn Ha) as Hdisj.
    rewrite shiftl_1_n in Hdisj; [|lia].
    rewrite Z.add_comm in Hb'.
    destruct Hb' as [Hb'0 Hb'mn].
    apply Z.add_nocarry_lt_pow2; assumption.
Qed.

Lemma disjoint_add_range_rev: forall a b n m,
  0 <= n ->
  0 <= m ->
  0 <= a < 2 ^ n ->
  0 <= b < 2 ^ m ->
  0 <= Z.shiftl b n + a < 2 ^ (n + m).
Proof.
  intros until m. intros Hn Hm Ha Hb.
  rewrite Z.add_comm.
  apply disjoint_add_range; lia.
Qed.

Lemma shiftl_distr_r:
  forall a b n m,
    0 <= n ->
    0 <= m ->
    Z.shiftl a n + Z.shiftl b (n + m) = Z.shiftl (a + Z.shiftl b m) n.
Proof.
  intros until m. intros Hn Hm.
  do 4 (rewrite Z.shiftl_mul_pow2; [|lia]).
  rewrite Z.pow_add_r; [|lia|lia].
  rewrite Z.mul_assoc.
  replace (b * 2 ^ n * 2 ^ m) with (b * 2 ^ m * 2 ^ n) by lia.
  lia.
Qed.

Lemma shiftl_distr_l:
  forall a b n m,
    0 <= n ->
    0 <= m ->
    Z.shiftl b (m + n) + Z.shiftl a n = Z.shiftl (a + Z.shiftl b m) n.
Proof.
  intros until m. intros Hn Hm.
  rewrite Z.add_comm.
  replace ((m + n)) with (n + m) by lia.
  apply shiftl_distr_r; lia.
Qed.

Lemma bitmask_size0:
  forall n val,
    bitmask n 0 val = 0.
Proof.
  intros until val.
  unfold bitmask.
  rewrite Z.shiftl_0_l.
  rewrite Z.land_0_r.
  reflexivity.
Qed.

Lemma bitmask_shiftr_shiftl:
  forall n m val,
    0 <= n ->
    0 <= m ->
    0 <= val ->
    bitmask n m val = Z.shiftl (bitmask 0 m (Z.shiftr val n)) n.
Proof.
  intros until val. intros Hn Hm Hval.
  rewrite bitmask_spec; eauto.
  rewrite bitmask0; eauto.
  rewrite Z.shiftr_div_pow2; eauto.
  rewrite Z.shiftl_mul_pow2; eauto.
  apply <- Z.shiftr_nonneg.
  assumption.
Qed.

Lemma bitmask_full:
  forall n val,
    0 <= n ->
    0 <= val ->
    bitmask 0 n val = val mod 2 ^ n.
Proof.
  intros until val. intros Hn Hval.
  rewrite bitmask_spec; eauto.
  rewrite Z.shiftr_0_r.
  replace (2^0) with 1 by lia.
  rewrite Z.mul_1_r.
  reflexivity.
  lia.
Qed.

Lemma bitmask_full':
  forall n val,
    0 <= n ->
    0 <= val < 2 ^ n ->
    bitmask 0 n val = val.
Proof.
  intros until val. intros Hn [Hvall Hvalr].
  rewrite bitmask_full; eauto.
  rewrite Z.mod_small; lia.
Qed.

Lemma bitmask0_is_mod:
  forall n val,
    0 <= n ->
    0 <= val ->
    bitmask 0 n val = val mod 2 ^ n.
Proof.
  intros n val. intros Hn Hval.
  rewrite bitmask0; lia.
Qed.

Lemma bitextract_spec:
  forall n m val,
    0 <= n ->
    0 <= m ->
    0 <= val ->
    bitextract n m val = val / 2 ^ n mod 2 ^ m.
Proof.
  intros until val. intros Hn Hm Hval.
  unfold bitextract.
  rewrite Z.shiftr_div_pow2; eauto.
  rewrite bitmask_spec; eauto.
  rewrite Z.shiftr_div_pow2; eauto.
  rewrite Z.div_mul; [|lia].
  reflexivity.
Qed.

Lemma bitextract_full:
  forall n val,
    0 <= n ->
    0 <= val ->
    bitextract 0 n val = val mod 2 ^ n.
Proof.
  intros until val. intros Hn Hval.
  rewrite bitextract_spec; eauto.
  rewrite Z.pow_0_r.
  rewrite Z.div_1_r.
  reflexivity.
  lia.
Qed.

Lemma bitextract_full':
  forall n val,
    0 <= n ->
    0 <= val < 2 ^ n ->
    bitextract 0 n val = val.
Proof.
  intros until val. intros Hn [Hvall Hvalr].
  rewrite bitextract_full; eauto.
  rewrite Z.mod_small; lia.
Qed.

Lemma bitextract_shiftr_1:
  forall n m val,
    0 <= n ->
    0 <= m ->
    0 <= val ->
    bitextract (n + 1) m val = Z.shiftr (bitextract n (m + 1) val) 1.
Proof.
  intros until val. intros Hn Hm Hval.
  unfold bitextract.
  rewrite Z.shiftr_shiftr; [|lia].
  unfold bitmask.
  apply Z.bits_inj'.
  intros i Hi.
  do 2 (rewrite Z.shiftr_spec; [|lia]).
  do 2 rewrite Z.land_spec.
  f_equal.
  do 2 (rewrite Z.shiftl_spec; [|lia]).
  replace (i + (n + 1) - (n + 1)) with i by lia.
  replace ((i + (n + 1) - n)) with (i + 1) by lia.
  assert (i < m \/ m <= i)%Z as Hmi by lia.
  destruct Hmi as [Hmi | Hmi].
  - rewrite Z.ones_spec_low; [|lia].
    rewrite Z.ones_spec_low; [|lia].
    reflexivity.
  - rewrite Z.ones_spec_high; [|lia].
    rewrite Z.ones_spec_high; [|lia].
    reflexivity.
Qed.

Lemma bitextract_shiftr':
  forall (k: nat) n m val,
    0 <= n ->
    0 <= m ->
    0 <= val ->
    bitextract (n + Z.of_nat k) m val = 
    Z.shiftr (bitextract n (m + Z.of_nat k) val) (Z.of_nat k).
Proof.
  induction k.
  - intros until val. intros Hn Hm Hval.
    replace (Z.of_nat 0) with 0 by lia.
    rewrite !Z.add_0_r.
    rewrite Z.shiftr_0_r.
    reflexivity.
  - intros until val. intros Hn Hm Hval.
    replace (n + Z.of_nat k.+1) with (n + Z.of_nat k + 1) by lia.
    rewrite bitextract_shiftr_1; [|lia|lia|lia].
    rewrite IHk; [|lia|lia|lia].
    rewrite Z.shiftr_shiftr; [|lia].
    f_equal; [|lia].
    f_equal; lia.
Qed.

Lemma bitextract_shiftr:
  forall n m k val,
    0 <= n ->
    0 <= m ->
    0 <= k ->
    0 <= val ->
    bitextract (n + k) m val = Z.shiftr (bitextract n (m + k) val) k.
Proof.
  intros until val. intros Hn Hm Hk Hval.
  assert (k = Z.of_nat (Z.to_nat k)) as Hnatk by lia.
  rewrite Hnatk.
  eapply bitextract_shiftr'; eauto.
Qed.

Lemma bitextract_n_is_shiftr:
  forall m n val,
    0 <= m <= n ->
    0 <= val < 2 ^ n ->
    bitextract m (n - m) val = Z.shiftr val m.
Proof.
  intros m n val. intros Hmn Hval.
  rewrite bitextract_spec; [|lia|lia|lia].
  rewrite Z.shiftr_div_pow2; [|lia].
  rewrite Z.mod_small; [reflexivity|].
  rewrite <- Z.shiftr_div_pow2; [|lia].
  apply shiftr_range; lia.
Qed.

Lemma int_lor_decomp_bitmask_i:
  forall val i m n,
    0 <= i ->
    0 <= n ->
    0 <= m ->
    0 <= val ->
    bitmask i (m + n) val = Z.lor (bitmask i m val) (bitmask (i + m) n val).
Proof.
  intros val i m n Hi Hn Hm Hval.
  do 3 (rewrite bitmask_spec; [|lia|lia|lia]).
  do 3 (rewrite <- Z.shiftl_mul_pow2; [|lia]).
  replace (i + m) with (m + i) at 2 by lia.
  rewrite <- Z.shiftl_shiftl; [|lia].
  rewrite <- Z.shiftl_lor.
  f_equal.
  rewrite <- Z.shiftr_shiftr; [|lia].
  remember (Z.shiftr val i) as val'.
  rewrite Z.shiftl_mul_pow2; [|lia].
  eapply int_lor_decomp; lia.
Qed.

Lemma int_lor_decomp_bitmask_3:
  forall val i j n,
    0 <= i < j ->
    j <= n ->
    0 <= val < 2 ^ n ->
    val = Z.lor (bitmask 0 i val)
                (Z.lor (bitmask i (j - i) val)
                       (bitmask j (n - j) val)).
Proof.
  intros val i j n Hi Hj Hval.
  erewrite int_lor_decomp_bitmask' with (val:=val)(n:=n-i)(m:=i) at 1; 
    [|lia|lia|].
  f_equal.
  replace (n - i) with (j - i + (n - j)) by lia.
  erewrite int_lor_decomp_bitmask_i with (val:=val)(i:=i)(m:=j-i)(n:=n-j); 
    [|lia|lia|lia|lia].
  replace (i + (j - i)) with j by lia.
  reflexivity.
  replace (i + (n - i)) with n by lia.
  assumption.
Qed.

Lemma same_bits_equal:
  forall a b,
    a = b ->
    forall i, Z.testbit a i = Z.testbit b i.
Proof.
  intros a b Heq i.
  rewrite Heq.
  reflexivity.
Qed.

Lemma shiftl_shiftr_id:
  forall n val,
    0 <= n ->
    0 <= val ->
    Z.land val (Z.ones n) = 0 ->
    Z.shiftl (Z.shiftr val n) n = val.
Proof.
  intros n val Hn Hval Hland.
  eapply Z.bits_inj'. intros i Hi.
  apply same_bits_equal with (i:=i) in Hland.
  assert (i < n \/ n <= i)%Z as Hin by lia.
  destruct Hin as [Hin | Hin].
  - rewrite Z.testbit_0_l in Hland.
    rewrite Z.land_spec in Hland.
    rewrite Z.ones_spec_low in Hland; [|lia].
    assert (Z.testbit val i = false) as Hival by lia.
    rewrite Hival.
    rewrite Z.shiftl_spec; [|lia].
    rewrite Z.testbit_neg_r; [|lia].
    reflexivity.
  - rewrite Z.shiftl_spec; [|lia].
    rewrite Z.shiftr_spec; [|lia].
    replace (i - n + n)%Z with i by lia.
    reflexivity.
Qed.

Lemma bitmask_low_0:
  forall n m val,
    0 <= n ->
    0 <= m ->
    0 <= val ->
    Z.land (bitmask n m val) (Z.ones n) = 0.
Proof.
  intros n m val Hn Hm Hval.
  unfold bitmask.
  apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec.
  rewrite Z.testbit_0_l.
  assert (i < n \/ n <= i)%Z as Hin by lia.
  destruct Hin as [Hin | Hin].
  - rewrite Z.shiftl_spec; [|lia].
    erewrite Z.testbit_neg_r with (n:=i-n); [|lia].
    rewrite Bool.andb_false_r.
    rewrite Bool.andb_false_l.
    reflexivity.
  - erewrite Z.ones_spec_high at 1; [|lia].
    rewrite Bool.andb_false_r.
    reflexivity.
Qed.

Lemma bitmask_pos:
  forall n m val,
    0 <= n ->
    0 <= m ->
    0 <= val ->
    0 <= bitmask n m val.
Proof.
  intros n m val Hn Hm Hval.
  rewrite bitmask_spec; [|lia|lia|lia].
  rewrite <- Z.shiftl_mul_pow2; [|lia].
  apply Z.shiftl_nonneg.
  apply Z.mod_pos_bound.
  lia.
Qed.

Lemma bitmask_bitextract_shiftl:
  forall i n val,
    0 <= i ->
    0 <= n ->
    0 <= val ->
    bitmask i n val = Z.shiftl (bitextract i n val) i.
Proof.
  intros i n val Hi Hn Hval.
  unfold bitextract.
  rewrite shiftl_shiftr_id.
  reflexivity.
  - lia.
  - apply bitmask_pos; lia.
  - apply bitmask_low_0; lia.
Qed. 


(** * Bytes related
    Lemmas related to bytes and bits.
 *)

From Wasm Require Import bytes properties.
From compcert Require Import Integers Memdata Archi.
Transparent Archi.big_endian.

Lemma little_endian_eq: forall bs,
    rev_if_be (bs) = bs.
Proof.
  intros.
  unfold rev_if_be.
  unfold big_endian.
  reflexivity.
Qed.


Lemma encode_decode_int64: forall n,
  0 <= n < 2 ^ 64 ->
  Memdata.decode_int (Memdata.encode_int 8 n) = n.
Proof.
  intros.
  rewrite Memdata.decode_encode_int.
  rewrite Z.mod_small.
  reflexivity.
  split.
  - lia.
  - simpl. rewrite <- two_power_n'.
    lia.
    lia.
Qed.

Lemma encode_decode_int': forall val n,
  0 <= val < 2 ^ (8 * Z.of_nat n) ->
  decode_int (Memdata.encode_int n val) = val.
Proof.
  intros.
  rewrite Memdata.decode_encode_int.
  rewrite Z.mod_small.
  reflexivity.
  rewrite two_p_equiv.
  rewrite Z.mul_comm.
  assumption.
Qed.

Lemma decode_int_nil: decode_int [::] = 0.
Proof. reflexivity. Qed.

Lemma decode_int_app: forall bs1 bs2,
  decode_int (bs1 ++ bs2) = decode_int bs1 + decode_int bs2 * 2 ^ (8 * Z.of_nat (size bs1)).
Proof.
  intros bs1 bs2.
  unfold decode_int.
  repeat rewrite little_endian_eq.
  rewrite int_of_bytes_append.
  rewrite length_is_size.
  rewrite two_p_equiv.
  do 3 f_equal.
  lia.
Qed.

Lemma decode_int_1:
  forall (b: byte),
    decode_int [:: b] = Byte.unsigned b.
Proof.
  intros.
  unfold decode_int.
  rewrite little_endian_eq.
  simpl. lia.
Qed.

Lemma decode_int_cons:
  forall (b: byte) (bs: bytes),
    decode_int (b :: bs) = Byte.unsigned b + decode_int bs * 2 ^ 8.
Proof.
  intros until bs.
  rewrite cons_app.
  rewrite decode_int_app.
  simpl.
  rewrite decode_int_1.
  reflexivity.
Qed.

Lemma encode_int_cons_head:
  forall (n: nat) (val: Z) (b: byte) (bs: bytes),
    0 <= val < 2 ^ (8 * Z.of_nat n) ->
    Memdata.encode_int n val = b :: bs ->
    Byte.unsigned b = val mod 2 ^ 8.
Proof.
  intros until bs. intros Hval Hbs.
  pose proof (Memdata.encode_int_length n val) as Hlen.
  assert (0 < n)%nat as Hn.
  {
    rewrite Hbs in Hlen.
    rewrite length_is_size in Hlen.
    rewrite size_cons in Hlen.
    lia.
  }
  unfold encode_int in Hbs.
  rewrite little_endian_eq in Hbs.
  replace n with (1 + (n - 1))%nat in Hbs by lia.
  assert (val = val mod two_p 8 + (Z.shiftr val 8) * two_p 8) as Hval'.
  {
    eapply int_decompose' with (n:=8 * Z.of_nat n)(m:=8)(val:=val); eauto.
    lia.
  }
  rewrite Hval' in Hbs.
  - rewrite bytes_of_int_append in Hbs.
    simpl in Hbs.
    inversion Hbs.
    rewrite Byte.unsigned_repr.
    + rewrite two_power_pos_equiv. reflexivity.
    + unfold Byte.max_unsigned, Byte.modulus, Byte.wordsize, Wordsize_8.wordsize.
      rewrite two_power_pos_equiv.
      rewrite two_power_nat_equiv.
      split.
      * apply mod_sign; lia.
      * apply mod_pow2_range'; lia.
  - replace (Z.of_nat 1 * 8) with 8 by lia.
  repeat rewrite two_p_equiv.
  split.
  + apply mod_sign; lia.
  + apply mod_pow2_range; lia.
Qed.

Lemma encode_int_cons_behead:
  forall (n: nat) (val: Z) (b: byte) (bs: bytes),
    0 <= val < 2 ^ (8 * Z.of_nat n) ->
    Memdata.encode_int n val = b :: bs ->
    Memdata.encode_int (n - 1) (Z.shiftr val 8) = bs.
Proof.
  intros until bs. intros Hval Hbs.
  pose proof (Memdata.encode_int_length n val) as Hlen.
  assert (0 < n)%nat as Hn.
  {
    rewrite Hbs in Hlen.
    rewrite length_is_size in Hlen.
    rewrite size_cons in Hlen.
    lia.
  }
  unfold encode_int in Hbs.
  rewrite little_endian_eq in Hbs.
  replace n with (1 + (n - 1))%nat in Hbs by lia.
  assert (val = val mod two_p 8 + (Z.shiftr val 8) * two_p 8) as Hval'.
  {
    eapply int_decompose' with (n:=8 * Z.of_nat n)(m:=8)(val:=val); eauto.
    lia.
  }
  rewrite Hval' in Hbs.
  - rewrite bytes_of_int_append in Hbs.
    simpl in Hbs.
    inversion Hbs.
    unfold encode_int.
    rewrite little_endian_eq.
    reflexivity.
  - replace (Z.of_nat 1 * 8) with 8 by lia.
    repeat rewrite two_p_equiv.
    split.
    + apply mod_sign; lia.
    + apply mod_pow2_range; lia.
Qed.

Lemma decode_int_cons_lor:
  forall (b: byte) (bs: bytes),
    decode_int (b :: bs) = Z.lor (Byte.unsigned b) (Z.shiftl (decode_int bs) 8).
Proof.
  intros until bs.
  rewrite decode_int_cons.
  rewrite <- Z.shiftl_mul_pow2; [|lia].
  assert (Z.land (Byte.unsigned b)
                 (Z.shiftl (decode_int bs) 8) = 0).
  {
    eapply shiftl_land_0; [lia|].
    apply Byte.unsigned_range.
  }
  rewrite Z.add_nocarry_lxor; [|assumption].
  rewrite Z.lxor_lor; [|assumption].
  reflexivity.
Qed.

Lemma encode_head:
  forall n val b bs,
  (0 < n)%nat ->
  encode_int n val = b :: bs ->
  encode_int 1 val = [:: b].
Proof.
  intros until bs. intros Hn Hbs.
  unfold encode_int in Hbs.
  rewrite little_endian_eq in Hbs.
  destruct n as [|n'].
  - discriminate Hn.
  - simpl in Hbs.
    inversion Hbs.
    unfold encode_int.
    rewrite little_endian_eq.
    simpl.
    reflexivity.
Qed.

Lemma encode_head':
  forall n val b bs,
  (0 < n)%nat ->
  encode_int n val = b :: bs ->
  b = Byte.repr val.
Proof.
  intros until bs. intros Hn Hbs.
  pose proof (encode_head n val b bs Hn Hbs) as Hhead.
  unfold encode_int in Hhead.
  rewrite little_endian_eq in Hhead.
  simpl in Hhead.
  inversion Hhead.
  reflexivity.
Qed.

Lemma encode_int_size0:
  forall val,
    encode_int 0 val = [::].
Proof.
  intros val.
  unfold encode_int.
  rewrite little_endian_eq.
  simpl.
  reflexivity.
Qed.

Lemma encode_decoded_cons:
  forall b bs,
    encode_int (1 + size bs) (decode_int (b :: bs)) 
    = b :: encode_int (size bs) (decode_int bs).
Proof.
  intros b bs.
  unfold encode_int.
  rewrite !little_endian_eq.
  rewrite decode_int_cons.
  rewrite bytes_of_int_append.
  simpl.
  rewrite Byte.repr_unsigned.
  reflexivity.
  apply Byte.unsigned_range.
Qed.

Lemma encode_exists:
  forall bs,
    exists val, 
      encode_int (size bs) val = bs /\
      0 <= val < 2 ^ (8 * Z.of_nat (size bs)).
Proof.
  intros bs.
  exists (decode_int bs).
  induction bs as [|b bs' IH].
  - rewrite size_nil_eq.
    rewrite encode_int_size0.
    rewrite decode_int_nil.
    split.
    + reflexivity.
    + lia.
  - rewrite size_cons.
    replace (size bs' + 1)%nat with (1 + size bs')%nat by lia.
    rewrite encode_decoded_cons.
    destruct IH as [Ival Irange].
    split.
    + rewrite Ival.
      reflexivity.
    + rewrite decode_int_cons_lor.
      pose proof (Byte.unsigned_range b) as Hb.
      replace (8 * Z.of_nat (1 + size bs')) with (8 + 8 * Z.of_nat (size bs')) by lia.
      eapply lor_bound_r with (n:=8) (m:=(8 + 8 * Z.of_nat (size bs')))
        (x:=Byte.unsigned b) (y:=(Z.shiftl (decode_int bs') 8)); eauto.
      * lia.
      * replace (8 + 8 * Z.of_nat (size bs')) with 
        (8 * Z.of_nat (size bs') + 8) by lia.
        eapply shiftl_range; eauto.
        lia.
        lia.
Qed.

Lemma encode_int_app:
  forall (n1 n2: nat) val1 val2,
  0 <= val1 < 2 ^ (8 * Z.of_nat n1) ->
  encode_int (n1 + n2) 
    (val1 + val2 * 2 ^ (8 * Z.of_nat n1) ) =
  encode_int n1 val1 ++ encode_int n2 val2.
Proof.
  intros until val2. intros Hval1.
  unfold encode_int.
  rewrite !little_endian_eq.
  rewrite <- bytes_of_int_append.
  rewrite ssrnat_nat_add.
  rewrite two_p_equiv.
  do 4 f_equal.
  lia.
  - rewrite two_p_equiv.
    replace (Z.of_nat n1 * 8) with (8 * Z.of_nat n1) by lia.
    assumption.
Qed.

Lemma decode_int_shiftr_1:
  forall (bs: bytes),
    (size bs > 0)%nat ->
    decode_int (drop 1 bs) = Z.shiftr (decode_int bs) 8.
Proof.
  intros bs Hbs.
  destruct bs as [|b bs'].
  - rewrite size_nil_eq in Hbs.
    discriminate Hbs.
  - rewrite drop1.
    rewrite behead_is_tail.
    rewrite decode_int_cons_lor.
    rewrite Z.shiftr_lor.
    rewrite Z.shiftr_shiftl_l; [|lia].
    replace (8 - 8) with 0 by lia.
    rewrite Z.shiftl_0_r.
    pose proof (Byte.unsigned_range b) as Hb.
    assert (Byte.unsigned b = 0 \/ Byte.unsigned b > 0) as Hb' by lia.
    destruct Hb' as [Hb' | Hb'].
    + rewrite Hb'.
      rewrite Z.lor_0_l.
      reflexivity.
    + rewrite Z.shiftr_eq_0.
      rewrite Z.lor_0_l.
      reflexivity.
      - lia.
      - unfold Byte.modulus in Hb.
        rewrite two_power_nat_equiv in Hb.
        unfold Byte.wordsize in Hb.
        unfold Wordsize_8.wordsize in Hb.
        replace (Z.of_nat 8) with 8 in Hb by lia.
        apply Z.log2_lt_pow2; lia.
Qed.

Lemma decode_int_range:
  forall bs,
    0 <= decode_int bs < 2 ^ (8 * Z.of_nat (size bs)).
Proof.
  intros bs.
  pose proof (encode_exists bs) as [val [Hval Hrange]].
  rewrite <- Hval.
  pose proof (Memdata.encode_int_length (size bs) val) as Hlen.
  rewrite length_is_size in Hlen.
  remember (size bs) as n.
  rewrite Hlen.
  rewrite Memdata.decode_encode_int.
  rewrite two_p_equiv.
  rewrite Z.mul_comm.
  rewrite Z.mod_small; lia.
Qed.

Lemma decode_int_app_lor: forall bs1 bs2,
  decode_int (bs1 ++ bs2) = Z.lor (decode_int bs1) (decode_int bs2 * 2 ^ (8 * Z.of_nat (size bs1))).
Proof.
  intros bs1 bs2.
  rewrite decode_int_app.
  pose proof (decode_int_range bs1) as Hrange1.
  assert ((0 <= size bs1)%nat) as Hsize1 by lia.
  assert (0 <= 8 * Z.of_nat (size bs1)) as Hsize1' by lia.
  pose proof (shiftl_land_0 (8 * Z.of_nat (size bs1)) 
    (decode_int bs1) (decode_int bs2) Hsize1' Hrange1) as Hland.
  generalize Hland.
  rewrite Z.shiftl_mul_pow2; [|lia].
  intros Hland'.
  rewrite Z.add_nocarry_lxor; eauto.
  rewrite Z.lxor_lor; eauto.
Qed.

Lemma decode_int_app_lor': forall bs1 bs2,
  decode_int (bs1 ++ bs2) = Z.lor (decode_int bs1) (Z.shiftl (decode_int bs2) (8 * Z.of_nat (size bs1))).
Proof.
  intros.
  rewrite Z.shiftl_mul_pow2; [|lia].
  rewrite decode_int_app_lor.
  reflexivity.
Qed.

Lemma decode_int_app_lor_3':
  forall bs1 bs2 bs3,
    decode_int (bs1 ++ bs2 ++ bs3) = 
    Z.lor (decode_int bs1)
          (Z.shiftl (Z.lor (decode_int bs2)
                           (Z.shiftl (decode_int bs3) 
                                     (8 * Z.of_nat (size bs2)))) 
                    (8 * Z.of_nat (size bs1))).
Proof.
  intros bs1 bs2 bs3.
  do 2 rewrite decode_int_app_lor'.
  reflexivity.
Qed.

Lemma decode_int_app_lor_3:
  forall bs1 bs2 bs3,
    decode_int (bs1 ++ bs2 ++ bs3) = 
    Z.lor (decode_int bs1)
          (Z.lor (Z.shiftl (decode_int bs2) (8 * Z.of_nat (size bs1)))
                 (Z.shiftl (decode_int bs3) (8 * Z.of_nat (size bs1 + size bs2)))).
Proof.
  intros bs1 bs2 bs3.
  rewrite decode_int_app_lor_3'.
  replace (8 * Z.of_nat (size bs1 + size bs2)) with
    (8 * Z.of_nat (size bs2) + 8 * Z.of_nat (size bs1)) by lia.
  rewrite <- Z.shiftl_shiftl; [|lia].
  rewrite Z.shiftl_lor.
  reflexivity.
Qed.


