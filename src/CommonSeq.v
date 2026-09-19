(* Copyright (C) CertiK 2024-2026 *)

From Coq Require Import Arith ZArith NArith Nnat Psatz List.
From mathcomp.ssreflect Require Import seq ssreflect eqtype.

(* Notation overridden of mathcomp to Coq *)
Set Warnings "-notation-overridden".
From mathcomp.ssreflect Require Import ssrnat ssrbool ssrfun.
Set Warnings "+notation-overridden".

From mathcomp Require Import lra zify.

Lemma cons_app: forall {A} (x: A) xs,
  x :: xs = [:: x] ++ xs.
Proof. reflexivity. Qed.

Lemma behead_is_tail:
  forall {A} (a: A) (l: seq A),
    behead (a :: l) = l.
Proof.
  intros. reflexivity.
Qed.

Lemma size_cons:
  forall A (x: A) (s: seq A),
    size (x :: s) = (size s + 1)%nat.
Proof.
  intros until s.
  simpl. lia.
Qed.

Lemma size_ge0:
  forall {A} (l: seq A),
    (0 <= size l)%nat.
Proof.
  intros. lia.
Qed.

Lemma size_nil:
  forall {A} (l: seq A),
    (size l = 0)%nat <-> l = [::].
Proof.
  intros. split.
  - apply size0nil.
  - intros. subst l. simpl. reflexivity.
Qed.

Lemma size_nil_eq:
  forall {A}, size (@nil A) = 0%nat.
Proof.
  reflexivity.
Qed.

Lemma take_size_gt0:
  forall {A} n ml (b: A) (bs: seq A),
    take n ml = b :: bs ->
    (n > 0)%nat.
Proof.
  intros until bs. intros Htake.
  destruct n.
  - rewrite take0 in Htake. discriminate Htake.
  - lia.
Qed.

Lemma take_l_not_nil:
  forall {A} n ml (b: A) (bs: seq A),
    take n ml = b :: bs ->
    ml <> nil.
Proof.
  intros until bs. intros Htake.
  destruct ml.
  - simpl in Htake. discriminate Htake.
  - discriminate 1.
Qed.

Lemma take_1:
  forall {A} (l: seq A) (a: A),
    take 1 [:: a & l] = [:: a].
Proof.
  intros. simpl. rewrite take0. reflexivity.
Qed.

Lemma app_take_size:
  forall {A} (l1 l2: seq A),
    take (size l1) (l1 ++ l2) = l1.
Proof.
  intros A l1 l2.
  rewrite take_cat.
  replace (size l1 < size l1)%N with false by lia.
  replace (size l1 - size l1)%N with 0%N by lia.
  rewrite take0.
  rewrite cats0.
  reflexivity.
Qed.

Lemma app_drop_size:
  forall {A} (l1 l2: seq A),
    drop (size l1) (l1 ++ l2) = l2.
Proof.
  intros A l1 l2.
  rewrite drop_cat.
  replace (size l1 < size l1)%N with false by lia.
  replace (size l1 - size l1)%N with 0%N by lia.
  rewrite drop0.
  reflexivity.
Qed.

Lemma seq_cons_cases:
  forall A (l: seq A),
    l = [::] \/ exists a l', l = a :: l'.
Proof.
  intros A l.
  destruct l.
  - left. reflexivity.
  - right. exists a. exists l. reflexivity.
Qed.

Lemma seq_cons_spec:
  forall A (l: seq A) (dft: A),
    l = [::] \/ 
    exists a l', l = a :: l' /\
    a = head dft l /\
    l' = behead l.
Proof.
  intros A l dft.
  destruct l.
  - left. reflexivity.
  - right. exists a. exists l. split; [reflexivity|].
    split; [reflexivity|].
    simpl. reflexivity.
Qed.

Lemma seq_cons_inv:
  forall A (l: seq A) (dft: A),
    l <> [::] ->
    l = head dft l :: behead l.
Proof.
  intros A l dft Hnil.
  pose proof (seq_cons_spec _ l dft) as [Hl | [a [l' [Hl [Ha Hl']]]]].
  - contradiction Hnil.
  - subst l. reflexivity.
Qed.

Lemma take_head_eq:
  forall {A} (l: seq A) (dft: A),
    l <> [::] ->
    take 1 l = [:: head dft l].
Proof.
  intros until dft. intros Hnil.
  destruct l.
  - contradiction Hnil. reflexivity.
  - simpl. rewrite take0. reflexivity.
Qed.

Lemma take_head:
  forall {A} (l l': seq A) (dft: A),
    take 1 (head dft l :: l') = [:: head dft l].
Proof.
  intros until dft.
  simpl. rewrite take0. reflexivity.
Qed.

Lemma take_1_cons:
  forall {A} (l l': seq A) (a: A) len,
    take len l = a :: l' ->
    take 1 l = [:: a] /\ take (len - 1) (drop 1 l) = l'.
Proof.
  intros until len. intros Htake.
  pose proof (take_l_not_nil len l a l' Htake) as Hnil.
  pose proof (take_size_gt0 len l a l' Htake) as Hlen.
  replace (len) with (1 + (len - 1))%nat in Htake by lia.
  rewrite takeD in Htake.
  pose proof (seq_cons_inv _ l a Hnil) as Hl.
  rewrite Hl in Htake.
  rewrite take_head in Htake.
  rewrite drop1 in Htake.
  simpl in Htake.
  inversion Htake.
  split.
  - rewrite Hl. simpl. rewrite take0. reflexivity.
  - rewrite drop1. reflexivity.
Qed.

Lemma take_1_is_head:
  forall {A} (l: seq A) (dft: A),
    l <> [::] ->
    take 1 l = [:: head dft l].
Proof.
  intros until dft. intros Hnil.
  destruct l.
  - contradiction Hnil. reflexivity.
  - simpl. rewrite take0. reflexivity.
Qed.

Lemma take_1_cons_inv:
  forall {A} (l l': seq A) (a: A) len,
    (len > 0)%nat ->
    take 1 l = [:: a] ->
    take (len - 1) (drop 1 l) = l' ->
    take len l = a :: l'.
Proof.
  intros until len. intros Hlen Htake Hdrop.
  replace len with (1 + (len - 1))%nat by lia.
  rewrite takeD.
  rewrite Htake. rewrite Hdrop. simpl.
  reflexivity.
Qed.

Lemma drop_not_nil:
  forall {A} (l: seq A) n,
    (n < size l)%nat ->
    drop n l <> [::].
Proof.
  intros until n. intros Hlen.
  assert (l = take n l ++ drop n l) as Hl.
  {
    rewrite cat_take_drop. reflexivity.
  }
  assert (size l = size (take n l) + size (drop n l))%nat as Hsize.
  {
    rewrite -> Hl at 1. rewrite size_cat. reflexivity.
  }
  assert (size(drop n l) = size l - n)%nat as Hsize'.
  {
    rewrite Hsize. rewrite size_take. rewrite Hlen. lia.
  }
  destruct (drop n l) eqn:Hdrop.
  - simpl in Hsize'. lia.
  - intros H. discriminate H.
Qed.

Lemma take_nil:
  forall {A} n (l: seq A),
    l <> [::] ->
    take n l = [::] ->
    n = 0%nat.
Proof.
  intros until l. intros Hnil Htake.
  destruct n.
  - reflexivity.
  - destruct l.
    + contradiction Hnil.
    + simpl in Htake. discriminate Htake.
Qed.

Lemma take_nil_l: forall {A: Type} n,
  take n (@nil A) = (@nil A).
Proof. reflexivity. Qed.

Lemma drop_n_take_1_nth:
  forall {A} (l: seq A) (dft: A) n,
    (n < size l)%nat ->
    take 1 (drop n l) = [:: nth dft l n].
Proof.
  intros until n. intros Hlen.
  replace (nth dft l n) with (nth dft l (n+0)%nat).
  rewrite <- nth_drop.
  remember (drop n l) as l'.
  erewrite (take_1_is_head l' dft).
  rewrite nth0.
  reflexivity.
  - subst l'. apply drop_not_nil. assumption.
  - replace (n + 0)%nat with n by lia.
    reflexivity.
Qed.

Lemma last_app:
  forall {A} (s: seq A),
    s = take (size s - 1) s ++ drop (size s - 1) s.
Proof.
  intros until s.
  erewrite cat_take_drop with (n0:=(size s - 1)%nat); eauto.
Qed.


Lemma iota_app: forall len1 len2,
    iota 0 (len1 + len2) = iota 0 len1 ++ iota len1 len2.
Proof.
  intros. apply iotaD.
Qed.

Lemma iota_S:
  forall a b, iota (S a) b = [seq ssrnat.addn 1 i | i <- iota a b].
Proof.
  intros.
  rewrite <- iotaDl.
  replace (ssrnat.addn 1 a) with (S a); [reflexivity|].
  ssrnat.nat_congr.
  reflexivity.
Qed.

Lemma iota_add_refl:
  forall a b, iota a b = [seq (a + i)%nat | i <- iota 0 b].
Proof.
  intros.
  rewrite <- iotaDl.
  ssrnat.nat_norm.
  reflexivity.
Qed.

Lemma iota_cons:
  forall a b,
  (b > 0)%nat ->
  iota a b = a :: iota (S a) (b - 1).
Proof.
  intros.
  replace b with (1 + (b - 1))%nat by lia.
  rewrite iotaD.
  simpl.
  replace (1 + (b - 1) - 1)%nat with (b - 1)%nat by lia.
  replace (a + 1)%nat with (S a) by lia.
  reflexivity.
Qed.
