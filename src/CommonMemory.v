(* Copyright (C) CertiK 2024-2026 *)

From Coq Require Import Arith ZArith NArith Nnat Psatz List.
From mathcomp.ssreflect Require Import seq ssreflect eqtype.

(* Notation overridden of mathcomp to Coq *)
Set Warnings "-notation-overridden".
From mathcomp.ssreflect Require Import ssrnat ssrbool ssrfun.
Set Warnings "+notation-overridden".

From mathcomp Require Import lra zify.

Require Import CommonData CommonSeq.

(** * auxilary operations 
  Auxilary operation definition and lemmas for lists and numbers
 *)

Definition seq_update {A} (s: seq A) (idx: nat) (val: A) :=
  take idx s ++ [:: val] ++ drop (idx + 1) s.

Lemma seq_update_spec: forall A (s s': seq A) (idx: nat) (val dft: A),
  (idx < size s)%nat ->
  seq_update s idx val = s' ->
  size s = size s' /\
  (forall i, i <> idx -> nth dft s i = nth dft s' i) /\
  nth dft s' idx = val.
Proof.
  intros until dft. intros Hlen H.
  split; [| split].
  - rewrite <- H.
    unfold seq_update.
    do 2 rewrite size_cat.
    rewrite size_take.
    rewrite Hlen.
    rewrite size_drop.
    simpl.
    lia.
  - intros i Hidx.
    rewrite <- H.
    unfold seq_update.
    assert (i < idx \/ i > idx)%nat as Hi by lia.
    destruct Hi as [Hlt | Hgt].
    + rewrite nth_cat.
      rewrite size_take.
      rewrite Hlen.
      rewrite Hlt.
      rewrite nth_take; [reflexivity | lia].
    + rewrite nth_cat.
      rewrite size_take.
      rewrite Hlen.
      assert (i < idx = false)%nat as Hgtb by lia.
      rewrite Hgtb.
      rewrite nth_cat.
      simpl.
      assert (i - idx < 1 = false)%nat as Hge1 by lia.
      rewrite Hge1.
      rewrite nth_drop.
      assert (idx + 1 + (i - idx - 1) = i)%nat as Hi by lia.
      rewrite Hi.
      reflexivity.
    + rewrite <- H.
      unfold seq_update.
      rewrite nth_cat.
      rewrite size_take.
      rewrite Hlen.
      assert (idx < idx = false)%nat as Hltb by lia.
      rewrite Hltb.
      rewrite nth_cat.
      simpl.
      assert (idx - idx < 1 = true)%nat as H0 by lia.
      rewrite H0.
      assert (idx - idx = 0)%nat as Ho by lia.
      rewrite Ho.
      rewrite nth0. simpl. reflexivity.
Qed.

(** * abstract list memory 
  Definition and lemmas for abstract list memory operations.
 *)

From Wasm Require Import numerics operations type_preservation memory_list.

Definition write_bytes_core (ml: bytes) (start_idx: N) (bs: bytes) : bytes :=
  take (N.to_nat start_idx) ml ++
  bs ++
  drop (N.to_nat (start_idx + N.of_nat (length bs))) ml.

Definition read_bytes_core (ml: bytes) (start_idx len: nat) : bytes :=
  take len (drop start_idx ml).

Lemma write_bytes_core_preserves_length:
  forall ml start_idx bs,
    (N.to_nat start_idx + length bs <= length ml)%nat ->
    length (write_bytes_core ml start_idx bs) = length ml.
Proof.
  intros until bs. intros Hlen. unfold write_bytes_core.
  repeat rewrite length_is_size. repeat rewrite length_is_size in Hlen.
  repeat rewrite size_cat.
  rewrite size_take.
  assert (N.to_nat start_idx < size ml \/ N.to_nat start_idx = size ml)%nat as Hlen' by lia.
  destruct Hlen' as [Hlt | Heq].
  - rewrite Hlt. rewrite size_drop. lia.
  - replace (N.to_nat start_idx < size ml)%nat with false by lia.
    rewrite size_drop. lia.
Qed.

Lemma write_bytes_core_preserves_size:
  forall ml start_idx bs,
    (N.to_nat start_idx + size bs <= size ml)%nat ->
    size (write_bytes_core ml start_idx bs) = size ml.
Proof.
  intros until bs. intros Hlen.
  rewrite <- !length_is_size.
  rewrite write_bytes_core_preserves_length; [|assumption].
  rewrite length_is_size. reflexivity.
Qed.

Lemma write_bytes_core_0:
  forall ml idx,
    write_bytes_core ml idx [::] = ml.
Proof.
  intros until idx.
  unfold write_bytes_core.
  simpl.
  replace (N.to_nat (idx + 0))%nat with (N.to_nat idx)%nat by lia.
  rewrite cat_take_drop.
  reflexivity.
Qed.

Lemma read_bytes_core_0:
  forall ml idx,
    read_bytes_core ml idx 0 = [::].
Proof.
  intros until idx.
  unfold read_bytes_core.
  rewrite take0.
  reflexivity.
Qed.


(** * read / write bytes auxiliray
  Definition and lemmas for auxiliary read / write bytes operations.
 *)
Lemma fold_left_cons:
  forall [A B : Type] (f : A -> B -> A) (l : seq B) (b : B) (acc : A),
    List.fold_left f (b :: l) acc = List.fold_left f l (f acc b).
Proof.
  intros until acc.
  simpl. reflexivity.
Qed.

Definition fold_leftin {A B} (f : nat -> A -> B -> A) (xs : list B) (acc0 : A) (n: nat) : A :=
  let '(_, acc_end) :=
    List.fold_left
      (fun '(k, acc) x =>
        ((k + 1)%nat, f k acc x))
      xs
      (n, acc0) in
  acc_end.

Lemma fold_lefti_is_fold_leftin0:
  forall [A B: Type] (f : nat -> A -> B -> A) (xs : list B) (acc0 : A),
    fold_lefti f xs acc0 = fold_leftin f xs acc0 0%nat.
Proof.
  intros until acc0.
  unfold fold_leftin. unfold fold_lefti.
  reflexivity.
Qed.

Lemma fold_lefti_cons:
  forall [A B: Type] (f: nat -> A -> B -> A) (xs: seq B) (b : B) (acc: A),
    fold_lefti f (b :: xs) acc = fold_leftin f xs (f 0%nat acc b) 1%nat.
Proof.
  intros until acc.
  unfold fold_lefti. unfold fold_leftin.
  simpl.
  reflexivity.
Qed.

Lemma fold_leftin_nil:
  forall [A B: Type] (f: nat -> A -> B -> A) (acc: A) (n: nat),
    fold_leftin f nil acc n = acc.
Proof.
  intros until n.
  unfold fold_leftin.
  simpl.
  reflexivity.
Qed.

Lemma fold_leftin_cons:
  forall [A B: Type] (f: nat -> A -> B -> A) (xs: seq B) (b : B) (acc: A) (n: nat),
    fold_leftin f (b :: xs) acc n = fold_leftin f xs (f n acc b) (n + 1)%nat.
Proof.
  intros until n.
  unfold fold_leftin.
  simpl.
  reflexivity.
Qed.

Definition write_bytes_list_n
  (ml: memory_list) (start_idx: N) (bs: bytes) (n: nat) : option memory_list :=
  fold_leftin
    (fun off dat_o b =>
      match dat_o with
      | None => None
      | Some dat =>
        let idx := BinNatDef.N.add start_idx (N.of_nat off) in
        mem_update idx b dat
      end)
    bs (Some ml) n.

Lemma write_bytes_list_n_cons:
  forall bs ml ml' start_idx b n,
    mem_update (start_idx + N.of_nat n)%num b ml = Some ml' ->
    write_bytes_list_n ml start_idx (b :: bs) n =
    write_bytes_list_n ml' start_idx bs (n + 1)%nat.
Proof.
  intros until n. intros Hupdate.
  unfold write_bytes_list_n.
  rewrite fold_leftin_cons.
  rewrite Hupdate.
  reflexivity.
Qed.

Lemma those_not_nil:
  forall A (l: list (option A)) (a : option A),
    those (a :: l) <> Some nil.
Proof.
  intros A l a.
  rewrite <- those_those0.
  simpl.
  destruct a.
  - destruct (those0 l); simpl; discriminate 1.
  - discriminate 1.
Qed.

Lemma those_nil:
  forall A,
    those (@nil (option A)) = Some (@nil A).
Proof.
  intros. rewrite <- those_those0. simpl.
  reflexivity.
Qed.

Lemma those_cons:
  forall A (a: option A) (a': A) (l: list (option A)) (l': list A),
    a = Some a' ->
    those l = Some l' ->
    those (a :: l) = Some (a' :: l').
Proof.
  intros A a a' l l' Ha Hl.
  rewrite <- those_those0 in *. subst.
  simpl. rewrite Hl. simpl. reflexivity.
Qed.

Lemma those_cons_desctruct:
  forall A (a: option A) (a': A) (l: list (option A)) (l': list A),
    those (a :: l) = Some (a' :: l') ->
    a = Some a' /\ those l = Some l'.
Proof.
  intros A a a' l l'.
  rewrite <- those_those0. simpl.
  destruct a as [b|] eqn: Ha.
  - unfold option_map. destruct (those0 l) eqn: Hthose_l.
    + inversion 1. subst.
      rewrite <- those_those0. rewrite Hthose_l.
      split; reflexivity.
    + discriminate 1.
    + discriminate 1.
Qed.

Lemma those_Some:
  forall A (l: list (option A)) (l': list A),
    those l = Some l' ->
    Forall (fun x => x <> None) l.
Proof.
  intros A.
  induction l as [|a t].
  - intros. apply Forall_nil_iff. exact I.
  - intros l' H. apply Forall_cons_iff.
    split.
    * generalize H. rewrite <- those_those0. simpl.
      destruct a eqn: Ha; [discriminate 2 | discriminate 1].
    * destruct l' as [|a' t'].
      pose proof (those_not_nil _ t a) as Hnnil.
      exfalso. apply Hnnil. exact H.
      apply (IHt t').
      eapply those_cons_desctruct in H.
      destruct H as [Ha Ht]. exact Ht.
Qed.

Lemma those_Some_forall:
  forall A (l: list (option A)) (l': list A),
    those l = Some l' ->
    Forall2 (fun x y => x = Some y) l l'.
Proof.
  intros A.
  induction l as [|a t Hind].
  - intros l' H.
    rewrite those_nil in H.
    inversion H.
    apply Forall2_nil.
  - destruct l'.
    + pose proof (those_not_nil _ t a).
      intros Hthose. rewrite Hthose in H.
      exfalso. apply H. reflexivity.
  - intros Hat.
    eapply those_cons_desctruct in Hat.
    destruct Hat as [Ha Ht].
    apply Forall2_cons_iff.
    split; [eassumption|].
    apply Hind. eassumption.
Qed.

Lemma those_forall_Some:
  forall A (l: list (option A)) (l': list A),
    Forall2 (fun x y => x = Some y) l l' ->
    those l = Some l'.
Proof.
  intros A.
  induction l as [|a t Hind].
  - destruct l'; intros.
    + apply those_nil.
    + inversion H.
  - destruct l'; intros.
    + inversion H.
    + apply those_cons.
      apply Forall2_cons_iff in H.
      destruct H as [Ha Hf].
      * eassumption.
      * apply Hind.
        apply Forall2_cons_iff in H.
        destruct H as [Ha Hf].
        eassumption.
Qed.

Lemma those_app:
  forall A (l1 l2 : list (option A)) (l1' l2' : list A),
    those l1 = Some l1' ->
    those l2 = Some l2' ->
    those (l1 ++ l2) = Some (l1' ++ l2').
Proof.
  intros until l2'. intros H1 H2.
  apply those_Some_forall in H1, H2.
  apply those_forall_Some.
  apply Forall2_app; eassumption.
Qed.

Lemma those_app_inv:
  forall A (l1 l2: list (option A)) (l' : list A),
    those (l1 ++ l2) = Some l' ->
    exists l1' l2',
      those l1 = Some l1' /\ those l2 = Some l2' /\ l' = l1' ++ l2'.
Proof.
  intros until l'. intros H.
  eapply those_Some_forall in H.
  apply Forall2_app_inv_l in H.
  destruct H as (l1' & l2' & H1 & H2 & Heq).
  exists l1'. exists l2'.
  apply those_forall_Some in H1, H2.
  split; [eassumption|].
  split; [eassumption|].
  assumption.
Qed.

Lemma mem_update_spec:
  forall ml idx val,
    (N.to_nat idx + 1 <= length ml.(ml_data))%nat ->
    mem_update idx val ml = Some {|
      ml_init := ml.(ml_init);
      ml_data := seq_update ml.(ml_data) (N.to_nat idx) val
    |}.
Proof.
  intros until val.
  intros Hlen.
  unfold mem_update.
  assert (idx <? N.of_nat (length ml.(ml_data)))%num as Hlen' by lia.
  rewrite Hlen'.
  unfold seq_update.
  reflexivity.
Qed.

Lemma mem_update_exists:
  forall ml idx val,
    (N.to_nat idx + 1 <= length ml.(ml_data))%nat ->
    exists ml', mem_update idx val ml = Some ml'.
Proof.
  intros until val. intros Hlen.
  exists {|
    ml_init := ml.(ml_init);
    ml_data := seq_update ml.(ml_data) (N.to_nat idx) val
  |}.
  apply mem_update_spec. lia.
Qed.

Lemma mem_update_succ:
  forall ml idx val ml',
    mem_update idx val ml = Some ml' ->
    (N.to_nat idx < length ml.(ml_data))%nat.
Proof.
  intros until ml'. intros Hupdate.
  unfold mem_update in Hupdate.
  destruct (N.to_nat idx <? length ml.(ml_data))%nat eqn:Hlen.
  - lia.
  - assert (idx <? N.of_nat (length ml.(ml_data)) = false)%num as Hlen' by lia.
    rewrite Hlen' in Hupdate.
    discriminate Hupdate.
Qed.

Lemma mem_update_preserves_length:
  forall ml idx val ml',
    mem_update idx val ml = Some ml' ->
    length ml.(ml_data) = length ml'.(ml_data).
Proof.
  intros until ml'. intros Hupdate.
  pose proof (mem_update_succ _ _ _ _ Hupdate) as Hlen.
  unfold mem_update in Hupdate.
  assert (idx <? N.of_nat (length ml.(ml_data)) = true)%num as Hlen' by lia.
  rewrite Hlen' in Hupdate.
  inversion Hupdate.
  destruct ml; simpl in *.
  do 2 rewrite length_is_size.
  rewrite length_is_size in Hlen.
  rewrite size_cat.
  rewrite size_take.
  rewrite Hlen.
  rewrite size_cons.
  rewrite size_drop.
  lia.
Qed.

Lemma mem_update_preserves_init:
  forall ml idx val ml',
    mem_update idx val ml = Some ml' ->
    ml.(ml_init) = ml'.(ml_init).
Proof.
  intros until ml'. intros Hupdate.
  unfold mem_update in Hupdate.
  destruct (idx <? N.of_nat (length ml.(ml_data)))%num eqn:Hlen.
  - inversion Hupdate. reflexivity.
  - discriminate Hupdate.
Qed.

Lemma mem_update_def:
  forall ml idx val,
    (N.to_nat idx + 1 <= length ml.(ml_data))%nat ->
    exists ml', mem_update idx val ml = Some ml' /\
      length ml'.(ml_data) = length ml.(ml_data) /\
      ml.(ml_init) = ml'.(ml_init).
Proof.
  intros until val. intros Hlen.
  pose proof (mem_update_exists ml idx val Hlen) as [ml' Hupdate].
  exists ml'. split; [assumption|split].
  - symmetry. eapply mem_update_preserves_length. eassumption.
  - eapply mem_update_preserves_init. eassumption.
Qed.

Lemma write_bytes_list_n_restart:
  forall bs ml start_idx n,
    (N.to_nat start_idx + n + length bs <= length ml.(ml_data))%nat ->
    write_bytes_list_n ml start_idx bs n = 
    write_bytes_list_n ml (start_idx + N.of_nat n) bs 0%nat.
Proof.
  induction bs.
  - intros until n. simpl.
    unfold write_bytes_list_n.
    do 2 rewrite fold_leftin_nil.
    reflexivity.
  - intros until n. intros Hlen.
    assert (N.to_nat start_idx + n + 1 <= length ml.(ml_data))%nat as Hlen'.
    {
      generalize Hlen. simpl. lia.
    }
    pose proof (mem_update_def ml (start_idx + N.of_nat n) a) as 
      (ml' & Hupdate & Hleneq & Hiniteq); [lia|].
    erewrite write_bytes_list_n_cons; [|eassumption].
    replace (start_idx + N.of_nat n)%num with (start_idx + N.of_nat n + 0)%num in Hupdate by lia.
    erewrite write_bytes_list_n_cons; [|eassumption].
    replace (0 + 1)%N with 1%N by lia.
    pose proof (IHbs ml' start_idx (n + 1)%nat) as Hind.
    rewrite Hind.
    pose proof (IHbs ml' (start_idx + N.of_nat n)%num 1%nat) as Hind1.
    rewrite Hind1.
    replace (start_idx + N.of_nat n + N.of_nat 1)%num with (start_idx + N.of_nat (n + 1))%num by lia.
    reflexivity.
    - generalize Hlen. rewrite Hleneq.
      repeat rewrite length_is_size. rewrite size_cons.
      autorewrite with Nnat.
      lia.
    - generalize Hlen. rewrite Hleneq.
      repeat rewrite length_is_size. rewrite size_cons.
      lia.
Qed.

(** * read / write bytes properties
  Lemmas for read / write bytes step-wise operations.
 *)

(** ** - write bytes *)

Lemma write_bytes_cons : 
  forall (bs: bytes) (mem mem': memory) (ml': memory_list) (idx: N) (b: byte),
    (N.to_nat idx + length(bs) + 1 <= mem_length mem.(mem_data))%nat ->
    mem_update idx b mem.(mem_data) = Some ml' ->
    mem'.(mem_data) = ml' ->
    mem'.(mem_max_opt) = mem.(mem_max_opt) ->
    write_bytes mem idx (b :: bs) = write_bytes mem' (idx + 1) bs.
Proof.
  intros until b. intros Hlen Hupdate Hm_data Hm_opt.
  unfold write_bytes.
  rewrite fold_lefti_cons.
  replace (idx + N.of_nat 0)%num with idx by lia.
  rewrite Hupdate.
  pose proof (write_bytes_list_n_restart bs ml' idx 1%nat) as Hrestart.
  unfold write_bytes_list_n in Hrestart.
  rewrite Hrestart.
  replace (idx + N.of_nat 1)%num with (idx + 1)%num by lia.
  rewrite Hm_data. rewrite Hm_opt.
  reflexivity.
  - assert (length ml'.(ml_data) = length mem.(mem_data).(ml_data)) as Hlen'.
    {
      erewrite <- mem_update_preserves_length. reflexivity.
      eassumption.
    }
    rewrite Hlen'.
    generalize Hlen. unfold mem_length.
    repeat rewrite length_is_size.
    lia.
Qed.

Lemma write_bytes_core_cons :
  forall ml ml' idx b bs,
    (N.to_nat idx + length(bs) + 1 <= length ml.(ml_data))%nat ->
    mem_update idx b ml = Some ml' ->
    write_bytes_core ml.(ml_data) idx (b :: bs) =
    write_bytes_core ml'.(ml_data) (idx + 1) bs.
Proof.
  intros until bs. repeat rewrite length_is_size. intros Hlen.
  unfold write_bytes_core, mem_update.
  assert (idx <? N.of_nat (size ml.(ml_data)) = true)%num as Hlen' by lia.
  rewrite Hlen'.
  assert (idx < size ml.(ml_data))%nat as Hlen'' by lia.
  destruct ml' as [init' data']; inversion 1; subst; simpl.
  rewrite take_cat.
  assert (N.to_nat idx < size (ml_data ml) = true)%nat as Hidxlen by lia.
  assert ((N.to_nat (idx + 1) < size (take (N.to_nat idx) (ml_data ml)))%N = false) as Hidx.
  {
    rewrite size_take.
    rewrite Hidxlen.
    lia.
  }
  rewrite Hidx.
  rewrite size_take.
  rewrite Hidxlen.
  replace (N.to_nat (idx + 1) - N.to_nat idx)%nat with 1%nat by lia.
  rewrite take_cons.
  rewrite take0.
  rewrite drop_cat.
  assert ((N.to_nat (idx + 1 + N.of_nat (length bs)) < size (take (N.to_nat idx) (ml_data ml)))%N = false) as Hidx''.
  {
    rewrite length_is_size. rewrite size_take.
    rewrite Hidxlen.
    lia.
  }
  rewrite Hidx''.
  rewrite size_take.
  rewrite Hidxlen.
  rewrite length_is_size.
  replace ((N.to_nat (idx + 1 + N.of_nat (size bs)) - N.to_nat idx)%nat)
    with (1 + size bs)%nat by lia.
  nat_norm.
  rewrite drop_cons.
  rewrite drop_drop.
  replace ((N.to_nat (idx + N.pos (Pos.of_succ_nat (size bs)))))
    with (size bs + N.to_nat idx + 1)%nat by lia.
  replace (size bs + (N.to_nat idx + 1)%coq_nat)%N
    with (size bs + N.to_nat idx + 1)%nat by lia.
  rewrite <- catA.
  simpl.
  reflexivity.
Qed.

Lemma write_bytes_spec : forall (bs bs': bytes) (mem: memory) (idx: N),
    (N.to_nat idx + length bs <= mem_length mem.(mem_data))%nat ->
    write_bytes_core mem.(mem_data).(ml_data) idx bs = bs' ->
    write_bytes mem idx bs = Some {| 
      mem_data := {|
        ml_init := mem.(mem_data).(ml_init);
        ml_data := bs'
      |};
      mem_max_opt := mem.(mem_max_opt)
    |}.
Proof.
  induction bs.
  - intros until idx. intros Hlen.
    unfold write_bytes.
    unfold write_bytes_core.
    simpl.
    replace (N.to_nat (idx + 0)) with (N.to_nat idx) by lia.
    rewrite cat_take_drop.
    intros Hcore.
    rewrite <- Hcore.
    do 2 f_equal.
    destruct mem, mem_data. simpl.
    reflexivity.
  - intros until idx.
    unfold mem_length.
    replace (length (a :: bs)) with (length bs + 1)%nat by (simpl; lia).
    intros Hlen Hcore.
    pose proof (mem_update_def mem.(mem_data) idx a) as 
      (ml' & Hupdate & Hlen' & Hinit).
    {
      lia.
    }
    pose (mem' := {|
      mem_data := ml';
      mem_max_opt := mem.(mem_max_opt)
    |}).
    pose proof (write_bytes_cons bs mem mem' ml' idx a) as Hcons.
    rewrite Hcons; eauto.
    pose proof (write_bytes_core_cons mem.(mem_data) ml' idx a bs) as Hcons_core.
    rewrite Hcons_core in Hcore; eauto.
    pose proof (IHbs bs' mem' (idx + 1)%num) as Hind.
    rewrite Hind; eauto.
    replace (ml_init (mem_data mem')) with (ml_init (mem_data mem)).
    replace (mem_max_opt mem') with (mem_max_opt mem).
    reflexivity.
    - subst mem'. simpl. reflexivity.
    - subst mem'. simpl.
      unfold mem_length. rewrite Hlen'.
      lia.
    - lia.
    - unfold mem_length. lia.
Qed.

Lemma write_bytes_def:
  forall (mem: memory) (idx: N) (bs: bytes),
    (N.to_nat idx + length bs <= mem_length mem.(mem_data))%nat ->
    exists mem', write_bytes mem idx bs = Some mem' /\
      mem'.(mem_data).(ml_init) = mem.(mem_data).(ml_init) /\
      mem'.(mem_max_opt) = mem.(mem_max_opt) /\
      mem'.(mem_data).(ml_data) = write_bytes_core mem.(mem_data).(ml_data) idx bs.
Proof.
  intros until bs. intros Hlen.
  pose (bs' := write_bytes_core mem.(mem_data).(ml_data) idx bs).
  pose (mem' := {|
    mem_data := {|
      ml_init := mem.(mem_data).(ml_init);
      ml_data := bs'
    |};
    mem_max_opt := mem.(mem_max_opt)
  |}).
  assert (write_bytes_core mem.(mem_data).(ml_data) idx bs = bs') as Hcore.
  {
    unfold bs'. reflexivity.
  }
  pose proof (write_bytes_spec bs bs' mem idx Hlen Hcore) as Hspec.
  exists mem'.
  split; [apply Hspec|].
  split; [reflexivity|].
  split; [reflexivity|].
  reflexivity.
Qed.

Lemma write_bytes_def':
  forall (mem: memory) (idx: N) (bs: bytes),
    ((N.to_nat idx + length bs)%coq_nat <= mem_length mem.(mem_data))%coq_nat ->
    exists mem', write_bytes mem idx bs = Some mem' /\
      mem'.(mem_data).(ml_init) = mem.(mem_data).(ml_init) /\
      mem'.(mem_max_opt) = mem.(mem_max_opt) /\
      mem'.(mem_data).(ml_data) = write_bytes_core mem.(mem_data).(ml_data) idx bs.
Proof.
  intros until bs. intros Hlen.
  assert ((N.to_nat idx + length bs <= mem_length mem.(mem_data))%nat) as Hlen' by lia.
  pose proof (write_bytes_def mem idx bs Hlen') as Hdef.
  eassumption.
Qed.

Lemma write_bytes_preserve_mem_length:
  forall (mem: memory) (idx: N) (bs: bytes) (mem': memory),
    (N.to_nat idx + length bs <= mem_length mem.(mem_data))%nat ->
    write_bytes mem idx bs = Some mem' ->
    mem_length mem.(mem_data) = mem_length mem'.(mem_data).
Proof.
  intros until mem'. intros Hlen Hwrite.
  pose proof (write_bytes_def mem idx bs Hlen) as
    (mem'' & Hwrite' & Hinit & Hmax & Hdata).
  assert (mem'' = mem') as Hmem'.
  {
    rewrite Hwrite in Hwrite'. inversion Hwrite'. reflexivity.
  }
  subst mem''.
  unfold mem_length.
  rewrite Hdata.
  f_equal.
  rewrite write_bytes_core_preserves_length; [reflexivity|].
  unfold mem_length in Hlen.
  lia.
Qed.

Lemma write_bytes_preserve_mem_length':
  forall (mem: memory) (idx: N) (bs: bytes) (mem': memory),
    ((N.to_nat idx + length bs)%coq_nat <= mem_length mem.(mem_data))%coq_nat ->
    write_bytes mem idx bs = Some mem' ->
    mem_length mem.(mem_data) = mem_length mem'.(mem_data).
Proof.
  intros until mem'. intros Hlen Hwrite.
  assert ((N.to_nat idx + length bs <= mem_length mem.(mem_data))%nat) as Hlen' by lia.
  eapply write_bytes_preserve_mem_length; eassumption.
Qed.

(** ** - read bytes *)

Lemma read_bytes_length: forall mem start_idx len bs,
    read_bytes mem start_idx len = Some bs ->
    length bs = len.
Proof.
  intros until bs. intros H.
  unfold read_bytes in H.
  apply those_length in H.
  rewrite <- H.
  rewrite map_length. rewrite length_is_size.
  rewrite size_iota.
  reflexivity.
Qed.

Lemma read_bytes_0:
  forall mem idx,
    read_bytes mem idx 0 = Some nil.
Proof.
  intros until idx.
  unfold read_bytes.
  simpl.
  rewrite those_nil.
  reflexivity.
Qed.

Lemma read_bytes_cons:
  forall mem idx len bs b,
    (N.to_nat idx + len <= mem_length mem.(mem_data))%nat ->
    read_bytes mem idx len = Some (b :: bs) ->
    read_bytes mem (idx + 1) (len - 1) = Some bs /\
    nth #00 mem.(mem_data).(ml_data) (N.to_nat idx) = b.
Proof.
  intros until b. intros Hlen Hread.
  assert (len = length (b :: bs))%nat as Hlen'.
  {
    apply read_bytes_length in Hread. lia.
  }
  assert (len > 0)%nat as Hlen''.
  {
    generalize Hlen'. simpl. lia.
  }
  unfold read_bytes in Hread.
  rewrite iota_cons in Hread; [|lia].
  rewrite List.map_cons in Hread.
  pose proof (those_cons_desctruct _ _ _ _ _ Hread) as [Hb Hbs].
  split.
  - (* tail *)
    unfold read_bytes.
    rewrite iota_S in Hbs.
    rewrite List.map_map in Hbs.
    rewrite <- Hbs.
    f_equal. f_equal.
    apply FunctionalExtensionality.functional_extensionality.
    intros x.
    replace ((idx + N.of_nat (1 + x))%num) with (idx + 1 + N.of_nat x)%num by lia.
    reflexivity.
  - (* head *)
    generalize Hb.
    replace ((idx + N.of_nat 0)%num) with idx by lia.
    unfold mem_lookup.
    assert ((N.to_nat idx) < length (ml_data (mem_data mem)))%nat as Hidx.
    {
      generalize Hlen. unfold mem_length. simpl. lia.
    }
    erewrite nth_error_nth; [|lia].
    inversion 1.
    reflexivity.
Qed.

Lemma read_bytes_core_cons:
  forall ml idx len bs b,
    (idx + len <= length ml)%nat ->
    read_bytes_core ml idx len = b :: bs ->
    read_bytes_core ml idx 1 = [:: b] /\
    read_bytes_core ml (idx + 1) (len - 1) = bs.
Proof.
  intros until b. intros Hlen.
  unfold read_bytes_core.
  intros Hread.
  assert (len > 0)%nat as Hlen'.
  {
    apply take_size_gt0 in Hread. lia.
  }
  pose proof (take_1_cons ((drop idx ml)) bs b len Hread) as [Htake Hdrop].
  rewrite drop_drop in Hdrop.
  replace ((1 + idx)%nat) with (idx + 1)%nat in Hdrop by lia.
  split; assumption.
Qed.

Lemma read_bytes_core_cons_inv:
  forall (ml: bytes) idx len bs b dft,
    (len > 0)%nat ->
    (idx + len <= length ml)%nat ->
    read_bytes_core ml (idx + 1) (len - 1) = bs ->
    nth dft ml idx = b ->
    read_bytes_core ml idx len = b :: bs.
Proof.
  intros until dft. intros Hlen Hidx Hdrop Hnth.
  unfold read_bytes_core.
  apply take_1_cons_inv.
  - assumption.
  - erewrite drop_n_take_1_nth with (dft:=dft).
    f_equal. assumption.
  - rewrite length_is_size in Hidx.
    lia.
  - unfold read_bytes_core in Hdrop.
    rewrite drop_drop.
    replace (1 + idx)%nat with (idx + 1)%nat by lia.
    assumption.
Qed.

Lemma read_bytes_def:
  forall (bs: bytes) (mem: memory) (idx: N) (len: nat),
    (N.to_nat idx + len <= mem_length mem.(mem_data))%nat ->
    read_bytes mem idx len = Some bs ->
    read_bytes_core mem.(mem_data).(ml_data) (N.to_nat idx) len = bs.
Proof.
  induction bs.
  - (* bs = nil *)
    intros until len. intros Hlen Hread.
    assert (len = 0)%nat as Hlen'.
    {
      apply read_bytes_length in Hread.
      simpl in Hread. lia.
    }
    subst len.
    unfold read_bytes_core.
    rewrite take0.
    reflexivity.
  - intros until len. intros Hlen Hread.
    assert (len = length (a :: bs))%nat as Hlen'.
    {
      apply read_bytes_length in Hread. lia.
    }
    pose proof (read_bytes_cons mem idx len bs a Hlen Hread) as [Hcons Ha].
    assert (N.to_nat idx + len <= length (ml_data (mem_data mem)))%N as Hidx.
    {
      unfold mem_length in Hlen. lia.
    }
    assert (len > 0)%nat.
    {
      generalize Hlen'. simpl. lia.
    }
    apply read_bytes_core_cons_inv with (dft:=#00); try assumption.
    pose proof (IHbs mem (idx + 1)%num (len - 1)%nat) as Hind.
    replace ((N.to_nat (idx + 1))) with ((N.to_nat idx + 1)%nat) in Hind by lia.
    apply Hind; eauto.
    lia.
Qed.

Lemma read_bytes_cons_inv:
  forall (bs: bytes) (mem: memory) (idx: N) (b: byte),
    (N.to_nat idx + (size bs) + 1 <= mem_length mem.(mem_data))%nat ->
    read_bytes mem (idx + 1) (size bs) = Some bs ->
    nth #00 mem.(mem_data).(ml_data) (N.to_nat idx) = b ->
    read_bytes mem idx (size bs + 1) = Some (b :: bs).
Proof.
  intros until b. intros Hlen Hread Hnth.
  unfold read_bytes.
  assert (0 <= size bs)%nat as Hbs by lia.
  assert (N.to_nat idx < size (ml_data (mem_data mem)))%N as Hidx.
  {
    unfold mem_length in Hlen. 
    rewrite length_is_size in Hlen. lia.
  }
  rewrite iota_cons; [|lia].
  rewrite List.map_cons.
  erewrite those_cons with (a':=b)(l':=bs).
  - reflexivity.
  - replace ((idx + N.of_nat 0)%num) with idx by lia.
    unfold mem_lookup.
    erewrite nth_error_nth with (x:=#00).
    f_equal.
    assumption.
    rewrite length_is_size. fold byte.
    lia.
  - replace (size bs + 1 - 1)%nat with (size bs)%nat by lia.
    unfold read_bytes in Hread.
    rewrite iota_S.
    rewrite List.map_map.
    fold bytes.
    rewrite <- Hread.
    f_equal. f_equal.
    apply FunctionalExtensionality.functional_extensionality.
    intros x.
    replace ((idx + N.of_nat (1 + x))%num) with ((idx + 1 + N.of_nat x)%num)
      by lia.
    reflexivity.
Qed.

Lemma read_bytes_spec:
  forall (bs: bytes) (mem: memory) (idx: N),
    (N.to_nat idx + (size bs) <= mem_length mem.(mem_data))%nat ->
    read_bytes_core mem.(mem_data).(ml_data) idx (size bs) = bs ->
    read_bytes mem idx (size bs) = Some bs.
Proof.
  induction bs.
  - intros until idx. intros Hlen Hread.
    simpl.
    unfold read_bytes.
    rewrite those_nil.
    reflexivity.
  - intros until idx. intros Hlen Hread.
    assert (size (a :: bs) = (size bs + 1)%nat) as Hlen'.
    {
      simpl. lia.
    }
    rewrite Hlen'.
    apply read_bytes_cons_inv.
    + lia.
    + pose proof (IHbs mem (idx + 1)%num) as Hind.
      apply Hind.
      * lia.
      * apply read_bytes_core_cons in Hread. destruct Hread as [Hhead Htail].
        simpl in Htail.
        replace (((size bs).+1 - 1)%nat) with (size bs) in Htail by lia.
        rewrite <- Htail at 2.
        f_equal. lia.
      * unfold mem_length in Hlen.
        lia.
      + apply read_bytes_core_cons in Hread.
        * destruct Hread as [Hhead Htail].
          unfold read_bytes_core in Hhead.
          erewrite drop_n_take_1_nth with (dft:=#00) in Hhead.
        * inversion Hhead. f_equal. lia.
        * unfold mem_length in Hlen.
          rewrite length_is_size in Hlen.
          simpl in Hlen.
          fold byte.
          lia.
        * unfold mem_length in Hlen.
          lia.
Qed.

Lemma read_bytes_core_length:
  forall ml idx len bs,
    (N.to_nat idx + len <= size ml)%nat ->
    read_bytes_core ml idx len = bs ->
    length bs = len.
Proof.
  intros until bs. intros Hlen Hread.
  unfold read_bytes_core in Hread.
  rewrite length_is_size.
  rewrite <- Hread.
  rewrite size_take.
  assert ((N.to_nat idx + len < size ml)%N \/ (N.to_nat idx + len = size ml)%N) 
    as Hlen' by lia.
  destruct Hlen' as [Hlen' | Hlen'].
  - replace ((len < size (drop idx ml))%N) with true.
    + reflexivity.
    + rewrite size_drop.
      lia.
  - assert (len = size ml - N.to_nat idx)%nat as Hlen'' by lia.
    rewrite Hlen''.
    rewrite size_drop.
    rewrite N2nat_id.
    replace (size ml - N.to_nat idx < size ml - N.to_nat idx)%nat with false
      by lia.
    reflexivity.
Qed.

Lemma read_bytes_some:
  forall mem idx len,
    (N.to_nat idx + len <= mem_length mem.(mem_data))%nat ->
    exists bs, read_bytes mem idx len = Some bs.
Proof.
  intros until len. intros Hlen.
  exists (read_bytes_core mem.(mem_data).(ml_data) (N.to_nat idx) len).
  remember (read_bytes_core mem.(mem_data).(ml_data) (N.to_nat idx) len) as bs.
  symmetry in Heqbs.
  assert (size bs = len)%nat as Hlen'.
  {
    rewrite <- length_is_size.
    pose proof (read_bytes_core_length mem.(mem_data).(ml_data) idx len bs) as Hlen''.
    apply Hlen''.
    - unfold mem_length in Hlen. rewrite length_is_size in Hlen.
      lia.
    - rewrite <- Heqbs. f_equal. rewrite N2nat_id. reflexivity.
  }
  rewrite <- Hlen'.
  apply read_bytes_spec.
  - lia.
  - rewrite <- Heqbs at 2.
    rewrite <- Hlen'.
    f_equal.
    lia.
Qed.

Lemma read_bytes_not_none:
  forall mem idx len,
    (N.to_nat idx + len <= mem_length mem.(mem_data))%nat ->
    read_bytes mem idx len <> None.
Proof.
  intros until len. intros Hlen.
  pose proof (read_bytes_some mem idx len Hlen) as (bs & Hbs).
  rewrite Hbs.
  discriminate.
Qed.

Lemma read_written_bytes_core_same:
  forall (ml ml': bytes) (idx: N) (bs: bytes),
    (N.to_nat idx + size bs <= size ml)%nat ->
    write_bytes_core ml idx bs = ml' ->
    read_bytes_core ml' idx (size bs) = bs.
Proof.
  intros until bs. intros Hlen Hwrite.
  rewrite <- Hwrite.
  assert (size bs = 0 \/ size bs > 0)%nat as Hbs by lia.
  destruct Hbs as [Hbs | Hbs].
  - apply size0nil in Hbs.
    subst bs.
    rewrite size_nil_eq.
    rewrite read_bytes_core_0.
    reflexivity.
  - assert (N.to_nat idx < size ml)%nat as Hidx by lia.
    unfold read_bytes_core, write_bytes_core.
    rewrite take_drop.
    rewrite take_cat.
    rewrite size_take.
    rewrite Hidx.
    replace ((size bs + idx < N.to_nat idx)%nat) with false by lia.
    replace ((size bs + idx - N.to_nat idx)%nat) with (size bs)%nat by lia.
    rewrite take_cat.
    replace (size bs < size bs)%nat with false by lia.
    replace (size bs - size bs)%nat with 0%nat by lia.
    rewrite take0.
    rewrite drop_cat. rewrite size_take.
    rewrite Hidx.
    replace (idx < N.to_nat idx)%N with false by lia.
    replace (idx - N.to_nat idx)%N with 0%N by lia.
    rewrite drop0.
    rewrite cats0.
    reflexivity.
Qed.

Lemma read_written_bytes_core_others:
  forall (ml ml': bytes) (idx: N) (bs: bytes),
    (N.to_nat idx + size bs <= size ml)%nat ->
    write_bytes_core ml idx bs = ml' ->
    forall (i: N) (bo: bytes),
      (i + size bo <= idx \/ (idx + size bs <= i /\ i + size bo <= size ml))%nat ->
      read_bytes_core ml i (size bo) = bo ->
      read_bytes_core ml' i (size bo) = bo.
Proof.
  intros until bs. intros Hlen Hwrite i bo Hidx Hread.
  rewrite <- Hwrite.
  assert (size bs = 0 \/ size bs > 0)%nat as Hbs by lia.
  destruct Hbs as [Hbs | Hbs].
  - (* bs == 0 *)
    apply size0nil in Hbs.
    subst bs.
    rewrite write_bytes_core_0.
    exact Hread.
  - assert (size bo = 0 \/ size bo > 0)%nat as Hbo by lia.
    destruct Hbo as [Hbo | Hbo].
    + apply size0nil in Hbo.
      subst bo.
      rewrite size_nil_eq.
      rewrite read_bytes_core_0.
      reflexivity.
    + unfold read_bytes_core, write_bytes_core.
      rewrite take_drop.
      rewrite take_cat.
      rewrite size_take.
      assert (N.to_nat idx < size ml)%nat as Hidx' by lia.
      rewrite Hidx'.
      destruct Hidx as [Hidx | [Hidx_lo Hidx_hi]].
      * (* left region: 0 <= i + size bo <= idx *)
        assert (i + size bo < N.to_nat idx \/ size bo + i = N.to_nat idx)%nat 
          as Hidx'' by lia.
        destruct Hidx'' as [Hidx'' | Hidx''].
        - replace (size bo + i < N.to_nat idx)%N with true by lia.
          rewrite take_takel; [|lia].
          rewrite <- take_drop.
          unfold read_bytes_core in Hread.
          assumption.
        - replace (size bo + i < N.to_nat idx)%nat with false by lia.
          rewrite Hidx''.
          replace (N.to_nat idx - N.to_nat idx)%nat with 0%nat by lia.
          rewrite take0.
          rewrite cats0.
          unfold read_bytes_core in Hread.
          rewrite take_drop in Hread.
          rewrite Hidx'' in Hread.
          assumption.
      * (* right region: idx + size bs <= i + size bo <= size ml *)
        replace (size bo + i < N.to_nat idx)%N with false by lia.
        rewrite drop_cat. rewrite size_take.
        replace (N.to_nat idx < size ml)%nat with true by lia.
        replace (i < N.to_nat idx)%N with false by lia.
        rewrite take_cat.
        replace ((size bo + i - N.to_nat idx < size bs)%N) with false by lia.
        rewrite length_is_size.
        replace ((N.to_nat (idx + N.of_nat (size bs)))%nat) with (N.to_nat idx + size bs)%nat by lia.
        rewrite drop_cat.
        replace ((i - N.to_nat idx < size bs)%N) with false by lia.
        replace ((size bo + i - N.to_nat idx - size bs)%nat) with
          ((size bo + (i - N.to_nat idx - size bs))%nat) by lia.
        rewrite <- take_drop.
        rewrite drop_drop.
        replace (i - N.to_nat idx - size bs + (N.to_nat idx + size bs))%nat
          with (N.to_nat i)%nat by lia.
        unfold read_bytes_core in Hread.
        rewrite <- N2nat_id.
        assumption.
Qed.

Lemma read_written_bytes_core_others_eq:
  forall (ml ml': bytes) (idx: N) (bs: bytes),
    (N.to_nat idx + size bs <= size ml)%nat ->
    write_bytes_core ml idx bs = ml' ->
    forall (i: N) (len: nat),
      (i + len <= idx \/ (idx + size bs <= i /\ i + len <= size ml))%nat ->
      read_bytes_core ml' i len = read_bytes_core ml i len.
Proof.
  intros until bs. intros Hlen Hwrite i len Hidx.
  remember (read_bytes_core ml i len) as bo.
  symmetry in Heqbo.
  assert (len = size bo) as Hbs.
  {
    rewrite <- length_is_size.
    erewrite read_bytes_core_length with (ml:=ml)(bs:=bo)(idx:=i)(len:=len).
    - reflexivity.
    - lia.
    - assumption.
  }
  rewrite Hbs.
  rewrite Hbs in Heqbo.
  repeat rewrite Hbs in Hidx.
  eapply read_written_bytes_core_others with (ml:=ml) (bs:=bs) (bo:=bo) (idx:=idx);
    eauto.
Qed.

Lemma read_written_bytes_same:
  forall (mem mem': memory) (idx: N) (bs: bytes),
    (N.to_nat idx + size bs <= mem_length mem.(mem_data))%nat ->
    write_bytes mem idx bs = Some mem' ->
    read_bytes mem' idx (size bs) = Some bs.
Proof.
  intros until bs. intros Hlen Hwrite.
  pose proof (write_bytes_def mem idx bs Hlen) as (mem'' & Hwrite' & Hinit & Hmax & Hdata).
  rewrite Hwrite in Hwrite'. inversion Hwrite'. subst mem''.
  clear Hwrite'.
  assert (mem_length (mem_data mem) = mem_length (mem_data mem')) as Hplen.
  {
    eapply write_bytes_preserve_mem_length with (idx:=idx) (bs:=bs).
    - rewrite length_is_size. assumption.
    - assumption. 
  }
  apply read_bytes_spec.
  - rewrite <- Hplen. assumption.
  - remember (ml_data (mem_data mem)) as ml.
    remember (ml_data (mem_data mem')) as ml'.
    pose proof (read_written_bytes_core_same ml ml' idx bs) as Hread.
    apply Hread.
    + subst ml. 
      unfold mem_length in Hlen. rewrite length_is_size in Hlen. 
      lia.
    + rewrite Hdata. reflexivity.
Qed.

Lemma read_written_bytes_core_same':
  forall (mem: memory) (idx: N) (bs ml': bytes),
    (N.to_nat idx + size bs <= mem_length mem.(mem_data))%nat ->
    write_bytes_core mem.(mem_data).(ml_data) idx bs = ml' ->
    read_bytes {|
      mem_data := {|
        ml_init := mem.(mem_data).(ml_init);
        ml_data := ml' |};
      mem_max_opt := mem.(mem_max_opt)
    |} idx (size bs) = Some bs.
Proof.
  intros until ml'. intros Hlen Hwrite.
  remember {|
    mem_data := {|
      ml_init := ml_init (mem_data mem);
      ml_data := ml' |};
    mem_max_opt := mem_max_opt mem
  |} as mem'.
  assert ((ml_data (mem_data mem')) = ml') as  Hml'.
  {
    subst mem'. simpl. reflexivity.
  }
  assert ((N.to_nat idx + size bs <= size (ml_data (mem_data mem)))%N) as Hlen'.
  {
    unfold mem_length in Hlen. rewrite length_is_size in Hlen. lia.
  }
  assert ((N.to_nat idx + length bs <= length (ml_data (mem_data mem)))%N) as Hlen''.
  {
    repeat rewrite length_is_size. lia.
  }
  assert (mem_length (mem_data mem) = mem_length (mem_data mem')) as Hplen.
  {
    unfold mem_length. f_equal. rewrite Heqmem'. simpl. 
    rewrite <- Hwrite.
    erewrite write_bytes_core_preserves_length with (start_idx:=idx) (bs:=bs).
    - reflexivity.
    - lia.
  }
  apply read_bytes_spec.
  - rewrite <- Hplen. assumption.
  - pose proof (read_written_bytes_core_same (ml_data (mem_data mem)) ml' idx bs) as Hread.
    rewrite Hml'.
    apply Hread.
    + assumption.
    + assumption.
Qed.

Lemma read_written_bytes_core_others':
  forall (mem: memory) (idx: N) (bs ml': bytes),
    (N.to_nat idx + size bs <= mem_length mem.(mem_data))%nat ->
    write_bytes_core mem.(mem_data).(ml_data) idx bs = ml' ->
    forall (i: N) (len: nat),
      (i + len <= idx \/ (idx + size bs <= i /\ i + len <= mem_length mem.(mem_data)))%nat ->
      read_bytes {|
        mem_data := {|
          ml_init := mem.(mem_data).(ml_init);
          ml_data := ml' |};
        mem_max_opt := mem.(mem_max_opt)
      |} i len = read_bytes mem i len.
Proof.
  intros until ml'. intros Hlen Hwrite i len Hidx.
  remember {|
    mem_data := {|
      ml_init := ml_init (mem_data mem);
      ml_data := ml' |};
    mem_max_opt := mem_max_opt mem
  |} as mem'.
  assert ((ml_data (mem_data mem')) = ml') as  Hml'.
  {
    subst mem'. simpl. reflexivity.
  }
  assert ((N.to_nat idx + size bs <= size (ml_data (mem_data mem)))%N) as Hlen'.
  {
    unfold mem_length in Hlen. rewrite length_is_size in Hlen. lia.
  }
  assert ((N.to_nat idx + length bs <= length (ml_data (mem_data mem)))%N) as Hlen''.
  {
    repeat rewrite length_is_size. lia.
  }
  assert (mem_length (mem_data mem) = mem_length (mem_data mem')) as Hplen.
  {
    unfold mem_length. f_equal. rewrite Heqmem'. simpl. 
    rewrite <- Hwrite.
    erewrite write_bytes_core_preserves_length with (start_idx:=idx) (bs:=bs).
    - reflexivity.
    - lia.
  }
  assert (0 <= size bs)%nat as Hbs by lia.
  assert (0 <= len)%nat as Hbolen by lia.
  assert (N.to_nat i <= size (ml_data (mem_data mem)))%N as Hi.
  {
    unfold mem_length in Hidx. rewrite length_is_size in Hidx. lia.
  }
  assert (i + len <= size (ml_data (mem_data mem)))%N as Hi'.
  {
    unfold mem_length in Hidx. rewrite length_is_size in Hidx. lia.
  }
  remember (read_bytes mem i len) as sbo.
  destruct sbo as [bo|] eqn: Hbo.
  - symmetry in Heqsbo.
    pose proof (read_bytes_length mem i len bo Heqsbo) as Hbol.
    rewrite <- Hbol.
    rewrite length_is_size.
    apply read_bytes_spec.
    + rewrite <- Hplen.
      rewrite <- Hbol in Hi'.
      rewrite length_is_size in Hi'.
      unfold mem_length. rewrite length_is_size. lia.
    + pose proof (read_written_bytes_core_others (ml_data (mem_data mem)) ml' idx bs) as Hread.
      rewrite Hml'.
      apply Hread.
      * assumption.
      * assumption.
      * assert (size bo = len) as Hbo'.
        {
          rewrite <- Hbol. rewrite length_is_size. reflexivity.
        }
        lia.
      * eapply read_bytes_def in Heqsbo.
        rewrite <- Heqsbo at 2.
        rewrite <- Hbol.
        rewrite length_is_size.
        f_equal. lia.
      * lia.
  - pose proof (read_bytes_not_none mem i len) as Hnone.
    rewrite <- Heqsbo in Hnone.
    contradiction Hnone.
    lia.
    reflexivity.
Qed.

Lemma read_written_bytes_others:
  forall (mem mem': memory) (idx: N) (bs: bytes),
    (N.to_nat idx + size bs <= mem_length mem.(mem_data))%nat ->
    write_bytes mem idx bs = Some mem' ->
    forall (i: N) (len: nat),
      (i + len <= idx \/ (idx + size bs <= i /\ i + len <= mem_length mem.(mem_data)))%nat ->
      read_bytes mem' i len = read_bytes mem i len.
Proof.
  intros until bs. intros Hlen Hwrite i len Hidx.
  pose proof (write_bytes_def mem idx bs Hlen) as (mem'' & Hwrite' & Hinit & Hmax & Hdata).
  rewrite Hwrite in Hwrite'. inversion Hwrite'. subst mem''.
  clear Hwrite'.
  remember (ml_data (mem_data mem)) as ml.
  remember (write_bytes_core ml idx bs) as ml'.
  assert (mem' = {|
    mem_data := {|
      ml_init := ml_init (mem_data mem);
      ml_data := ml'
    |};
    mem_max_opt := mem_max_opt mem
  |}) as Hmem'.
  {
    destruct mem' as [mem_data' mem_max_opt'] eqn: Hmem'; simpl in *.
    destruct mem_data' as [ml_init' ml_data'] eqn: Hmem_data'; simpl in *.
    rewrite Hinit Hdata Hmax.
    reflexivity.
  }
  rewrite Hmem'.
  symmetry in Heqml'.
  rewrite Heqml in Heqml'.
  eapply read_written_bytes_core_others' with (mem:=mem) (ml':=ml') (bs:=bs)
    (idx:=idx) (i:=i) (len:=len); eauto.
Qed.

Lemma read_written_bytes_core_full:
  forall (idx: N) (ml bs ml': bytes),
    (N.to_nat idx + size bs <= size ml)%nat ->
    write_bytes_core ml idx bs = ml' ->
    read_bytes_core ml' idx (size bs) = bs /\
    forall (i: N) (len: nat),
      (i + len <= idx \/ (idx + size bs <= i /\ i + len <= size ml))%nat ->
      read_bytes_core ml' i len = read_bytes_core ml i len.
Proof.
  intros until ml'. intros Hlen Hwrite.
  split.
  - eapply read_written_bytes_core_same; eassumption.
  - intros i len Hidx.
    eapply read_written_bytes_core_others_eq; eauto.
Qed.

Lemma read_written_bytes_full:
  forall (mem mem': memory) (idx: N) (bs: bytes),
    (N.to_nat idx + size bs <= mem_length mem.(mem_data))%nat ->
    write_bytes mem idx bs = Some mem' ->
    read_bytes mem' idx (size bs) = Some bs /\
    forall (i: N) (len: nat),
      (i + len <= idx \/ (idx + size bs <= i /\ i + len <= mem_length mem.(mem_data)))%nat ->
      read_bytes mem' i len = read_bytes mem i len.
Proof.
  intros until bs. intros Hlen Hwrite.
  split.
  - eapply read_written_bytes_same; eassumption.
  - intros i len Hidx.
    eapply read_written_bytes_others; eauto.
Qed.

Lemma write_bytes_some:
  forall (mem: memory) (idx: N) (bs: bytes),
    (N.to_nat idx + size bs <= mem_length mem.(mem_data))%nat ->
    exists mem', write_bytes mem idx bs = Some mem'.
Proof.
  intros until bs. intros Hlen.
  exists ({|
    mem_data := {|
      ml_init := mem.(mem_data).(ml_init);
      ml_data := write_bytes_core mem.(mem_data).(ml_data) idx bs
    |};
    mem_max_opt := mem.(mem_max_opt)
  |}).
  eapply write_bytes_spec; eauto.
Qed.

Lemma read_written_bytes_full_exists:
  forall (mem: memory) (idx: N) (bs: bytes),
    (N.to_nat idx + size bs <= mem_length mem.(mem_data))%nat ->
    exists mem', write_bytes mem idx bs = Some mem' /\
      read_bytes mem' idx (size bs) = Some bs /\
      forall (i: N) (len: nat),
        (i + len <= idx \/ (idx + size bs <= i /\ i + len <= mem_length mem.(mem_data)))%nat ->
        read_bytes mem' i len = read_bytes mem i len.
Proof.
  intros until bs. intros Hlen.
  pose proof (write_bytes_some mem idx bs Hlen) as (mem' & Hwrite).
  exists mem'.
  split; [assumption|].
  eapply read_written_bytes_full; eauto.
Qed.

(** * zkwasm heap relation
  For a given memory, we define a relation between the WasmCert list memory and
  a heap.
 *)

From Wasm Require Import bytes.
From compcert Require Import Integers Memdata Archi.
Transparent Archi.big_endian.

Require Import Shared.
Require Import OpStoreModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Lemma write_bytes_preserve_mem_max_opt:
  forall (mem mem': memory) (idx: N) (bs: bytes),
  (N.to_nat idx + length bs <= mem_length (mem_data mem))%N ->
  write_bytes mem idx bs = Some mem' ->
  mem.(mem_max_opt) = mem'.(mem_max_opt).
Proof.
  intros until bs. intros Hidx Hwrite.
  pose proof (write_bytes_def mem idx bs Hidx) as Hwrite'.
  destruct Hwrite' as (mem'e & Hwrite' & Hinit & Hmaxopt & Hdata).
  rewrite Hwrite in Hwrite'.
  inversion Hwrite'. subst mem'e. clear Hwrite'.
  rewrite Hmaxopt.
  reflexivity.
Qed.

Lemma write_bytes_preserve_ml_init:
  forall (mem mem': memory) (idx: N) (bs: bytes),
  (N.to_nat idx + length bs <= mem_length (mem_data mem))%N ->
  write_bytes mem idx bs = Some mem' ->
  mem.(mem_data).(ml_init) = mem'.(mem_data).(ml_init).
Proof.
  intros until bs. intros Hidx Hwrite.
  pose proof (write_bytes_def mem idx bs Hidx) as Hwrite'.
  destruct Hwrite' as (mem'e & Hwrite' & Hinit & Hmaxopt & Hdata).
  rewrite Hwrite in Hwrite'.
  inversion Hwrite'. subst mem'e. clear Hwrite'.
  rewrite Hinit.
  reflexivity.
Qed.

Definition rel_heap_valid (mem: memory): Prop :=
  ml_valid mem.(mem_data).

Lemma write_bytes_preserve_heap_valid:
  forall (mem mem': memory) (blk: N) (bs: bytes),
    (N.to_nat blk + length bs <= mem_length (mem_data mem))%N ->
    write_bytes mem blk bs = Some mem' ->
    rel_heap_valid mem ->
    rel_heap_valid mem'.
Proof.
  intros until bs. intros Hblk Hwrite.
  pose proof (write_bytes_preserve_mem_length mem blk bs mem' Hblk Hwrite) as Hlen.
  unfold rel_heap_valid, ml_valid.
  rewrite Hlen.
  eauto.
Qed.

Definition rel_heap_bounded (m: map) (size: Z): Prop :=
  forall block z,
    get m block = Some z -> 
    (8 * block + 8) <= (Z.of_N operations.page_size) * size.

Opaque page_size.

Lemma mem_length_is_page_size:
  forall mem,
    (mem_length mem.(mem_data) mod page_size = 0)%num ->
    mem_length mem.(mem_data) = (page_size * (mem_size mem))%num.
Proof.
  intros mem Hmod.
  unfold mem_size, operations.mem_length.
  pose proof (N.Div0.div_exact (mem_length (mem_data mem)) page_size) as Hdiv.
  apply proj2 in Hdiv.
  rewrite <- Hdiv; [|lia].
  reflexivity.
Qed.

Definition rel_heap_size (size: Z) (mem: memory): Prop :=
  size = Z.of_N (mem_size mem).

Lemma write_bytes_preserve_heap_size:
  forall (mem mem': memory) (size: Z) (blk: N) (bs: bytes),
    (N.to_nat blk + length bs <= mem_length (mem_data mem))%N ->
    write_bytes mem blk bs = Some mem' ->
    rel_heap_size size mem ->
    rel_heap_size size mem'.
Proof.
  intros until bs. intros Hblk Hwrite.
  pose proof (write_bytes_preserve_mem_length mem blk bs mem' Hblk Hwrite) as Hlen.
  unfold rel_heap_size, mem_size, operations.mem_length.
  rewrite Hlen.
  eauto.
Qed.

Lemma write_bytes_preserve_heap_bounded:
  forall (m m': map) (mem: memory) (size: Z) (blk: Z) (val: Z),
    (8 * Z.to_nat blk + 8 <= mem_length (mem_data mem))%N ->
    m' = set m blk val ->
    rel_heap_size size mem ->
    rel_heap_valid mem ->
    rel_heap_bounded m size ->
    rel_heap_bounded m' size.
Proof.
  intros until val. intros Hblk Hset Hsize Hvalid.
  unfold rel_heap_bounded.
  intros Hbounded block z Hget.
  unfold rel_heap_valid, ml_valid in Hvalid.
  assert (block = blk \/ block <> blk) as Hblock by lia.
  destruct Hblock as [Hblock | Hblock].
  - subst blk.
    rewrite mem_length_is_page_size in Hblk; [|lia].
    unfold rel_heap_size in Hsize.
    assert (mem_size mem = Z.to_N size) as Hsize' by lia.
    rewrite Hsize' in Hblk.
    lia.
  - rewrite Hset in Hget.
    rewrite gso in Hget; [|lia].
    specialize Hbounded with (block:=block)(z:=z).
    apply Hbounded.
    assumption.
Qed.

Lemma write_bytes_preserve_heap_bounded':
  forall (m: map) (mem: memory) (size: Z) (blk: Z) (val: Z),
    (8 * Z.to_nat blk + 8 <= mem_length (mem_data mem))%N ->
    rel_heap_size size mem ->
    rel_heap_valid mem ->
    rel_heap_bounded m size ->
    rel_heap_bounded (set m blk val) size.
Proof.
  intros until val. intros Hblk Hsize Hvalid Hbounded.
  remember (set m blk val) as m'.
  eapply write_bytes_preserve_heap_bounded; eauto.
Qed.

Definition rel_heap_limit (limit: Z) (mem: memory): Prop :=
  mem_max_opt mem = Some (Z.to_N limit).

Lemma write_bytes_preserve_heap_limit:
  forall (mem mem': memory) (limit: Z) (idx: N) (bs: bytes),
    (N.to_nat idx + length bs <= mem_length (mem_data mem))%N ->
    write_bytes mem idx bs = Some mem' ->
    rel_heap_limit limit mem ->
    rel_heap_limit limit mem'.
Proof.
  intros until bs. intros Hidx Hwrite.
  pose proof (write_bytes_preserve_mem_max_opt mem mem' idx bs Hidx Hwrite) 
    as Hmaxopt.
  unfold rel_heap_limit.
  rewrite Hmaxopt.
  eauto.
Qed.

Lemma heap_rel_write_core: forall m p mp mem blk val,
  heap_rel m p mp mem ->
  0 <= blk ->
  0 <= val < 2^64 ->
  8 * blk + 8 <= Z.of_N (mem_length mem.(mem_data)) ->
  exists ml',
    write_bytes_core mem.(mem_data).(ml_data) (8 * Z.to_N blk) (Memdata.encode_int 8 val) = ml' /\
    heap_rel (set m blk val) p mp {|
      mem_data := {|
        ml_init := mem.(mem_data).(ml_init);
        ml_data := ml'
      |};
      mem_max_opt := mem.(mem_max_opt)
    |}.
Proof.
  intros until val. intros Hheap.
  generalize Hheap. intros [Hm Hsz Hvalid] Hval Hblk Hlen.
  remember (Memdata.encode_int 8 val) as bs.
  remember (8 * Z.to_N blk)%num as idx.
  remember ((ml_data (mem_data mem))) as ml.
  assert (size bs = 8)%nat as Hbs.
  {
    subst bs. rewrite <- length_is_size.
    rewrite Memdata.encode_int_length. reflexivity.
  }
  eexists.
  split; [reflexivity|].
  assert ((N.to_nat idx + length bs <= length ml)%nat) as Hidx.
  {
    rewrite Heqidx. rewrite Heqbs. rewrite Memdata.encode_int_length.
    unfold mem_length in Hlen. rewrite nat_N_Z in Hlen.
    rewrite <- Heqml in Hlen. lia.
  }
  pose proof (write_bytes_core_preserves_length ml idx bs Hidx) as Hplen.
  split.
  - remember ({|
      mem_data :=
       {|
         ml_init := ml_init (mem_data mem);
         ml_data := write_bytes_core ml idx bs
       |};
      mem_max_opt := mem_max_opt mem
    |}) as mem'.
    assert (mem_length (mem_data mem) = mem_length (mem_data mem')) as Hplen'.
    {
      unfold mem_length. f_equal. rewrite Heqmem'. simpl.
      rewrite <- Heqml.
      lia.
    }
    intros block i64 Hblocklen Hz.
    remember (Z.to_N blk) as written_blk.
    assert (block = written_blk \/ (block < written_blk \/ block > written_blk))%N as Hblock by lia.
    destruct Hblock as [Hblock | Hblock].
    + (* written region *)
      exists bs.
      assert (val = i64).
      {
        generalize Hz. rewrite Hblock. rewrite Heqwritten_blk.
        rewrite Z2N.id; [|lia].
        rewrite gss.
        inversion 1.
        reflexivity.
      }
      subst i64.
      pose proof (read_written_bytes_core_same' mem (8 * block) bs 
        (write_bytes_core ml idx bs)) as Hread.
      rewrite <- Heqmem' in Hread.
      rewrite Hbs in Hread.
      split.
      - apply Hread.
        + lia.
        + rewrite Heqidx. rewrite Hblock.
          rewrite Heqml. reflexivity.
      - rewrite Heqbs.
        rewrite encode_decode_int64; lia.
    + (* other region *)
      remember (read_bytes_core ml (8 * block) 8) as bo.
      remember (write_bytes_core ml idx bs) as ml'.
      pose proof (read_written_bytes_core_others' mem idx bs ml') as Hread.
      rewrite <- Heqmem' in Hread.
      assert (read_bytes mem' (8 * block) 8 = read_bytes mem (8 * block) 8) as Hread'.
      {
        apply Hread.
        - rewrite Hbs. subst idx.
          subst written_blk.
          lia.
        - rewrite Heqml'.
          rewrite Heqml.
          reflexivity.
        - rewrite Hbs.
          subst idx.
          assert (block + 1 <= written_blk \/ written_blk + 1 <= block)%nat 
            as Hblock' by lia.
          assert (8 * block + 8 <= 8 * written_blk \/
                  8 * written_blk + 8 <= 8 * block)%nat as Hblock'' by lia.
          destruct Hblock'' as [Hblock'' | Hblock''].
          + left.
            lia.
          + right.
            split.
            * lia.
            * rewrite Hplen'.
              unfold operations.mem_length in Hblocklen.
              lia.
      }
      generalize (Hm block i64). intros Hm'.
      rewrite Hread'.
      apply Hm'.
      * unfold operations.mem_length.
        unfold operations.mem_length in Hblocklen.
        rewrite <- Hplen' in Hblocklen.
        lia.
      * rewrite gso in Hz; [|lia].
        assumption.
  - unfold mem_size, operations.mem_length, mem_length. simpl.
    rewrite Hplen.
    unfold mem_size, operations.mem_length, mem_length in Hsz.
    rewrite <- Heqml in Hsz.
    assumption.
  - unfold ml_valid, operations.mem_length, mem_length. simpl.
    rewrite Hplen.
    unfold ml_valid, operations.mem_length, mem_length in Hvalid.
    rewrite <- Heqml in Hvalid.
    assumption.
  - intros block z Hget.
    destruct (Z.eq_dec blk block) as [Heq | Hneq].
    + subst.
      change  (length (Memdata.encode_int 8 val)) with (8%nat) in Hidx.
      replace (length (ml_data (mem_data mem))) with (N.to_nat (page_size * (mem_size mem))) in Hidx.
      2: {
        Opaque page_size.
        unfold mem_size, operations.mem_length.
        unfold ml_data. unfold mem_length.
        destruct (mem_data mem).
        simpl.
        unfold ml_valid in Hvalid.
        unfold mem_length in Hvalid. simpl in Hvalid.
        rewrite <- (proj2 (N.Div0.div_exact (N.of_nat (length ml_data)) (page_size%N))) by auto.
        lia.
      }
      lia.
    + rewrite gso in Hget; auto.
      eapply heap_bounded; eauto.
      simpl; auto.
    + auto.
Qed.

Lemma heap_rel_write : forall m p mp mem blk val,
  heap_rel m p mp mem ->
  0 <= blk ->
  0 <= val < 2^64 ->
  8 * blk + 8 <= Z.of_N (mem_length mem.(mem_data)) ->
  exists mem',
    write_bytes mem (8 * Z.to_N blk) (Memdata.encode_int 8 val) = Some mem' /\ 
    heap_rel (set m blk val) p mp mem'.
Proof.
  intros until val. intros Hheap.
  generalize Hheap. intros [Hm Hsz Hvalid] Hblk Hval Hlen.
  remember (Memdata.encode_int 8 val) as bs.
  remember (8 * Z.to_N blk)%num as idx.
  assert (N.to_nat idx + length bs <= N.to_nat (mem_length mem.(mem_data)))%nat as Hidx.
  {
    rewrite Heqidx. rewrite Heqbs. rewrite Memdata.encode_int_length.
    lia.
  }
  pose proof (write_bytes_def mem idx bs) as 
    (mem' & Hwrite & Hinit & Hopt & Hdata).
  {
    unfold memory_list.mem_length.
    rewrite ssrnat_nat_N_id.
    unfold mem_length, memory_list.mem_length in Hidx.
    rewrite Nat2N.id in Hidx.
    apply Hidx.
  }
  exists mem'.
  split; [assumption|].
  assert (mem_length (mem_data mem) = mem_length (mem_data mem')) as Hplen.
  {
    eapply (write_bytes_preserve_mem_length mem idx bs mem').
    - rewrite Heqidx. rewrite Heqbs. rewrite Memdata.encode_int_length.
      lia.
    - assumption.
  }
  pose proof (heap_rel_write_core m p mp mem blk val Hheap Hblk Hval Hlen) as 
    (ml' & Hcore & Hheap').
  rewrite <- Heqidx in Hcore.
  rewrite <- Heqbs in Hcore.
  rewrite Hcore in Hdata.
  assert (mem' = {|
           mem_data := {| ml_init := ml_init (mem_data mem); ml_data := ml' |};
           mem_max_opt := mem_max_opt mem
         |}) as Hmem'.
  {
    rewrite <- Hdata. destruct mem', mem_data. simpl in *.
    f_equal; [|assumption].
    f_equal. assumption.
  }
  rewrite <- Hmem' in Hheap'.
  assumption.
Qed.

Lemma decode_encoded_int_app: forall val (n: nat) bs bs1 bs2,
  0 <= val < 2 ^ (Z.of_nat n * 8) ->
  Memdata.encode_int n val = bs ->
  bs = bs1 ++ bs2 ->
  decode_int bs1 + decode_int bs2 * 2 ^ (8 * Z.of_nat (size bs1)) = val.
Proof.
  intros until bs2. intros Hval Hbs Hbs_app.
  remember (size bs1) as x.
  pose proof (cat_take_drop x bs) as Hdcp.
  assert (bs1 = take x bs) as Hbs1.
  {
    rewrite Hbs_app.
    rewrite Heqx.
    rewrite app_take_size.
    reflexivity.
  }
  assert (bs2 = drop x bs) as Hbs2.
  {
    rewrite Hbs_app.
    rewrite Heqx.
    rewrite app_drop_size.
    reflexivity.
  }
  rewrite Heqx.
  rewrite <- decode_int_app.
  rewrite <- Hbs_app.
  rewrite <- Hbs.
  rewrite Memdata.decode_encode_int.
  rewrite Z.mod_small; [reflexivity|].
  rewrite two_p_equiv.
  lia.
Qed.

Lemma decode_encoded_int_app': forall val (n x: nat) bs,
  0 <= val < 2 ^ (Z.of_nat n * 8) ->
  (x <= n)%nat ->
  Memdata.encode_int n val = bs ->
  decode_int (take x bs) + decode_int (drop x bs) * 2 ^ (8 * Z.of_nat x) = val.
Proof.
  intros until bs. intros Hval Hx Hbs.
  remember (take x bs) as bs1.
  remember (drop x bs) as bs2.
  assert (size bs = n) as Hn.
  {
    rewrite <- Hbs.
    rewrite <- length_is_size.
    apply Memdata.encode_int_length.
  }
  assert (x = size bs1)%nat as Hx'.
  {
    subst bs1. rewrite size_take.
    rewrite Hn.
    assert (x < n \/ x = n)%nat as Hxn by lia.
    destruct Hxn as [Hxn | Hxn].
    - rewrite Hxn.
      reflexivity.
    - replace (x < n)%N with false by lia.
      assumption.
  }
  rewrite Hx'.
  erewrite decode_encoded_int_app; eauto.
  rewrite Heqbs1 Heqbs2.
  rewrite cat_take_drop.
  reflexivity.
Qed.

Lemma decode_encoded_int_app'': forall val (n x: nat),
  0 <= val < 2 ^ (Z.of_nat n * 8) ->
  (x <= n)%nat ->
  decode_int (take x (Memdata.encode_int n val)) + decode_int (drop x (Memdata.encode_int n val)) * 2 ^ (8 * Z.of_nat x) = val.
Proof.
  intros until x. intros Hval Hx.
  eapply decode_encoded_int_app'; eauto.
Qed.

From Coq Require Import Znumtheory ZBits.

Lemma decode_encoded_int_head:
  forall n val b bs,
  (0 < n)%nat ->
  0 <= val ->
  encode_int n val = b :: bs ->
  decode_int [:: b] = bitmask 0 8 val.
Proof.
  intros until bs. intros Hn Hval Hbs.
  pose proof (encode_head' n val b bs Hn Hbs) as Hhead.
  rewrite Hhead.
  unfold decode_int.
  rewrite little_endian_eq.
  simpl.
  rewrite Byte.unsigned_repr_eq.
  rewrite bitmask0; [|lia|lia].
  unfold Byte.modulus, Byte.wordsize, Wordsize_8.wordsize.
  rewrite two_power_nat_equiv.
  lia.
Qed.

Lemma decode_encoded_int_head':
  forall n val,
  (0 < n)%nat ->
  0 <= val ->
  decode_int (take 1 (encode_int n val)) = bitmask 0 8 val.
Proof.
  intros until val. intros Hn Hval.
  remember (encode_int n val) as bs.
  pose proof (encode_int_length n val) as Hlen.
  destruct bs as [|b bs'].
  - rewrite <- Heqbs in Hlen.
    simpl in Hlen.
    rewrite <- Hlen in Hn.
    discriminate Hn.
  - rewrite take_1.
    symmetry in Heqbs.
    eapply decode_encoded_int_head; eauto.
Qed.

Lemma unsigned_encoded_int_head:
  forall n val b bs,
  (0 < n)%nat ->
  0 <= val ->
  encode_int n val = b :: bs ->
  Byte.unsigned b = bitmask 0 8 val.
Proof.
  intros until bs. intros Hn Hval Hbs.
  pose proof (encode_head' n val b bs Hn Hbs) as Hhead.
  rewrite Hhead.
  rewrite Byte.unsigned_repr_eq.
  rewrite bitmask0; [|lia|lia].
  unfold Byte.modulus, Byte.wordsize, Wordsize_8.wordsize.
  rewrite two_power_nat_equiv.
  lia.
Qed.

Lemma decode_encoded_int_tail:
  forall n val b bs,
  (0 < n)%nat ->
  0 <= val < 2 ^ (8 * Z.of_nat n) ->
  encode_int n val = b :: bs ->
  decode_int bs = Z.shiftr val 8.
Proof.
  intros until bs. intros Hn Hval Hbs.
  assert (n = 1 \/ n > 1)%nat as Hn' by lia.
  destruct Hn' as [Hn' | Hn'].
  - assert (bs = [::]) as Hnil.
    {
      rewrite Hn' in Hbs.
      pose proof (Memdata.encode_int_length 1 val) as Hlen.
      rewrite length_is_size in Hlen.
      rewrite Hbs in Hlen.
      rewrite size_cons in Hlen.
      assert (size bs = 0)%nat as Hbs' by lia.
      apply size0nil; eauto.
    }
    rewrite Hnil.
    rewrite decode_int_nil.
    rewrite Hn' in Hval.
    replace (8 * Z.of_nat 1) with 8 in Hval by lia.
    rewrite Z.shiftr_div_pow2; [|lia].
    rewrite Z.div_small; [|lia].
    reflexivity.
  - pose proof (encode_int_cons_behead n val b bs Hval Hbs) as Hcons.
    rewrite <- Hcons.
    rewrite Memdata.decode_encode_int.
    rewrite Z.mod_small; [reflexivity|].
    rewrite two_p_equiv.
    replace ((Z.of_nat (n - 1) * 8)) with (8 * Z.of_nat n - 8) by lia.
    apply shiftr_range.
    + lia.
    + lia.
Qed.

Lemma decode_encoded_int_drop_1:
  forall n val bs,
  (0 < n)%nat ->
  0 <= val < 2 ^ (8 * Z.of_nat n) ->
  encode_int n val = bs ->
  decode_int (drop 1 bs) = Z.shiftr val 8.
Proof.
  intros until bs. intros Hn Hval Hbs.
  destruct bs as [|b bs'].
  - pose proof (Memdata.encode_int_length n val) as Hlen.
    rewrite Hbs in Hlen.
    rewrite length_is_size in Hlen.
    rewrite size_nil_eq in Hlen.
    rewrite <- Hlen in Hn.
    discriminate Hn.
  - rewrite drop1.
    rewrite behead_is_tail.
    eapply decode_encoded_int_tail; eauto.
Qed.

Lemma decode_encoded_int_drop_1':
  forall n val,
  (0 < n)%nat ->
  0 <= val < 2 ^ (8 * Z.of_nat n) ->
  decode_int (drop 1 (encode_int n val)) = Z.shiftr val 8.
Proof.
  intros until val. intros Hn Hval.
  remember (encode_int n val) as bs.
  eapply decode_encoded_int_drop_1; eauto.
Qed.

Lemma decode_encoded_int_low:
  forall (x n: nat) (val: Z) (bs: bytes),
    (0 <= x < n)%nat ->
    0 <= val < 2 ^ (8 * Z.of_nat n) ->
    Memdata.encode_int n val = bs ->
    decode_int (take x bs) = bitmask 0 (8 * Z.of_nat x) val.
Proof.
  induction x.
  - intros until bs. intros Hx [Hvall Hvalr] Hbs.
    rewrite take0.
    rewrite bitmask_size0.
    reflexivity.
  - intros until bs.  intros Hx Hval Hbs.
    generalize Hval. intros [Hvall Hvalr].
    replace (x.+1) with (1 + x)%nat by lia.
    rewrite takeD.
    assert (size bs = n) as Hn.
    {
      rewrite <- Hbs.
      apply Memdata.encode_int_length.
    }
    assert (0 < n)%nat as Hn' by lia.
    destruct bs as [|b bs'].
    + rewrite <- Hn in Hn'.
      discriminate Hn'.
    + rewrite take_1.
      rewrite drop1.
      rewrite behead_is_tail.
      rewrite decode_int_cons_lor.
      replace (8 * Z.of_nat (1 + x)) with (8 + 8 * Z.of_nat x) by lia.
      rewrite int_lor_decomp_bitmask; [|lia|lia|lia].
      erewrite unsigned_encoded_int_head with (n:=n)(val:=val)(b:=b)(bs:=bs'); eauto.
      pose proof (encode_int_cons_behead n val b bs' Hval Hbs) as Hcons.
      f_equal.
      remember (Z.shiftr val 8) as val'.
      erewrite IHx with (n:=(n - 1)%nat)(val:=val')(bs:=bs'); eauto.
      + rewrite Heqval'.
        rewrite <- bitmask_shiftr_shiftl; lia.
      + lia.
      + subst val'.
        replace ((8 * Z.of_nat (n - 1))) with (8 * Z.of_nat n - 8)%Z by lia.
        apply shiftr_range; lia.
Qed.

Lemma decode_encoded_int_high:
  forall (x n: nat) (val: Z) (bs: bytes),
    (0 <= x <= n)%nat ->
    0 <= val < 2 ^ (8 * Z.of_nat n) ->
    Memdata.encode_int n val = bs ->
    decode_int (drop x bs) = bitextract (8 * Z.of_nat x) (8 * Z.of_nat (n - x)) val.
Proof.
  induction x.
  - intros until bs. intros Hx [Hvall Hvalr] Hbs.
    rewrite drop0.
    replace ((8 * Z.of_nat 0)) with 0%Z by lia.
    replace (8 * Z.of_nat (n - 0)) with (8 * Z.of_nat n)%Z by lia.
    rewrite bitextract_full'; [|lia|lia].
    rewrite <- Hbs.
    apply encode_decode_int'; lia.
  - intros until bs.  intros Hx Hval Hbs.
    generalize Hval. intros [Hvall Hvalr].
    replace ((8 * Z.of_nat x.+1)) with (8 * Z.of_nat x + 8)%Z by lia.
    rewrite bitextract_shiftr; [|lia|lia|lia|lia].
    replace ((8 * Z.of_nat (n - x.+1) + 8)) with (8 * Z.of_nat (n - x))%Z by lia.
    erewrite <- IHx; eauto.
    replace (x.+1) with (1 + x)%nat by lia.
    rewrite <- drop_drop.
    rewrite decode_int_shiftr_1.
    reflexivity.
    + pose proof (Memdata.encode_int_length n val) as Hlen.
      rewrite length_is_size in Hlen.
      rewrite Hbs in Hlen.
      rewrite size_drop.
      rewrite Hlen.
      lia.
    + lia.
Qed.




Lemma decode_encoded_int_low_same:
  forall (k n: nat) (x y: Z) (bs1 bs2: bytes),
    (0 <= k < n)%nat ->
    0 <= x < 2 ^ (8 * Z.of_nat n) ->
    0 <= y < 2 ^ (8 * Z.of_nat n) ->
    bitmask 0 (8 * Z.of_nat k) x = bitmask 0 (8 * Z.of_nat k) y ->
    Memdata.encode_int n x = bs1 ->
    Memdata.encode_int n y = bs2 ->
    decode_int (take k bs1) = decode_int (take k bs2).
Proof.
  intros until bs2. intros Hkn Hx Hy Hmask Hbs1 Hbs2.
  rewrite (decode_encoded_int_low k n x bs1); eauto.
  rewrite (decode_encoded_int_low k n y bs2); eauto.
Qed.

Lemma decode_encoded_int_high_same:
  forall (k n: nat) (x y: Z) (bs1 bs2: bytes),
    (0 <= k <= n)%nat ->
    0 <= x < 2 ^ (8 * Z.of_nat n) ->
    0 <= y < 2 ^ (8 * Z.of_nat n) ->
    bitextract (8 * Z.of_nat k) (8 * Z.of_nat (n - k)) x = bitextract (8 * Z.of_nat k) (8 * Z.of_nat (n - k)) y ->
    Memdata.encode_int n x = bs1 ->
    Memdata.encode_int n y = bs2 ->
    decode_int (drop k bs1) = decode_int (drop k bs2).
Proof.
  intros until bs2. intros Hkn Hx Hy Hmask Hbs1 Hbs2.
  rewrite (decode_encoded_int_high k n x bs1); eauto.
  rewrite (decode_encoded_int_high k n y bs2); eauto.
Qed.

Lemma read_bytes_core_app:
  forall ml idx m n,
    (idx + m + n <= size ml)%N ->
    read_bytes_core ml idx (m + n) =
    read_bytes_core ml idx m ++ read_bytes_core ml (idx + m) n.
Proof.
  intros until n. intros Hlen.
  unfold read_bytes_core.
  remember (drop idx ml) as bs_o.
  erewrite <- cat_take_drop with (n0:=m)(s:=bs_o).
  rewrite take_cat.
  rewrite size_take.
  assert (size bs_o = size ml - idx)%nat as Hsize.
  {
    rewrite Heqbs_o.
    rewrite size_drop.
    reflexivity.
  }
  assert (m + n <= size bs_o)%N by lia.
  assert (m < size bs_o \/ m = size bs_o)%nat as Hm by lia.
  destruct Hm as [Hm | Hm]; rewrite Hm.
  - replace ((m + n < m)%N) with false by lia.
    replace ((m + n - m)%N) with n by lia.
    rewrite take_cat.
    rewrite size_take.
    rewrite Hm.
    replace (m < m)%N with false by lia.
    replace (m - m)%N with 0%N by lia.
    rewrite take0.
    rewrite cats0.
    subst bs_o.
    rewrite drop_drop.
    replace ((m + idx)%N) with (idx + m)%N by lia.
    reflexivity.
  - replace (size bs_o < size bs_o)%N with false by lia.
    replace ((size bs_o + n < size bs_o)%N) with false by lia.
    rewrite !take_size.
    replace ((size bs_o + n - size bs_o)%N) with n by lia.
    rewrite drop_size.
    rewrite take_nil_l.
    rewrite !cats0.
    rewrite take_size.
    subst bs_o.
    replace (idx + size (drop idx ml))%N with (size ml) by lia.
    rewrite drop_size.
    rewrite take_nil_l.
    rewrite cats0.
    reflexivity.
Qed.

Lemma read_bytes_core_prefix:
  forall ml idx m n,
    (idx + m + n <= size ml)%N ->
    read_bytes_core ml idx m = take m (read_bytes_core ml idx (m + n)).
Proof.
  intros until n. intros Hlen.
  unfold read_bytes_core.
  rewrite take_takel; [|lia].
  reflexivity.
Qed.

Lemma read_bytes_core_suffix:
  forall ml idx m n,
    (idx + m + n <= size ml)%N ->
    read_bytes_core ml (idx + m) n = drop m (read_bytes_core ml idx (m + n)).
Proof.
  intros until n. intros Hlen.
  unfold read_bytes_core.
  rewrite !take_drop.
  rewrite drop_drop.
  f_equal; [lia|].
  f_equal; lia.
Qed.

Lemma read_written_bytes_core_partial:
  forall (ml ml': bytes) (idx k t: N) (bs bs_w: bytes),
    (idx + k + size bs + t <= size ml)%nat -> 
    read_bytes_core  ml  idx (k + size bs + t) = bs_w ->
    write_bytes_core ml (idx + k) bs = ml' ->
    read_bytes_core  ml' idx (k + size bs + t) = take k bs_w ++ bs ++ drop (k + size bs) bs_w.
Proof.
  intros until bs_w. intros Hidx Hread Hwrite.
  pose proof (read_written_bytes_core_full (idx + k) ml bs ml') as Hfull.
  destruct Hfull as [Hs Ho].
  - lia.
  - assumption.
  assert (size ml = size ml') as Hml'.
  {
    rewrite <- Hwrite. symmetry.
    apply write_bytes_core_preserves_size.
    lia.
  }
  rewrite read_bytes_core_app; [|lia].
  rewrite read_bytes_core_app; [|lia].
  rewrite Ho.
  rewrite nat_of_add_bin in Hs Ho.
  rewrite Hs.
  replace (idx + (k + size bs))%N with (idx + k + size bs)%N by lia.
  pose proof (Ho (idx + k + N.of_nat (size bs))%num t) as Hhigh.
  rewrite !nat_of_add_bin in Hhigh.
  rewrite !ssrnat_nat_N_id in Hhigh.
  rewrite Hhigh.
  assert ((k + size bs + t = k + (size bs + t))%nat) as Hhigh' by lia.
  rewrite Hhigh' in Hread.
  erewrite read_bytes_core_prefix with (ml:=ml)(idx:=idx)(m:=k)(n:=(size bs + t)%nat);
    [|lia].
  replace (idx + k + size bs)%nat with (idx + (k + size bs))%nat by lia.
  erewrite read_bytes_core_suffix with (ml:=ml)(idx:=idx)(m:=(k + size bs)%nat)
    (n:=t); [|lia].
  rewrite Hread.
  replace ((k + size bs + t)%nat) with (k + (size bs + t))%nat by lia.
  rewrite Hread.
  rewrite <- catA.
  reflexivity.
  - right.
    lia.
  - left.
    lia.
Qed.

Lemma read_written_bytes_core_partial':
  forall (mem mem': memory) (idx k t: N) (ml' bs bs_w: bytes),
    (idx + k + size bs + t <= mem_length mem.(mem_data))%nat -> 
    read_bytes_core  mem.(mem_data).(ml_data) idx (k + size bs + t) = bs_w ->
    write_bytes_core mem.(mem_data).(ml_data) (idx + k) bs = ml' ->
    mem' = {|
      mem_data := {|
        ml_init := mem.(mem_data).(ml_init);
        ml_data := ml';
      |};
      mem_max_opt := mem.(mem_max_opt);
    |} ->
    read_bytes mem' idx (k + size bs + t) = Some (take k bs_w ++ bs ++ drop (k + size bs) bs_w).
Proof.
  intros until bs_w. intros Hidx Hread Hwrite Hmem'.
  remember (ml_data (mem_data mem)) as ml.
  assert (mem_length (mem_data mem) = N.of_nat (size ml)) as Hlen.
  {
    unfold mem_length. rewrite length_is_size.
    rewrite Heqml. reflexivity.
  }
  rewrite Hlen in Hidx.
  rewrite ssrnat_nat_N_id in Hidx.
  remember (take k bs_w ++ bs ++ drop (k + size bs) bs_w) as bs'.
  assert (size bs_w = k + size bs + t)%nat as Hbs'.
  {
    rewrite <- length_is_size.
    eapply (read_bytes_core_length ml idx (k + size bs + t) bs_w); 
      [lia|assumption].
  }
  assert (0 <= size bs)%nat as Hlenbs by lia.
  assert (0 <= t)%nat as Ht by lia.
  assert (0 <= k)%nat as Hk by lia.
  assert (k <= size bs_w)%nat as Hkbs by lia.
  assert (size bs' = k + size bs + t)%nat as Hbs''.
  {
    rewrite Heqbs'.
    rewrite !size_cat.
    rewrite !size_take.
    rewrite !size_drop.
    assert (k < N.of_nat (size bs_w) \/ k = N.of_nat (size bs_w))%N as Hk' by lia.
    rewrite ssrnat_nat_N_id in Hk'.
    destruct Hk' as [Hk' | Hk'].
    - rewrite Hk'.
      lia.
    - replace (k < size bs_w)%nat with false by lia.
      lia.
  }
  rewrite <- Hbs''.
  assert (size ml = size ml') as Hsizeml.
  {
    rewrite <- Hwrite. symmetry.
    apply write_bytes_core_preserves_size.
    lia.  
  }
  assert (mem_length (mem_data mem) = mem_length (mem_data mem')) as Hmemlen.
  {
    unfold mem_length.
    rewrite !length_is_size.
    rewrite <- Heqml. rewrite Hmem'.
    simpl.
    rewrite Hsizeml.
    reflexivity.
  }
  assert (mem_length (mem_data mem) = N.of_nat (size ml))%nat.
  {
    unfold mem_length. rewrite length_is_size.
    rewrite Heqml. reflexivity.
  }
  eapply read_bytes_spec; [lia|].
  assert ((ml_data (mem_data mem')) = ml') as Hml'.
  {
    rewrite Hmem'. simpl. reflexivity.
  }
  rewrite Hml'.
  rewrite Hbs''. rewrite Heqbs'.
  eapply read_written_bytes_core_partial; eauto.
Qed.

Lemma decode_encoded_int_partial:
  forall (i j n x y: Z) (bs bs': bytes),
    0 <= i < j ->
    j <= n ->
    0 <= x < 2 ^ (8 * n) ->
    0 <= y < 2 ^ (8 * n) ->
    bitmask 0 (8 * i) x = bitmask 0 (8 * i) y ->
    bitextract (8 * j) (8 * (n - j)) x = bitextract (8 * j) (8 * (n - j)) y ->
    encode_int (Z.to_nat n) x = bs ->
    encode_int (Z.to_nat (j - i)) (Z.shiftr y (8 * i)) = bs' ->
    decode_int (take (Z.to_nat i) bs ++ bs' ++ drop (Z.to_nat j) bs) = y.
Proof.
  intros until bs'. intros Hi Hj Hx Hy Hmask Hextract Hbs Hbs'.
  assert (size bs = Z.to_nat n) as Hszbs.
  {
    rewrite <- Hbs.
    apply Memdata.encode_int_length.
  }
  assert (size bs' = Z.to_nat (j - i)) as Hszbs'.
  {
    rewrite <- Hbs'.
    apply Memdata.encode_int_length.
  }
  assert (i < n) as Hiltn by lia.
  (* decompose bs *)
  rewrite decode_int_app_lor_3.
  rewrite size_take.
  assert ((Z.to_nat i < size bs)%N) as Hiltbs by lia.
  rewrite Hiltbs.
  rewrite Z2Nat.id; [|lia].
  (* decompose int *)
  rewrite (int_lor_decomp_bitmask_3 y (8 * i) (8 * j) (8 * n)); [|lia|lia|lia].
  f_equal; [|f_equal].
  - (* low *)
    remember (Z.to_nat i) as i'.
    rewrite <- Hmask.
    replace (8 * i) with (8 * Z.of_nat i') by lia.
    eapply (decode_encoded_int_low i' (Z.to_nat n) x bs); 
      [lia| |eassumption].
    rewrite Z2Nat.id; lia.
  - (* middle *)
    rewrite <- Hbs'.
    rewrite Memdata.decode_encode_int.
    rewrite Z2Nat.id; [|lia].
    rewrite bitmask_shiftr_shiftl; [|lia|lia|lia].
    rewrite bitmask0_is_mod; [|lia|].
    do 2 f_equal.
    rewrite two_p_equiv.
    replace ((j - i) * 8) with (8 * j - 8 * i) by lia.
    reflexivity.
    + rewrite Z.shiftr_div_pow2; [|lia].
      apply Z.div_pos; lia.
  - (* high *)
    rewrite bitmask_bitextract_shiftl; [|lia|lia|lia].
    f_equal.
    + replace ((8 * n - 8 * j)) with (8 * (n - j)) by lia.
      rewrite <- Hextract.
      remember (Z.to_nat j) as j'.
      replace (8 * j) with (8 * Z.of_nat j') by lia.
      replace ((8 * (n - j))) with (8 * Z.of_nat (Z.to_nat n - j')) by lia.
      eapply (decode_encoded_int_high j' (Z.to_nat n) x bs);
        [lia| |eassumption].
      * rewrite Z2Nat.id; lia.
    + rewrite Hszbs'.
      lia.
Qed.

Lemma heap_rel_write_partial_core: 
  forall (m: map) (mp p: Z) (mem: memory) (blk val_o val_w x y: Z),
  0 <= x < y ->
  y <= 8 ->
  0 <= val_o < 2^64 ->
  0 <= val_w < 2^64 ->
  heap_rel m mp p mem ->
  0 <= blk ->
  8 * blk + 8 <= Z.of_N (mem_length mem.(mem_data)) ->
  read_bytes_core mem.(mem_data).(ml_data) (8 * Z.to_nat blk) 8 = encode_int 8 val_o ->
  bitmask 0 (8 * x) val_o = bitmask 0 (8 * x) val_w ->
  bitextract (8 * y) (8 * (8 - y)) val_o = bitextract (8 * y) (8 * (8 - y)) val_w ->
  exists ml',
    write_bytes_core mem.(mem_data).(ml_data) (Z.to_N (8 * blk + x))
    (encode_int (Z.to_nat (y - x)) (Z.shiftr val_w (8 * x))) = ml' /\
    heap_rel (set m blk val_w) mp p ({|
      mem_data := {|
        ml_init := mem.(mem_data).(ml_init);
        ml_data := ml';
      |};
      mem_max_opt := mem.(mem_max_opt);
    |}).
Proof.
  intros until y. intros Hxy Hy Hvalo Hvalw Hrel Hblk Hlen Hread Hmask Hextract.
  assert (0 <= 8 - y)%Z as Hy' by lia.
  assert (0 < 8 - x)%Z as Hx' by lia.
  remember (encode_int 8 val_o) as bs_o.
  remember (8 * blk) as idx0.
  remember (idx0 + x) as idx.
  assert (0 <= idx) as Hidxge0 by lia.
  assert (size bs_o = 8)%nat as Hlenbs.
  {
    rewrite Heqbs_o.
    apply encode_int_length.
  }
  remember (write_bytes_core (ml_data (mem_data mem)) (Z.to_N idx)
            (encode_int (Z.to_nat (y - x)) (Z.shiftr val_w (8 * x)))) as ml'.
  exists ml'.
  split; [reflexivity|].
  remember ({|
      mem_data := {| ml_init := ml_init (mem_data mem); ml_data := ml' |};
      mem_max_opt := mem_max_opt mem
    |}) as mem'.
  remember (ml_data (mem_data mem)) as ml.
  assert (size ml = mem_length (mem_data mem)) as Hlen'.
  {
    unfold mem_length. rewrite <- Heqml.
    rewrite length_is_size.
    rewrite ssrnat_nat_N_id.
    reflexivity.
  }
  assert (idx0 + 8 <= Z.of_nat (size ml)) as Hidx0 by lia.
  remember (8 * x) as x_bit.
  remember (y - x) as lenB.
  remember (encode_int (Z.to_nat lenB) (Z.shiftr val_w x_bit)) as bs.
  assert (size bs = Z.to_nat lenB) as HlenB.
  {
    rewrite Heqbs.
    apply encode_int_length.
  }
  assert (0 < lenB <= 8)%Z as HlenB' by lia.
  assert (idx + lenB <= Z.of_nat (size ml)) as Hidx by lia.
  assert (Z.to_nat idx + size bs <= size ml)%nat as Hidx' by lia.
  assert (Z.to_nat idx + size bs <= mem_length (mem_data mem))%nat as Hidx'' by lia.
  assert (size ml = size ml') as Hlenml.
  {
    rewrite Heqml'. symmetry.
    eapply write_bytes_core_preserves_size.
    rewrite Z_N_nat.
    rewrite HlenB.
    rewrite <- Z2Nat.inj_add; [|lia|lia].
    lia.
  }
  assert (mem_length (mem_data mem) = mem_length (mem_data mem')) as Hmemlen.
  {
    unfold mem_length. rewrite <- Heqml.
    rewrite Heqmem'. simpl.
    rewrite !length_is_size.
    rewrite Hlenml.
    reflexivity.
  }
  generalize Hrel; intros [Hmap Hmem_size Hml_valid Hbounded Hlimit Hlimit_valid].
  split.
  - (* decode wirtten bytes *)
    intros block v_read.
    remember (8 * block)%num as idx'.
    unfold operations.mem_length.
    rewrite <- Hmemlen.
    intros Hblock Hget.
    pose proof (read_written_bytes_full mem mem' (Z.to_N idx) bs) as Hfull.
    destruct Hfull as [Hread_bs Hread_others].
    + rewrite Z_N_nat.
      rewrite <- Hlen'.
      rewrite HlenB.
      lia.
    + pose proof (write_bytes_spec bs ml' mem (Z.to_N idx)) as Hwrite_spec.
      rewrite Hwrite_spec.
      * rewrite Heqmem'.
        reflexivity.
      * rewrite Z_N_nat. rewrite length_is_size.
        apply Hidx''.
      * rewrite Heqml'.
        rewrite <- Heqml.
        reflexivity.
    assert (idx' = Z.to_N idx0 \/ idx' <> Z.to_N idx0) as Hidx_eq by lia.
    destruct Hidx_eq as [Hidx_eq | Hidx_eq].
    + (* same i64 *)
      exists (take (Z.to_nat x) bs_o ++ bs ++ take (Z.to_nat (8 - y)) (drop (Z.to_nat y) bs_o)).
      rewrite take_drop.
      replace ((Z.to_nat (8 - y) + Z.to_nat y)%nat) with 8%nat by lia.
      erewrite take_oversize with (n:=8%nat); [|lia].
      split.
      * assert (x + Z.of_nat (size bs) + (8 - y) = 8) as Hbs_decomp.
        {
          rewrite HlenB. rewrite Z2Nat.id; [|lia].
          lia.
        }
        assert (Z.to_N x + size bs + Z.to_N (8 - y) = 8)%N as Hbs_decomp'
          by lia.
        rewrite <- Hbs_decomp' at 1.
        erewrite read_written_bytes_core_partial' with (mem:=mem) (mem':=mem')
          (bs_w:=bs_o); try eassumption.
        - rewrite !ssrnat_Z_N_nat.
          assert (x + Z.of_nat (size bs) = y)%Z as Hbs_decomp''.
          {
            rewrite HlenB. rewrite Z2Nat.id; [|lia].
            lia.
          }
          assert (Z.to_nat x + size bs = Z.to_nat y)%nat as Hbs_decomp''' by lia.
          rewrite <- Hbs_decomp'''.
          reflexivity.
        - rewrite Hidx_eq.
          rewrite HlenB.
          rewrite HeqlenB.
          rewrite <- Hlen'.
          lia.
        - rewrite <- Hread.
          rewrite <- Heqml.
          rewrite Hidx_eq.
          rewrite Heqidx0.
          assert (x + Z.of_nat (size bs) + 8 - y = 8) as Hbs_comp by lia.
          assert (Z.to_N x + size bs + Z.to_N (8 - y) = 8)%N as Hbs_comp' by lia.
          rewrite Hbs_comp'.
          f_equal.
          lia.
        - rewrite Heqml'.
          rewrite <- Heqml.
          rewrite Hidx_eq.
          rewrite Heqidx.
          f_equal.
          lia.
      * assert (blk = Z.of_N block) as Hblock' by lia.
        assert (v_read = val_w) as Hw.
        {
          rewrite <- Hblock' in Hget.
          rewrite gss in Hget.
          inversion Hget.
          reflexivity.
        }
        rewrite Hw.
        eapply decode_encoded_int_partial with (x:=val_o)(y:=val_w)
          (n:=8)(bs:=bs_o)(bs':=bs); eauto.
        - rewrite <- Heqx_bit.
          lia.
        - rewrite <- Heqx_bit.
          rewrite <- HeqlenB.
          rewrite Heqbs.
          reflexivity.
    + (* others *)
      rewrite Hread_others.
      assert (8 * block + 8 <= operations.mem_length mem)%num as Hmap_len.
      {
        unfold operations.mem_length. lia.
      }
      assert (get m (Z.of_N block) = Some v_read) as Hmap_get.
      {
        rewrite gso in Hget.
        assumption.
        lia.
      }
      rewrite Heqidx'.
      eapply (Hmap block v_read Hmap_len Hmap_get); eauto.
      * assert (size bs = Z.to_nat y - Z.to_nat x)%nat as Hbs_len by lia.
        subst idx.
        rewrite Hbs_len.
        rewrite <- Hlen'.
        lia.
  - (* mem size preservation *)
    unfold mem_size, operations.mem_length.
    rewrite <- Hmemlen.
    rewrite Hmem_size.
    unfold mem_size, operations.mem_length.
    reflexivity.
  - (* ml_valid preservation *)
    unfold ml_valid.
    rewrite <- Hmemlen.
    unfold ml_valid in Hml_valid.
    exact Hml_valid.
  - (* heap_bounded perservation *)
    eapply write_bytes_preserve_heap_bounded'; try eassumption.
    lia.
  - (* heap_limit *)
    assert (mem_max_opt mem = mem_max_opt mem') as Hmaxopt.
    {
      destruct mem' as [data' maxopt'] eqn: Hmem'; simpl.
      inversion Heqmem'.
      reflexivity.
    }
    rewrite Hmaxopt in Hlimit.
    assumption.
  - (* heap_limit_valid *)
    assumption.
Qed.

Lemma heap_rel_write_partial': 
  forall (m: map) (mp p: Z) (mem: memory) (blk val_o val_w x y: Z),
  0 <= x < y ->
  y <= 8 ->
  0 <= val_o < 2^64 ->
  0 <= val_w < 2^64 ->
  heap_rel m mp p mem ->
  0 <= blk ->
  8 * blk + 8 <= Z.of_N (mem_length mem.(mem_data)) ->
  read_bytes mem (8 * Z.to_N blk) 8 = Some (encode_int 8 val_o) ->
  bitmask 0 (8 * x) val_o = bitmask 0 (8 * x) val_w ->
  bitextract (8 * y) (8 * (8 - y)) val_o = bitextract (8 * y) (8 * (8 - y)) val_w ->
  exists mem',
    write_bytes mem (Z.to_N (8 * blk + x))
    (encode_int (Z.to_nat (y - x)) (Z.shiftr val_w (8 * x))) = Some mem' /\
    heap_rel (set m blk val_w) mp p mem'.
Proof.
  intros until y. intros Hxy Hy Hvalo Hvalw Hrel Hblk Hlen Hread Hmask Hextract.
  pose proof (heap_rel_write_partial_core m mp p mem blk val_o val_w x y) as Hwrite.
  destruct Hwrite as (ml' & Hwrite & Hrel'); eauto.
  - apply read_bytes_def in Hread; [|lia].
    replace (8 * Z.to_nat blk)%nat with (N.to_nat (8 * Z.to_N blk)) by lia.
    apply Hread.
  - remember ({|
            mem_data := {| ml_init := ml_init (mem_data mem); ml_data := ml' |};
            mem_max_opt := mem_max_opt mem
          |}) as mem'.
    exists mem'.
    split; [|assumption].
    + rewrite Heqmem'.
      apply write_bytes_spec; [|assumption].
      rewrite Memdata.encode_int_length.
      rewrite Z_N_nat.
      lia.
Qed.

Lemma heap_rel_write_partial: 
  forall (m: map) (mp p: Z) (mem: memory) (blk val_o val_w x y: Z),
  0 <= x < y ->
  y <= 8 ->
  0 <= val_o < 2^64 ->
  0 <= val_w < 2^64 ->
  heap_rel m mp p mem ->
  0 <= blk ->
  8 * blk + 8 <= Z.of_N (mem_length mem.(mem_data)) ->
  read_bytes mem (8 * Z.to_N blk) 8 = Some (encode_int 8 val_o) ->
  val_o mod 2 ^ (8 * x) = val_w mod 2 ^ (8 * x) ->
  Z.shiftr val_o (8 * y) = Z.shiftr val_w (8 * y) ->
  exists mem',
    write_bytes mem (Z.to_N (8 * blk + x))
    (encode_int (Z.to_nat (y - x)) (Z.shiftr val_w (8 * x))) = Some mem' /\
    heap_rel (set m blk val_w) mp p mem'.
Proof.
  intros until y. intros Hxy Hy Hvalo Hvalw Hrel Hblk Hlen Hread Hmod Hshiftr.
  eapply (heap_rel_write_partial' m mp p mem blk val_o val_w x y); eauto.
  - do 2 (rewrite bitmask0_is_mod; [|lia|lia]).
    eassumption.
  - replace (8 * (8 - y)) with (64 - (8 * y)) by lia.
    assert (0 < y <= 8) as Hy' by lia.
    assert (0 <= 8 * y <= 64) as Hy'' by lia.
    erewrite bitextract_n_is_shiftr with (m:=8 * y)(n:=64); [|lia|lia].
    erewrite bitextract_n_is_shiftr with (m:=8 * y)(n:=64); [|lia|lia].
    eassumption.
Qed.

Lemma heap_rel_write_combined : forall m mp p mem blk z z' x y,
  0 <= x < 8 ->
  0 < y <= 8 ->
  x < y ->
  0 <= z < 2^64 ->
  0 <= z' < 2 ^ 64 ->
  0 <= blk ->
  heap_rel m mp p mem ->
  8 * blk + 8 <= Z.of_N (operations.mem_length mem) ->
  read_bytes mem (8 * Z.to_N blk) 8 = Some (Memdata.encode_int 8 z) ->
  z mod 2^(8 * x) = z' mod 2^(8 * x) ->
  Z.shiftr z (8 * y) = Z.shiftr z' (8 * y) ->
  exists mem',
    write_bytes mem (8 * Z.to_N blk + Z.to_N x)
    (Memdata.encode_int (Z.to_nat (y - x)) (Z.shiftr z' (8 * x))) = Some mem' /\
    heap_rel (set m blk z') mp p mem'.
Proof.
  intros until y. intros Hx Hy Hxy Hz Hrel Hlen Hread Hmod Hshiftr.
  replace (8 * Z.to_N blk + Z.to_N x)%num with (Z.to_N (8 * blk + x))%num.
  eapply (heap_rel_write_partial m mp p mem blk z z' x y); eauto.
  - lia.
  - lia.
  - lia.
Qed.

Lemma write_bytes_core_app:
  forall (idx: N) (ml ml' ml'' bs1 bs2: bytes),
  (N.to_nat idx + size bs1 + size bs2 <= size ml)%nat ->
  write_bytes_core ml idx bs1 = ml' ->
  write_bytes_core ml' (idx + N.of_nat (size bs1)) bs2 = ml'' ->
  write_bytes_core ml idx (bs1 ++ bs2) = ml''.
Proof.
  intros until bs2. intros Hidx Hbs1 Hbs2.
  rewrite <- Hbs2.
  rewrite <- Hbs1.
  unfold write_bytes_core.
  rewrite !length_is_size.
  assert (size (bs1 ++ bs2) = size bs1 + size bs2)%nat as Hszapp.
  {
    rewrite size_cat. reflexivity.
  }
  replace ((N.to_nat (idx + N.of_nat (size (bs1 ++ bs2))))%nat)
    with (N.to_nat idx + size bs1 + size bs2)%nat by lia.
  replace ((N.to_nat (idx + N.of_nat (size bs1) + N.of_nat (size bs2)))%nat)
    with (N.to_nat idx + size bs1 + size bs2)%nat by lia.
  replace ((N.to_nat (idx + N.of_nat (size bs1)))%nat)
    with (N.to_nat idx + size bs1)%nat by lia.
  rewrite drop_cat.
  assert (size (take (N.to_nat idx) ml) = N.to_nat idx) as Hszidx.
  {
    assert (N.to_nat idx < size ml \/ N.to_nat idx = size ml)%nat as Hidx'' by lia.
    destruct Hidx'' as [Hidx'' | Hidx''].
    - rewrite size_take.
      rewrite Hidx''. reflexivity.
    - rewrite take_oversize; [|lia].
      lia.
  }
  rewrite Hszidx.
  assert ((N.to_nat idx + size bs1 + size bs2 < N.to_nat idx)%N = false ) 
    as Hidx_false by lia.
  rewrite Hidx_false.
  replace ((N.to_nat idx + size bs1 + size bs2 - N.to_nat idx)%nat)
    with (size bs1 + size bs2)%nat by lia.
  rewrite drop_cat.
  replace ((size bs1 + size bs2 < size bs1)%N) with false by lia.
  replace ((size bs1 + size bs2 - size bs1)%nat) with (size bs2)%nat by lia.
  rewrite drop_drop.
  replace (size bs2 + (N.to_nat idx + size bs1))%nat
    with (N.to_nat idx + size bs1 + size bs2)%nat by lia.
  remember (drop (N.to_nat idx + size bs1 + size bs2) ml) as bs_high.
  rewrite take_cat.
  rewrite Hszidx.
  replace ((N.to_nat idx + size bs1 < N.to_nat idx)%N) with false by lia.
  replace (N.to_nat idx + size bs1 - N.to_nat idx)%nat
    with (size bs1)%nat by lia.
  rewrite take_cat.
  replace (size bs1 < size bs1)%N with false by lia.
  replace ((size bs1 - size bs1)%nat) with 0%nat by lia.
  rewrite take0.
  rewrite cats0.
  rewrite !catA.
  reflexivity.
Qed.

Lemma write_bytes_app:
  forall (idx: N) (mem mem' mem'': memory) (bs1 bs2: bytes),
  (N.to_nat idx + size bs1 + size bs2 <= mem_length mem.(mem_data))%nat ->
  write_bytes mem idx bs1 = Some mem' ->
  write_bytes mem' (idx + N.of_nat (size bs1)) bs2 = Some mem'' ->
  write_bytes mem idx (bs1 ++ bs2) = Some mem''.
Proof.
  intros until bs2. intros Hlen Hwrite1 Hwrite2.
  assert (0 <= size bs1)%nat as Hbs1 by lia.
  assert (0 <= size bs2)%nat as Hbs2 by lia.
  assert (mem_length (mem_data mem) = mem_length (mem_data mem')) as Hmemlen.
  {
    eapply (write_bytes_preserve_mem_length mem idx bs1 mem').
    - rewrite length_is_size.
      lia.
    - assumption.
  }
  assert (mem_length (mem_data mem') = mem_length (mem_data mem'')) as Hmemlen'.
  {
    eapply (write_bytes_preserve_mem_length mem' (idx + N.of_nat (size bs1)) bs2 mem'').
    - rewrite length_is_size.
      lia.
    - assumption.
  }
  remember (ml_data (mem_data mem)) as ml.
  assert (N.to_nat idx + size bs1 + size bs2 <= size ml)%nat as Hlen'.
  {
    unfold mem_length in Hlen.
    rewrite length_is_size in Hlen.
    rewrite <- Heqml in Hlen.
    lia.
  }
  (* bs1 *)
  pose proof (write_bytes_def mem idx bs1) as Hwrite1'.
  destruct Hwrite1' as (mem'e & Hwrite1' & Hml_init1 & Hopt1 & Hdata1).
  {
    rewrite length_is_size.
    lia.
  }
  rewrite Hwrite1 in Hwrite1'.
  inversion Hwrite1'.
  subst mem'e. clear Hwrite1'.
  symmetry in Hdata1.
  remember (ml_data (mem_data mem')) as ml'.
  (* bs2 *)
  pose proof (write_bytes_def mem' (idx + N.of_nat (size bs1)) bs2) as Hwrite2'.
  destruct Hwrite2' as (mem''e & Hwrite2' & Hml_init2 & Hopt2 & Hdata2).
  {
    rewrite length_is_size.
    lia.
  }
  rewrite Hwrite2 in Hwrite2'.
  inversion Hwrite2'.
  subst mem''e. clear Hwrite2'.
  remember (ml_data (mem_data mem'')) as ml''.
  (* bs1 ++ bs2 *)
  assert (mem'' = {|
    mem_data := {|
      ml_init := ml_init (mem_data mem);
      ml_data := ml_data (mem_data mem'') |};
    mem_max_opt := mem_max_opt mem
  |}) as Hmem'.
  {
    destruct mem'' as [mem_data'' mem_max''] eqn: Hmem''_des; simpl in *.
    destruct mem_data'' as [ml_init'' ml_data''] eqn: Hmem_data''_des; simpl in *.
    rewrite Hml_init2 Hopt2.
    rewrite Hml_init1 Hopt1.
    reflexivity.
  }
  rewrite Hmem'.
  eapply write_bytes_spec.
  - rewrite length_is_size.
    rewrite size_cat.
    lia.
  - rewrite <- Heqml''.
    rewrite <- Heqml.
    eapply (write_bytes_core_app idx ml ml' ml'' bs1 bs2).
    + lia.
    + rewrite <- Heqml in Hdata1.
      assumption.
    + rewrite <- Heqml' in Hdata2.
      symmetry in Hdata2.
      assumption.
Qed.


Lemma write_encoded_bytes_app:
  forall (idx: N) (mem mem' mem'': memory) {n1 n2: nat} val1 val2,
  0 <= val1 < 2 ^ (8 * Z.of_nat n1) ->
  (N.to_nat idx + n1 + n2 <= mem_length mem.(mem_data))%nat ->
  write_bytes mem idx (encode_int n1 val1) = Some mem' ->
  write_bytes mem' (idx + N.of_nat n1) (encode_int n2 val2) = Some mem'' ->
  write_bytes mem idx 
    (encode_int (n1 + n2)
                (val1 + val2 * 2^(8 * Z.of_nat n1))) = Some mem''.
Proof.
  intros until val2. intros Hlen Hidx Hwrite1 Hwrite2.
  remember (encode_int n1 val1) as bs1. symmetry in Heqbs1.
  remember (encode_int n2 val2) as bs2. symmetry in Heqbs2.
  remember (encode_int (n1 + n2) (val1 + val2 * 2^(8 * Z.of_nat n1))) as bs.
  symmetry in Heqbs.
  erewrite encode_int_app with (n1:=n1)(n2:=n2)(val1:=val1)(val2:=val2) in Heqbs;
    [|lia].
  rewrite Heqbs1 Heqbs2 in Heqbs.
  rewrite <- Heqbs.
  assert (size bs1 = n1)%nat as Hlenbs1.
  {
    rewrite <- Heqbs1.
    apply encode_int_length.
  }
  assert (size bs2 = n2)%nat as Hlenbs2.
  {
    rewrite <- Heqbs2.
    apply encode_int_length.
  }
  eapply write_bytes_app with (idx:=idx)(mem:=mem)(mem':=mem')(mem'':=mem'')
    (bs1:=bs1)(bs2:=bs2); try eassumption.
  - rewrite Hlenbs1 Hlenbs2.
    assumption.
  - rewrite Hlenbs1.
    eassumption.
Qed. 

Lemma write_bytes_combine : forall (mem mem' mem'': memory) (addr: N) {len1 len2 : nat} val1 val2,
  0 <= val1 < 2 ^ (8 * Z.of_nat len1) ->
  (addr + N.of_nat (len1 + len2) <= operations.mem_length mem)%N ->
  write_bytes mem addr
    (Memdata.encode_int len1 val1) = Some mem' ->
  write_bytes mem' (addr + N.of_nat len1) 
    (Memdata.encode_int len2 val2) = Some mem'' ->
  write_bytes mem addr
    (Memdata.encode_int (len1 + len2) 
    (val2 * 2^(Z.of_nat len1 * 8) + val1 mod 2^(Z.of_nat len1 * 8))) = Some mem''.
Proof.
  intros until val2. intros Hval1 Hlen Hwrite1 Hwrite2.
  assert (val1 mod 2 ^ (Z.of_nat len1 * 8) = val1) as Hval1'.
  {
    rewrite Z.mod_small.
    reflexivity.
    rewrite Z.mul_comm.
    assumption.
  }
  rewrite Hval1'.
  erewrite Z.add_comm at 1.
  replace (Z.of_nat len1 * 8) with (8 * Z.of_nat len1) by lia.
  eapply write_encoded_bytes_app; try eassumption.
  unfold operations.mem_length in Hlen.
  lia.
Qed.

Lemma write_bytes_combine' : forall (mem mem' mem'': memory) (addr: N) {len1 len2 : nat} val1 val2,
  0 <= val1 < 2 ^ (8 * Z.of_nat len1) ->
  (addr + N.of_nat (len1 + len2) <= operations.mem_length mem)%num ->
  write_bytes mem addr
    (Memdata.encode_int len1 val1) = Some mem' ->
  write_bytes mem' (addr + N.of_nat len1) 
    (Memdata.encode_int len2 val2) = Some mem'' ->
  write_bytes mem addr
    (Memdata.encode_int (len1 + len2) 
    (val2 * 2^(Z.of_nat len1 * 8) + val1 mod 2^(Z.of_nat len1 * 8))) = Some mem''.
Proof.
  intros until val2. intros Hval1 Hlen Hwrite1 Hwrite2.
  eapply write_bytes_combine; try eassumption.
  lia.
Qed.

