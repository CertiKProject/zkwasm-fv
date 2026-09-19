(* Copyright (C) CertiK 2024-2026 *)

(* Proofs about the optable in rtable.rs *)

Require Import List.
Require Import ZArith.
Require Import Lia.

Require Import Shared.
Require Import IntegerFunctions.
Require Import RTableModel.

Ltac destr_conj :=
  repeat match goal with
      [ H: _ /\ _  |- _ ] => destruct H
      end.

Lemma op_table_at_inj : forall {i op op' x x' y y' res res'},
    op_table_at i op x y res ->
    op_table_at i op' x' y' res' ->
    op=op' /\ x=x' /\ y=y' /\ res=res'.
Proof.
 intros; unfold op_table_at in *.
 destr_conj.
 repeat (split;try congruence).
Qed.
 

Theorem in_op_table_and : forall x y res,
  in_op_table BitOp_And x y res ->
       0 <= x < 256 
    /\ 0 <= y < 256 
    /\ res = Z.land x y.
Proof.
  destruct 1 as [i [[Hrange1 Hrange2] Hin]].
  assert (0 <= i < 256*256 
         \/ 256*256 <= i < 2*256*256 
         \/ 2*256*256 <= i < 3*256*256 
         \/ 3*256*256 <= i < 3*256*256 + 256
         \/ i = 3*256*256 + 256
         \/ 3*256*256 + 256 + 1 <= i < 3*256*256 + 256 + 128
         \/ 3*256*256 + 256 + 128 <= i).
   {
     destruct (Z_lt_dec i (256*256)); [left;lia|right].
     destruct (Z_lt_dec i (2*256*256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256 + 256)); [left;lia|right].
     destruct (Z.eq_dec i (3*256*256 + 256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256 + 256 + 128)); [left;lia|right].
    lia.
   }
   destruct H as [?| [?|[?|[?|[?|[?|?]]]]]].
  - assert (Hdiv := Z_div_mod i 256 ltac:(lia)).
    destruct (Z.div_eucl i 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    subst i.
    assert (Htable := op_table_and q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    repeat split; lia.
  - assert (Hdiv := Z_div_mod (i - 256*256) 256 ltac:(lia)).
    destruct (Z.div_eucl (i - 256*256) 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    assert (Hdiv' : i = 256*256 + 256 * q + r) by lia.
    subst i.
    assert (Htable := op_table_or q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_And, BitOp_Or in *; congruence.
  - assert (Hdiv := Z_div_mod (i - 2*256*256) 256 ltac:(lia)).
    destruct (Z.div_eucl (i - 2*256*256) 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    assert (Hdiv' : i = 2*256*256 + 256 * q + r) by lia.
    subst i.
    assert (Htable := op_table_xor q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_And, BitOp_Xor in *; congruence.
  - set (j := i - 3*256*256).
    assert (Htable := op_table_popcnt j ltac:(lia)).
    replace i with (3*256*256+j) in Hin by lia.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_And, Popcnt_index in *; congruence.
  - assert (Htable := op_table_power1).
    subst i.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_And, Power_index in *; congruence.
  - set (j := i - ( 3 * 256 * 256 + 256 + 1)).
    assert (Htable := op_table_power j ltac:(lia)).
    replace i with (3*256*256+256+1+j) in Hin by lia.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_And, Power_index in *; congruence.
  - assert (Htable := op_table_other i ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    repeat split; lia.
Qed.

Theorem in_op_table_or : forall x y res,
in_op_table BitOp_Or x y res ->
     0 <= x < 256 
  /\ 0 <= y < 256 
  /\ res = Z.lor x y.
Proof.
  destruct 1 as [i [[Hrange1 Hrange2] Hin]].
  assert (0 <= i < 256*256 
         \/ 256*256 <= i < 2*256*256 
         \/ 2*256*256 <= i < 3*256*256 
         \/ 3*256*256 <= i < 3*256*256 + 256
         \/ i = 3*256*256 + 256
         \/ 3*256*256 + 256 + 1 <= i < 3*256*256 + 256 + 128
         \/ 3*256*256 + 256 + 128 <= i).
   {
     destruct (Z_lt_dec i (256*256)); [left;lia|right].
     destruct (Z_lt_dec i (2*256*256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256 + 256)); [left;lia|right].
     destruct (Z.eq_dec i (3*256*256 + 256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256 + 256 + 128)); [left;lia|right].
    lia.
   }
   destruct H as [?| [?|[?|[?|[?|[?|?]]]]]].
  - assert (Hdiv := Z_div_mod i 256 ltac:(lia)).
    destruct (Z.div_eucl i 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    subst i.
    assert (Htable := op_table_and q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_Or, BitOp_And in *; congruence.
  - assert (Hdiv := Z_div_mod (i - 256*256) 256 ltac:(lia)).
    destruct (Z.div_eucl (i - 256*256) 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    assert (Hdiv' : i = 256*256 + 256 * q + r) by lia.
    subst i.
    assert (Htable := op_table_or q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    repeat split; lia.
  - assert (Hdiv := Z_div_mod (i - 2*256*256) 256 ltac:(lia)).
    destruct (Z.div_eucl (i - 2*256*256) 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    assert (Hdiv' : i = 2*256*256 + 256 * q + r) by lia.
    subst i.
    assert (Htable := op_table_xor q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_Or, BitOp_Xor in *; congruence.
  - set (j := i - 3*256*256).
    assert (Htable := op_table_popcnt j ltac:(lia)).
    replace i with (3*256*256+j) in Hin by lia.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_Or, Popcnt_index in *; congruence.
  - assert (Htable := op_table_power1).
    subst i.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_Or, Power_index in *; congruence.
  - set (j := i - ( 3 * 256 * 256 + 256 + 1)).
    assert (Htable := op_table_power j ltac:(lia)).
    replace i with (3*256*256+256+1+j) in Hin by lia.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_Or, Power_index in *; congruence.
  - assert (Htable := op_table_other i ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    repeat split; lia.
Qed.

Theorem in_op_table_xor : forall x y res,
in_op_table BitOp_Xor x y res ->
     0 <= x < 256 
  /\ 0 <= y < 256 
  /\ res = Z.lxor x y.
Proof.
  destruct 1 as [i [[Hrange1 Hrange2] Hin]].
  assert (0 <= i < 256*256 
         \/ 256*256 <= i < 2*256*256 
         \/ 2*256*256 <= i < 3*256*256 
         \/ 3*256*256 <= i < 3*256*256 + 256
         \/ i = 3*256*256 + 256
         \/ 3*256*256 + 256 + 1 <= i < 3*256*256 + 256 + 128
         \/ 3*256*256 + 256 + 128 <= i).
   {
     destruct (Z_lt_dec i (256*256)); [left;lia|right].
     destruct (Z_lt_dec i (2*256*256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256 + 256)); [left;lia|right].
     destruct (Z.eq_dec i (3*256*256 + 256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256 + 256 + 128)); [left;lia|right].
    lia.
   }
   destruct H as [?| [?|[?|[?|[?|[?|?]]]]]].
  - assert (Hdiv := Z_div_mod i 256 ltac:(lia)).
    destruct (Z.div_eucl i 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    subst i.
    assert (Htable := op_table_and q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_Xor, BitOp_And in *; congruence.
  - assert (Hdiv := Z_div_mod (i - 256*256) 256 ltac:(lia)).
    destruct (Z.div_eucl (i - 256*256) 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    assert (Hdiv' : i = 256*256 + 256 * q + r) by lia.
    subst i.
    assert (Htable := op_table_or q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_Xor, BitOp_Or in *; congruence.
  - assert (Hdiv := Z_div_mod (i - 2*256*256) 256 ltac:(lia)).
    destruct (Z.div_eucl (i - 2*256*256) 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    assert (Hdiv' : i = 2*256*256 + 256 * q + r) by lia.
    subst i.
    assert (Htable := op_table_xor q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    repeat split; lia.
  - set (j := i - 3*256*256).
    assert (Htable := op_table_popcnt j ltac:(lia)).
    replace i with (3*256*256+j) in Hin by lia.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_Xor, Popcnt_index in *; congruence.
  - assert (Htable := op_table_power1).
    subst i.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_Xor, Power_index in *; congruence.
  - set (j := i - ( 3 * 256 * 256 + 256 + 1)).
    assert (Htable := op_table_power j ltac:(lia)).
    replace i with (3*256*256+256+1+j) in Hin by lia.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_Xor, Power_index in *; congruence.
  - assert (Htable := op_table_other i ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold BitOp_Xor in *; congruence.
Qed.

Theorem in_op_table_popcnt : forall x y res,
in_op_table Popcnt_index x y res ->
     0 <= x < 256 
  /\ y = 0
  /\ res = popcnt x.
Proof.
  destruct 1 as [i [[Hrange1 Hrange2] Hin]].
  assert (0 <= i < 256*256 
         \/ 256*256 <= i < 2*256*256 
         \/ 2*256*256 <= i < 3*256*256 
         \/ 3*256*256 <= i < 3*256*256 + 256
         \/ i = 3*256*256 + 256
         \/ 3*256*256 + 256 + 1 <= i < 3*256*256 + 256 + 128
         \/ 3*256*256 + 256 + 128 <= i).
   {
     destruct (Z_lt_dec i (256*256)); [left;lia|right].
     destruct (Z_lt_dec i (2*256*256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256 + 256)); [left;lia|right].
     destruct (Z.eq_dec i (3*256*256 + 256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256 + 256 + 128)); [left;lia|right].
    lia.
   }
   destruct H as [?| [?|[?|[?|[?|[?|?]]]]]].
  - assert (Hdiv := Z_div_mod i 256 ltac:(lia)).
    destruct (Z.div_eucl i 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    subst i.
    assert (Htable := op_table_and q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold Popcnt_index, BitOp_And in *;
      congruence.
  - assert (Hdiv := Z_div_mod (i - 256*256) 256 ltac:(lia)).
    destruct (Z.div_eucl (i - 256*256) 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    assert (Hdiv' : i = 256*256 + 256 * q + r) by lia.
    subst i.
    assert (Htable := op_table_or q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold Popcnt_index, BitOp_Or in *; congruence.
  - assert (Hdiv := Z_div_mod (i - 2*256*256) 256 ltac:(lia)).
    destruct (Z.div_eucl (i - 2*256*256) 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    assert (Hdiv' : i = 2*256*256 + 256 * q + r) by lia.
    subst i.
    assert (Htable := op_table_xor q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold Popcnt_index, BitOp_Xor in *; congruence.
  - set (j := i - 3*256*256).
    assert (Htable := op_table_popcnt j ltac:(lia)).
    replace i with (3*256*256+j) in Hin by lia.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    repeat split; lia.
  - assert (Htable := op_table_power1).
    subst i.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold Popcnt_index, Power_index in *; congruence.
  - set (j := i - ( 3 * 256 * 256 + 256 + 1)).
    assert (Htable := op_table_power j ltac:(lia)).
    replace i with (3*256*256+256+1+j) in Hin by lia.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold Popcnt_index, Power_index in *; congruence.
  - assert (Htable := op_table_other i ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold Popcnt_index in *; congruence.
Qed.

Theorem in_op_table_power : forall x y res,
    in_op_table Power_index x y res ->
    (y <> 0 \/ res <> 0) ->
    128 <= y < 256 /\ res = 2 ^ (y - 128).
Proof.
  destruct 1 as [i [[Hrange1 Hrange2] Hin]].
  assert (0 <= i < 256*256 
         \/ 256*256 <= i < 2*256*256 
         \/ 2*256*256 <= i < 3*256*256 
         \/ 3*256*256 <= i < 3*256*256 + 256
         \/ i = 3*256*256 + 256
         \/ 3*256*256 + 256 + 1 <= i < 3*256*256 + 256 + 128
         \/ 3*256*256 + 256 + 128 <= i).
   {
     destruct (Z_lt_dec i (256*256)); [left;lia|right].
     destruct (Z_lt_dec i (2*256*256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256 + 256)); [left;lia|right].
     destruct (Z.eq_dec i (3*256*256 + 256)); [left;lia|right].
     destruct (Z_lt_dec i (3*256*256 + 256 + 128)); [left;lia|right].
    lia.
   }
   destruct H as [?| [?|[?|[?|[?|[?|?]]]]]].
  - assert (Hdiv := Z_div_mod i 256 ltac:(lia)).
    destruct (Z.div_eucl i 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    subst i.
    assert (Htable := op_table_and q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    unfold Power_index, BitOp_And, BitOp_Or in *.
    destr_conj; subst. congruence.
  - assert (Hdiv := Z_div_mod (i - 256*256) 256 ltac:(lia)).
    destruct (Z.div_eucl (i - 256*256) 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    assert (Hdiv' : i = 256*256 + 256 * q + r) by lia.
    subst i.
    assert (Htable := op_table_or q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold Power_index, BitOp_And, BitOp_Or in *. congruence.
  - assert (Hdiv := Z_div_mod (i - 2*256*256) 256 ltac:(lia)).
    destruct (Z.div_eucl (i - 2*256*256) 256) as [q r].
    destruct Hdiv as [Hdiv1 Hdiv2].
    assert (Hdiv' : i = 2*256*256 + 256 * q + r) by lia.
    subst i.
    assert (Htable := op_table_xor q r ltac:(lia) ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold  Power_index, BitOp_And, BitOp_Xor in *; congruence.
  - set (j := i - 3*256*256).
    assert (Htable := op_table_popcnt j ltac:(lia)).
    replace i with (3*256*256+j) in Hin by lia.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    unfold  Power_index, BitOp_And, Popcnt_index in *; congruence.
  - assert (Htable := op_table_power1).
    subst i.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    intros Hnonzero; destruct Hnonzero; lia.
  - set (j := i - ( 3 * 256 * 256 + 256 + 1)).
    assert (Htable := op_table_power j ltac:(lia)).
    replace i with (3*256*256+256+1+j) in Hin by lia.
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    intros Hrange.
    replace (128 + j - 128) with j by lia.
    rewrite Z.shiftl_1_l.
    split; lia.
  - assert (Htable := op_table_other i ltac:(lia)).
    assert (Hinj := op_table_at_inj Hin Htable).
    destr_conj; subst.
    repeat split; lia.
Qed.
