(* Copyright (C) CertiK 2024-2026 *)

Require Import Wasm.numerics.
Require Import Shared.
Require Import ETableModel.
Require Import Relation.
Require Import ImageTableModel.
Require Import CommonModel.

Require Import List.
Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.


Lemma bound_lt : forall x b b',  b < b' ->  0 <= x < b -> 0 <= x < b'.
Proof.
  lia.
Qed.


Lemma COMMON_RANGE_OFFSET_nonneg : 0 <= COMMON_RANGE_OFFSET.
Proof. cbv; intros; congruence. Qed.

Lemma OPCODE_ARG1_SHIFT_nonneg : 0 <= OPCODE_ARG1_SHIFT.
Proof. cbv; intros; congruence. Qed.

Lemma OPCODE_ARG0_SHIFT_nonneg : 0 <= OPCODE_ARG0_SHIFT.
Proof. cbv; intros. congruence. Qed.

Lemma OPCODE_CLASS_SHIFT_nonneg : 0 <= OPCODE_CLASS_SHIFT.
Proof. cbv; intros. congruence. Qed.

(* Lemmas used for instruction decoding proofs. *)
Definition bool_of_Z (z:Z) : bool
             := if Z.eqb z 0 then false else true.

Lemma Z_of_BinShiftOp_inj : forall b b',
    Z_of_BinShiftOp b = Z_of_BinShiftOp b' ->
    b = b'.
Proof.
  destruct b; destruct b'; simpl in *; intros; try lia; reflexivity.
Qed.

Lemma Z_of_BinOp_inj : forall b b',
    Z_of_BinOp b = Z_of_BinOp b' ->
    b = b'.
Proof.
  destruct b; destruct b'; simpl in *; intros; try lia; reflexivity.
Qed.

Lemma Z_of_UnaryOp_inj : forall b b',
    Z_of_UnaryOp b = Z_of_UnaryOp b' ->
    b = b'.
Proof.
  destruct b; destruct b'; simpl in *; intros; try lia; reflexivity.
Qed.

Lemma Z_of_BitOp_inj : forall b b',
    Z_of_BitOp b = Z_of_BitOp b' ->
    b = b'.
Proof.
  destruct b; destruct b'; simpl in *; intros; try lia; reflexivity.
Qed.

Lemma Z_of_RelOp_inj : forall b b',
    Z_of_RelOp b = Z_of_RelOp b' ->
    b = b'.
Proof.
  destruct b; destruct b'; simpl in *; intros; try lia; reflexivity.
Qed.

Lemma Z_of_bool_inj : forall b b',
    Z_of_bool b = Z_of_bool b' ->
    b = b'.
Proof.
  destruct b; destruct b'; simpl in *; intros; try lia; reflexivity.
Qed.

Lemma encode_load_access_inj : forall sz sz' sign sign',
    encode_load_access sz sign = encode_load_access sz' sign' ->
    sz = sz' /\ sign = sign'.
Proof.
  destruct sz; destruct sz'; destruct sign; destruct sign';
    unfold encode_load_access; simpl; intros; split; try lia; reflexivity.
Qed.

Lemma encode_store_access_inj : forall sz sz',
    encode_store_access sz  = encode_store_access sz' ->
    sz = sz'.
Proof.
  destruct sz; destruct sz';
    unfold encode_store_access; simpl; intros;  try lia; reflexivity.
Qed.

Lemma encode_ConvOp_inj : forall sign sign' is32 is32' src src' dst dst',
    encode_ConvOp sign is32 src dst = encode_ConvOp sign' is32' src' dst' ->
    sign = sign' /\ is32 = is32' /\ src = src' /\ dst = dst'.
Proof.
  destruct sign; destruct sign'; destruct is32; destruct is32'; destruct src; destruct src'; destruct dst; destruct dst';
    unfold encode_ConvOp; simpl; intros; repeat split; try lia; reflexivity.
Qed.
  
Lemma shift_plus_inj : forall {x x' y y' s},
    0 <= s ->
    Z.shiftl x s + y = Z.shiftl x' s + y' ->
    0 <= y < 2^s ->
    0 <= y' < 2^s ->
    x = x' /\ y = y'.
Proof.
  intros x x' y y' s Hs H Hy Hy'.
  rewrite !Zbits.Zshiftl_mul_two_p in * by lia.
  rewrite two_p_correct in *.

  assert (H' : (x * 2 ^ s + y)/2^s = (x' * 2 ^ s + y')/2^s) by
    (f_equal; assumption).
  rewrite !Z_div_plus_full_l in H' by lia.
  rewrite !Zdiv_small in H' by lia.
  assert (Hx : x = x') by lia.
  split; [assumption|].
  clear H' Hy Hy'.
  rewrite Hx in *.
  lia.
Qed.
  
Lemma shift_inj : forall {s},
    0 <= s ->
    forall x x',
    Z.shiftl x s = Z.shiftl x' s  ->
    x = x'.
Proof.
  intros s Hle x x' H.
  rewrite !Zbits.Zshiftl_mul_two_p in H by lia.
  pose (two_p_gt_ZERO s Hle).
  apply Z.mul_reg_r in H; lia.
Qed.

Lemma Int32_unsigned_inj : forall x x' ,
    Wasm_int.Int32.unsigned x = Wasm_int.Int32.unsigned x' ->
    x = x'.
Proof.
  intros.
  destruct x as [x xrange].
  destruct x' as [x' xrange'].
  simpl in *.
  subst.
  f_equal.
  destruct xrange as [p q].
  destruct xrange' as [p' q'].
  rewrite (Wasm_int.Int64.Z_lt_irrelevant p p').
  rewrite (Wasm_int.Int64.Z_lt_irrelevant q q').
  reflexivity.
Qed.  

Lemma Int64_unsigned_inj : forall x x' ,
    Wasm_int.Int64.unsigned x = Wasm_int.Int64.unsigned x' ->
    x = x'.
Proof.
  intros.
  destruct x as [x xrange].
  destruct x' as [x' xrange'].
  simpl in *.
  subst.
  f_equal.
  destruct xrange as [p q].
  destruct xrange' as [p' q'].
  rewrite (Wasm_int.Int64.Z_lt_irrelevant p p').
  rewrite (Wasm_int.Int64.Z_lt_irrelevant q q').
  reflexivity.
Qed.

Opaque Z.add Z.mul Z.shiftl Z_of_bool.


(* Size-bounding lemmas. *)

Lemma size_trans: forall s s' x,
    s < s' ->
    0 <= x < 2^s ->
    0 <= x < 2^s'.
Proof.
  intros s s' x H [H1 H2].
  split; try lia.
  apply Z.lt_le_trans with (2^s).
  lia.
  apply Z.pow_le_mono_r; lia.
Qed.  

Lemma int64_lt_arg1 : forall i,
 0 <= Wasm_int.Int64.unsigned i < 2 ^ OPCODE_ARG1_SHIFT.
Proof.
  intros i.
  unfold OPCODE_ARG1_SHIFT.
  replace (2^64) with Wasm_int.Int64.modulus.
  2: { unfold Wasm_int.Int64.modulus, Wasm_int.Int64.wordsize, Integers.Wordsize_64.wordsize.
       rewrite two_power_nat_correct.
       rewrite Zpower_nat_Z.
       f_equal. }
  apply Wasm_int.Int64.unsigned_range.
Qed.

Lemma int64_lt_64 : forall i,
 0 <= Wasm_int.Int64.unsigned i < 2 ^ 64.
Proof.
  intros i.
  destruct (Wasm_int.Int64.unsigned_range i).
  split; auto.
Qed.

Lemma int32_lt_32 : forall i,
 0 <= Wasm_int.Int32.unsigned i < 2 ^ 32.
Proof.
  intros i.
  unfold OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT,  COMMON_RANGE_OFFSET.
  destruct (Wasm_int.Int32.unsigned_range i).
  split; auto.
Qed.

Lemma int32_lt_arg0 : forall i,
 0 <= Wasm_int.Int32.unsigned i < 2 ^ OPCODE_ARG0_SHIFT.
Proof.
  intros.
  apply (size_trans 32).
  unfold OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET  ; lia.
  apply int32_lt_32.
Qed.

Lemma int64_lt_arg0 : forall i,
    0 <= Wasm_int.Int64.unsigned i < 2 ^ OPCODE_ARG0_SHIFT.
Proof.
  intros.
  apply (size_trans OPCODE_ARG1_SHIFT).
  unfold OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  lia.
  apply int64_lt_arg1.
Qed.

Lemma is32_lt_class_shift : forall x,
    0 <= x < 2^32 ->
    0 <= x < 2 ^ OPCODE_CLASS_SHIFT.
Proof.  
  intros.
  apply (size_trans 32).
  unfold OPCODE_CLASS_SHIFT, OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET; lia.
  auto.
Qed.

Lemma zero_lt_class_shift :  0 <= 0 < 2 ^ OPCODE_CLASS_SHIFT.
Proof.
  change OPCODE_CLASS_SHIFT with ( 64 + 32 + 32); lia.
Qed.  

Lemma shift_arg0_lt_class_shift : forall x,
    0 <= x < 2 ^ 32 ->
    0 <= Z.shiftl x OPCODE_ARG0_SHIFT < 2 ^ OPCODE_CLASS_SHIFT.
Proof.
  split.
  1: { apply Z.shiftl_nonneg; lia. }
  unfold OPCODE_CLASS_SHIFT, OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  rewrite !Z.shiftl_mul_pow2 by lia.
  lia.
Qed.


(* Reminder: 
Definition COMMON_RANGE_OFFSET := 32.
Definition OPCODE_ARG1_SHIFT := 64.
Definition OPCODE_ARG0_SHIFT := OPCODE_ARG1_SHIFT + COMMON_RANGE_OFFSET.
Definition OPCODE_CLASS_SHIFT := OPCODE_ARG0_SHIFT + COMMON_RANGE_OFFSET.

In other words, the layout is like this:

[class (16 bits)][arg0 (32 bits)][arg1 (32 bits)] [arg2  (64 bits)]

*)

Lemma shift_arg1_lt_arg0 : forall x,
    0 <= x < 2 ^ 32 ->
    0 <= Z.shiftl x OPCODE_ARG1_SHIFT < 2 ^ OPCODE_ARG0_SHIFT.
Proof.
  split.
  1: { apply Z.shiftl_nonneg; lia. }
  unfold OPCODE_CLASS_SHIFT, OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  rewrite !Z.shiftl_mul_pow2 by lia.
  lia.
Qed.

(* This is not a tight bound, but it's all we need below. *)
Lemma shift_arg1_lt_class_shift : forall x,
    0 <= x < 2 ^ 32 ->
    0 <= Z.shiftl x OPCODE_ARG1_SHIFT < 2 ^ OPCODE_CLASS_SHIFT.
Proof.
  intros.
  apply (size_trans OPCODE_ARG0_SHIFT).
  unfold OPCODE_CLASS_SHIFT, OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  lia.
  apply shift_arg1_lt_arg0; auto.
Qed.


Lemma Z_of_bool_isbit : forall b,
    Z_of_bool b = 0 \/ Z_of_bool b = 1.
Proof.
  destruct b; simpl; auto.
Qed.

Lemma isbit_is32 : forall x,
    (x = 0 \/ x = 1) ->
    0 <= x < 2^32.
Proof.
  destruct 1; subst; lia.
Qed.

Lemma Z_of_UnaryOp_is32 : forall b,
    0 <= Z_of_UnaryOp b < 2^32.
Proof.
  destruct b; simpl; lia.
Qed.

Lemma Z_of_BitOp_is32 : forall b,
    0 <= Z_of_BitOp b < 2^32.
Proof.
  destruct b; simpl; lia.
Qed.

Lemma Z_of_BinOp_is32 : forall b,
    0 <= Z_of_BinOp b < 2^32.
Proof.
  destruct b; simpl; lia.
Qed.

Lemma Z_of_BinShiftOp_is32 : forall b,
    0 <= Z_of_BinShiftOp b < 2^32.
Proof.
  destruct b; simpl; lia.
Qed.

Lemma Z_of_RelOp_is32 : forall b,
    0 <= Z_of_RelOp b < 2^32.
Proof.
  destruct b; simpl; lia.
Qed.    

Transparent Z_of_bool.
Lemma encode_load_access_is32 : forall l s,
   0 <= encode_load_access l s < 2^32.
Proof.
  destruct l; destruct s; unfold encode_load_access, Z_of_bool; simpl; lia.
Qed.

Lemma encode_store_access_is32 : forall l,
   0 <= encode_store_access l < 2^32.
Proof.
  destruct l;  unfold encode_store_access, Z_of_bool; simpl; lia.
Qed.

Lemma encode_ConvOp_is32 : forall sign is32 src dst,
    0 <= encode_ConvOp sign is32 src dst < 2^32.
Proof.
  destruct sign; destruct is32; destruct src; destruct dst; unfold encode_ConvOp; simpl;
    rewrite !Z.shiftl_mul_pow2 by lia;
    lia.
Qed.

Opaque Z_of_bool.

Require IntegerFunctions.

Lemma shift_plus_bound : forall x y i j,
    0 <= x < 2^i ->
    0 <= y < 2^j ->
    0 <= Z.shiftl x j + y < 2 ^ (j+i).
Proof.
  intros x y i j Hx Hy.
  assert (0 <= i).
  { destruct (Z_le_gt_dec 0 i).
    - assumption.
    - rewrite Z.pow_neg_r in Hx by lia. lia. }
  assert (0 <= j).
  { destruct (Z_le_gt_dec 0 j).
    - assumption.
    - rewrite Z.pow_neg_r in Hy by lia. lia. }
  rewrite Z.add_comm.
  rewrite IntegerFunctions.plus_lor_n by lia.
  apply (IntegerFunctions.lor_bound_r j); try lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  split; [lia|].
  rewrite Z.pow_add_r by lia.
  rewrite Z.mul_comm.
  apply Zmult_lt_compat_l; lia.
Qed.
  
Lemma shift_arg0_arg1_lt_class_shift : forall x y,
    0 <= x < 2^32 ->
    0 <= y < 2^64 ->
    0 <= Z.shiftl x OPCODE_ARG1_SHIFT + y < 2 ^ OPCODE_CLASS_SHIFT.
Proof.
  intros.
  unfold OPCODE_CLASS_SHIFT, COMMON_RANGE_OFFSET in *.
  unfold OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  assert (bound := shift_plus_bound x y 32 64 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma shift_arg1_64_lt_arg0 : forall x y,
    0 <= x < 2^32 ->
    0 <= y < 2^64 ->
    0 <= Z.shiftl x OPCODE_ARG1_SHIFT + y < 2 ^ OPCODE_ARG0_SHIFT.
Proof.
  unfold OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  intros.
  assert (bound := shift_plus_bound x y 32 64 ltac:(lia) ltac:(lia)).
  lia.
Qed.
  
Lemma shift_arg1_64_lt_class_shift : forall x y,
    0 <= x < 2^32 ->
    0 <= y < 2^OPCODE_ARG0_SHIFT -> 
    0 <= Z.shiftl x OPCODE_ARG0_SHIFT + y < 2 ^ OPCODE_CLASS_SHIFT.
Proof.
  unfold OPCODE_CLASS_SHIFT, OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  intros.
  assert (bound := shift_plus_bound x y 32 (64+32) ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma shift_16_class_shift_lt_144
  : forall x y,
  0 <= x < 2 ^ 16 ->
  0 <= y < 2 ^ OPCODE_CLASS_SHIFT ->
  0 <= Z.shiftl x OPCODE_CLASS_SHIFT + y <  2 ^ 144.
Proof.
  unfold OPCODE_CLASS_SHIFT, OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  intros.
  change 144 with (128+16).
  apply shift_plus_bound; lia.
Qed.
  
Lemma shift_16_class_shift_lt_144_no_plus
  : forall x,
  0 <= x < 2 ^ 16 ->
  0 <= Z.shiftl x OPCODE_CLASS_SHIFT <  2 ^ 144.
Proof.
  intros.
  replace  (Z.shiftl x OPCODE_CLASS_SHIFT) with ( Z.shiftl x OPCODE_CLASS_SHIFT + 0) by lia.  
  apply shift_16_class_shift_lt_144; auto.
  unfold OPCODE_CLASS_SHIFT, OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  lia.
Qed.

#[export] Hint Resolve int32_lt_32 : size_lemmas.
#[export] Hint Resolve int64_lt_64 : size_lemmas.
#[export] Hint Resolve int64_lt_arg1 : size_lemmas.
#[export] Hint Resolve int64_lt_arg0 : size_lemmas.
#[export] Hint Resolve int32_lt_arg0 : size_lemmas.
#[export] Hint Resolve is32_lt_class_shift : size_lemmas.
#[export] Hint Resolve zero_lt_class_shift : size_lemmas.
#[export] Hint Resolve shift_arg0_lt_class_shift : size_lemmas.
#[export] Hint Resolve shift_arg1_lt_arg0 : size_lemmas.
#[export] Hint Resolve shift_arg1_lt_class_shift : size_lemmas.
#[export] Hint Resolve Z_of_bool_isbit : size_lemmas.
#[export] Hint Resolve isbit_is32 : size_lemmas.
#[export] Hint Resolve Z_of_BitOp_is32 : size_lemmas.
#[export] Hint Resolve Z_of_BinOp_is32 : size_lemmas.
#[export] Hint Resolve Z_of_BinShiftOp_is32 : size_lemmas.
#[export] Hint Resolve Z_of_UnaryOp_is32 : size_lemmas.
#[export] Hint Resolve Z_of_RelOp_is32 : size_lemmas.
#[export] Hint Resolve encode_load_access_is32 : size_lemmas.
#[export] Hint Resolve encode_store_access_is32 : size_lemmas.
#[export] Hint Resolve encode_ConvOp_is32 : size_lemmas.

#[export] Hint Resolve shift_arg1_64_lt_arg0  : size_lemmas.
#[export] Hint Resolve shift_arg0_arg1_lt_class_shift   : size_lemmas.
#[export] Hint Resolve shift_arg1_64_lt_class_shift  : size_lemmas.

#[export] Hint Resolve shift_16_class_shift_lt_144  : size_lemmas.
#[export] Hint Resolve shift_16_class_shift_lt_144_no_plus  : size_lemmas.

Lemma opcode_of_instruction_inj : forall i1 i2,
    opcode_of_instruction i1 = opcode_of_instruction i2 ->
    i1 = i2.
Proof.
  (*
  (destruct i1; destruct i2; simpl; try rewrite <- !Zplus_assoc; intros H;
    try match goal with
      | [H: (Z.shiftl ?c1 OPCODE_CLASS_SHIFT + _)
                = Z.shiftl ?c2 OPCODE_CLASS_SHIFT |- _ ]
        => replace (Z.shiftl c2 OPCODE_CLASS_SHIFT) with (Z.shiftl c2 OPCODE_CLASS_SHIFT + 0) in H by lia
      | [H: (Z.shiftl ?c1 OPCODE_CLASS_SHIFT)
                = Z.shiftl ?c2 OPCODE_CLASS_SHIFT + _ |- _ ]
        => replace (Z.shiftl c1 OPCODE_CLASS_SHIFT) with (Z.shiftl c1 OPCODE_CLASS_SHIFT + 0) in H by lia
      end);
  try match goal with
    | [ H:    Z.shiftl ?c OPCODE_CLASS_SHIFT + _
            = Z.shiftl ?c OPCODE_CLASS_SHIFT + _ |- _] => apply Z.add_reg_l in H
    | [ H:    Z.shiftl _ OPCODE_CLASS_SHIFT
            = Z.shiftl _ OPCODE_CLASS_SHIFT |- _] => apply (shift_inj OPCODE_CLASS_SHIFT_nonneg) in H; now congruence
(*    | [ H: _ = 0 |- _] => admit (* todo later *) *)
(*    | [ H: 0 = _ |- _] => admit (* todo later *) *)
                                                                                
      | [ H:    Z.shiftl _ OPCODE_CLASS_SHIFT + _
            = Z.shiftl _ OPCODE_CLASS_SHIFT + _ |- _] => destruct (shift_plus_inj OPCODE_CLASS_SHIFT_nonneg H); [eauto 7 with size_lemmas | eauto 7 with size_lemmas | congruence]
    end;

  try match goal with
    | [ H:    Z.shiftl ?c OPCODE_ARG0_SHIFT + _
            = Z.shiftl ?c OPCODE_ARG0_SHIFT + _ |- _] => apply Z.add_reg_l in H
    | [ H:    Z.shiftl _ OPCODE_ARG0_SHIFT
            = Z.shiftl _ OPCODE_ARG0_SHIFT |- _] => apply (shift_inj OPCODE_ARG0_SHIFT_nonneg) in H
      | [ H:   Z.shiftl _ OPCODE_ARG0_SHIFT + _
            = Z.shiftl _ OPCODE_ARG0_SHIFT + _ |- _] => destruct (shift_plus_inj OPCODE_ARG0_SHIFT_nonneg H); clear H; [eauto 7 with size_lemmas | eauto 7 with size_lemmas  | ]
    end;
  try match goal with
    | [ H:    Z.shiftl ?c OPCODE_ARG1_SHIFT + _
            = Z.shiftl ?c OPCODE_ARG1_SHIFT + _ |- _] => apply Z.add_reg_l in H
    | [ H:    Z.shiftl _ OPCODE_ARG1_SHIFT
            = Z.shiftl _ OPCODE_ARG1_SHIFT |- _] => apply (shift_inj OPCODE_ARG1_SHIFT_nonneg) in H
      | [ H:   Z.shiftl _ OPCODE_ARG1_SHIFT + _
            = Z.shiftl _ OPCODE_ARG1_SHIFT + _ |- _] => destruct (shift_plus_inj OPCODE_ARG1_SHIFT_nonneg H); clear H; [eauto 7 with size_lemmas | eauto 7 with size_lemmas  | ]
    end;
  repeat match goal with
    | [ H: Z_of_BinShiftOp _ = Z_of_BinShiftOp _ |- _] => apply Z_of_BinShiftOp_inj in H
    | [ H: Z_of_BinOp _ = Z_of_BinOp _ |- _] => apply Z_of_BinOp_inj in H
    | [ H: Z_of_UnaryOp _ = Z_of_UnaryOp _ |- _] => apply Z_of_UnaryOp_inj in H
    | [ H: Z_of_BitOp _ = Z_of_BitOp _ |- _] => apply Z_of_BitOp_inj in H
    | [ H: Z_of_RelOp _ = Z_of_RelOp _ |- _] => apply Z_of_RelOp_inj in H
    | [ H: Z_of_bool _ = Z_of_bool _ |- _] => apply Z_of_bool_inj in H
    | [ H:  encode_load_access _ _ = encode_load_access _ _ |- _] =>
        apply encode_load_access_inj in H; destruct H
    | [ H:  encode_store_access _ = encode_store_access _ |- _] =>
        apply encode_store_access_inj in H; destruct H
    | [ H:  encode_ConvOp _ _ _ _ = encode_ConvOp _ _ _ _ |- _] =>
        apply encode_ConvOp_inj in H; destruct H as [? [? [? ?]]]
    | [ H: Wasm_int.Int32.unsigned _ = Wasm_int.Int32.unsigned _ |- _] => apply Int32_unsigned_inj in H
    | [ H: Wasm_int.Int64.unsigned _ = Wasm_int.Int64.unsigned _ |- _] => apply Int64_unsigned_inj in H
         end;
  try congruence.
Qed.   *)
  Admitted.

(* For just the instruction OpBinBit, we can't use the same decode proof as the other instructions,
   and instead we need this extra lemma... *)
Lemma opcode_of_instruction_weird_extra_case : forall is32 i,
    (is32 = 0 \/ is32 = 1) ->    
    opcode_of_instruction i <>      
      Z.shiftl (OpcodeClass_u64 BinBit) OPCODE_CLASS_SHIFT +
            RTableModel.Popcnt_index * Z.shiftl 1 OPCODE_ARG0_SHIFT +
        is32 * Z.shiftl 1 OPCODE_ARG1_SHIFT.
Proof.
  intros i32 i Hi32_bit.
  assert  (Hbound: 0 <= RTableModel.Popcnt_index * Z.shiftl 1 OPCODE_ARG0_SHIFT + i32 * Z.shiftl 1 OPCODE_ARG1_SHIFT <
  2 ^ OPCODE_CLASS_SHIFT).
  {
    replace  (RTableModel.Popcnt_index * Z.shiftl 1 OPCODE_ARG0_SHIFT)
      with   (Z.shiftl RTableModel.Popcnt_index OPCODE_ARG0_SHIFT).
    2: {
      rewrite !Z.shiftl_mul_pow2 by (apply OPCODE_ARG0_SHIFT_nonneg).
      lia.
    }    
    apply shift_arg1_64_lt_class_shift.
    - unfold RTableModel.Popcnt_index. lia.
    - replace  (i32 * Z.shiftl 1 OPCODE_ARG1_SHIFT) with (Z.shiftl i32 OPCODE_ARG1_SHIFT + 0).
      2: {  rewrite !Z.shiftl_mul_pow2 by (apply OPCODE_ARG1_SHIFT_nonneg).
      lia.
      }
      apply shift_arg1_64_lt_arg0; lia.
  }  
  
  destruct i; simpl; try rewrite <- !Zplus_assoc; intros H;
    (try match goal with
      | [H: (Z.shiftl ?c1 OPCODE_CLASS_SHIFT + _)
                = Z.shiftl ?c2 OPCODE_CLASS_SHIFT |- _ ]
        => replace (Z.shiftl c2 OPCODE_CLASS_SHIFT) with (Z.shiftl c2 OPCODE_CLASS_SHIFT + 0) in H by lia
      | [H: (Z.shiftl ?c1 OPCODE_CLASS_SHIFT)
                = Z.shiftl ?c2 OPCODE_CLASS_SHIFT + _ |- _ ]
        => replace (Z.shiftl c1 OPCODE_CLASS_SHIFT) with (Z.shiftl c1 OPCODE_CLASS_SHIFT + 0) in H by lia
      end);

 try match goal with
    | [ H:    Z.shiftl ?c OPCODE_CLASS_SHIFT + _
            = Z.shiftl ?c OPCODE_CLASS_SHIFT + _ |- _] => apply Z.add_reg_l in H
    | [ H:    Z.shiftl _ OPCODE_CLASS_SHIFT
            = Z.shiftl _ OPCODE_CLASS_SHIFT |- _] => apply (shift_inj OPCODE_CLASS_SHIFT_nonneg) in H; now congruence
                                                                                
      | [ H:    Z.shiftl _ OPCODE_CLASS_SHIFT + _
            = Z.shiftl _ OPCODE_CLASS_SHIFT + _ |- _] => destruct (shift_plus_inj OPCODE_CLASS_SHIFT_nonneg H); [eauto 7 with size_lemmas | eauto 7 with size_lemmas | congruence]
    end.

  Transparent Z.add Z.mul Z.shiftl Z.pow Z_of_BitOp Z_of_bool OPCODE_ARG0_SHIFT OPCODE_ARG1_SHIFT.
  destruct Hi32_bit; subst; destruct b; destruct b0;
  cbv in H; congruence.
  Opaque Z.add Z.mul Z.shiftl Z.pow Z_of_BitOp Z_of_bool OPCODE_ARG0_SHIFT OPCODE_ARG1_SHIFT.
Qed.

Lemma iscommon_is_2_32 : forall x,
    0 <= x < common ->
    0 <= x < 2^32.
Proof.
  intros.
  eapply bound_lt.
  apply common_le_2_32.
  auto.
Qed.

Lemma iscommon_is_2_64 : forall x,
    0 <= x < common ->
    0 <= x < 2^64.
Proof.
  intros.
  apply bound_lt with (2^32).
  lia.
  apply iscommon_is_2_32.
  auto.
Qed.

Lemma iscommon_is32 : forall x,
    0 <= x < common ->
    0 <= x <= Wasm_int.Int32.max_unsigned.
Proof.
  intros. 
  pose (iscommon_is_2_32 x).
  change ( Wasm_int.Int32.max_unsigned) with (2^32  -1).
  lia.
Qed.

Lemma iscommon_is64 : forall x,
 0 <= x < common ->
 0 <= x <= Wasm_int.Int64.max_unsigned.
Proof.
  intros. 
  pose (iscommon_is_2_64 x).
  change ( Wasm_int.Int64.max_unsigned) with (2^64  -1).
  lia.
Qed.

Lemma is64_is64 : forall x,
 0 <= x < Wasm_int.Int64.modulus ->
 0 <= x <= Wasm_int.Int64.max_unsigned.
Proof.
  change Wasm_int.Int64.modulus with (2^64).
  change Wasm_int.Int64.max_unsigned with (2^64 -1).
  lia.
Qed.
  
Lemma bool_of_Z_simpl : forall x,
    (x = 0 \/ x = 1) ->
    (Z_of_bool (bool_of_Z x)) = x.
Proof.
  Transparent Z_of_bool bool_of_Z.
  destruct 1; subst; unfold bool_of_Z; simpl; reflexivity.
  Opaque Z_of_bool bool_of_Z.
Qed.  

Lemma iscommon_lt_class_shift: forall x,
    0 <= x < common ->
    0 <= x <   2 ^ OPCODE_CLASS_SHIFT.
Proof.
  intros x H.
  change OPCODE_CLASS_SHIFT with 128.
  apply iscommon_is_2_32 in H.
  lia.
Qed.


Lemma iscommon_lt_arg0_shift: forall x,
    0 <= x < common ->
    0 <= x <   2 ^ OPCODE_ARG0_SHIFT.
Proof.
  intros x H.
  change OPCODE_ARG0_SHIFT with 96.
  apply iscommon_is_2_32 in H.
  lia.
Qed.

#[export] Hint Resolve iscommon_is_2_32 : size_lemmas.
#[export] Hint Resolve iscommon_is_2_64 : size_lemmas.
#[export] Hint Resolve iscommon_lt_class_shift : size_lemmas.
#[export] Hint Resolve iscommon_lt_arg0_shift : size_lemmas.

Lemma U64_unsigned_repr : forall c,
    is64 c ->
    forall i,
    Wasm_int.Int64.unsigned (Wasm_int.Int64.repr (etable_values c i)) = (etable_values c i).
Proof.
  intros.
  apply Wasm_int.Int64.unsigned_repr.
  apply is64_is64.
  apply H.
Qed.

Lemma common_unsigned_repr: forall c,
    iscommon c ->
    forall i,
    Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (etable_values c i)) = (etable_values c i).
Proof.
  intros.
  apply Wasm_int.Int32.unsigned_repr.
  apply iscommon_is32.
  apply H.
Qed.

Lemma common_unsigned_repr64: forall c,
    iscommon c ->
    forall i,
    Wasm_int.Int64.unsigned (Wasm_int.Int64.repr (etable_values c i)) = (etable_values c i).
Proof.
  intros.
  apply Wasm_int.Int64.unsigned_repr.
  apply iscommon_is64.
  apply H.
Qed.

Transparent Z_of_bool.
Lemma bool_is_common : forall x,
    0 <= Z_of_bool x < common.
Proof.
  split.
  - destruct x; simpl; lia.
  - pose CommonModel.one_lt_common.
    destruct x; simpl; lia.
Qed.

Lemma isbit_iscommon : forall x,
    (x = 0 \/ x = 1) ->
    0 <= x < common.
Proof.
  intros x H.
  split.
  - lia.
  - pose CommonModel.one_lt_common.
    lia.
Qed.

Definition encode_br_table_entry' fid iid index drop keep dst_pc :=
  Z.shiftl (Z.shiftl (Z.shiftl (Z.shiftl (Z.shiftl fid 32 + iid) 32 + index) 32 + drop) 32 + keep) 32 + dst_pc.

Lemma encode_br_table_entry'_spec : forall fid iid index drop keep dst_pc,
    0 <= fid < 2^32 ->
    0 <= iid < 2^32 ->
    0 <= index < 2^32 ->
    0 <= drop < 2^32 ->
    0 <= keep < 2^32 ->
    0 <= dst_pc < 2^32 ->
    encode_br_table_entry fid iid index drop keep dst_pc
    =  encode_br_table_entry' fid iid index drop keep dst_pc.
Proof.
  intros  fid iid index drop keep dst_pc Hfid Hiid Hindex Hdrop Hkeep Hdst_pc.
  unfold   encode_br_table_entry,   encode_br_table_entry'.
  replace ( (0 * INDIRECT_CLASS_SHIFT + fid * Z.shiftl 1 (0 + 32 + 32 + 32 + 32 + 32) +
   iid * Z.shiftl 1 (0 + 32 + 32 + 32 + 32) + index * Z.shiftl 1 (0 + 32 + 32 + 32) +
               drop * Z.shiftl 1 (0 + 32 + 32) + keep * Z.shiftl 1 (0 + 32) + dst_pc))
    with
    ( fid * Z.shiftl 1 (32 + 32 + 32 + 32 + 32) + iid * Z.shiftl 1 (32 + 32 + 32 + 32) +
  index * Z.shiftl 1 (32 + 32 + 32) + drop * Z.shiftl 1 (32 + 32) + keep * Z.shiftl 1 32 + dst_pc).
  2: { rewrite Z.mul_0_l.
       reflexivity.
  }
  replace (fid * Z.shiftl 1 (32 + 32 + 32 + 32 + 32) + iid * Z.shiftl 1 (32 + 32 + 32 + 32) +
             index * Z.shiftl 1 (32 + 32 + 32) + drop * Z.shiftl 1 (32 + 32) + keep * Z.shiftl 1 32 + dst_pc)
    with (Z.shiftl fid (32 + 32 + 32 + 32 + 32) + Z.shiftl iid (32 + 32 + 32 + 32) +
  Z.shiftl index (32 + 32 + 32) + Z.shiftl drop (32 + 32) + Z.shiftl keep 32 + dst_pc).
  2: {
    rewrite !Z.shiftl_mul_pow2 by lia.
    reflexivity.
  }
  replace (Z.shiftl fid (32 + 32 + 32 + 32 + 32) + Z.shiftl iid (32 + 32 + 32 + 32) +
             Z.shiftl index (32 + 32 + 32) + Z.shiftl drop (32 + 32) + Z.shiftl keep 32 + dst_pc)
    with (Z.shiftl (Z.shiftl (Z.shiftl (Z.shiftl (Z.shiftl fid 32 + iid) 32 + index) 32 + drop) 32 + keep) 32 + dst_pc).
  2: {
    rewrite !Z.shiftl_mul_pow2 by lia.
    rewrite !Z.pow_add_r by lia.
    lia.
  }    
  rewrite Zmod_small.
  { reflexivity. }
  { 
    apply bound_lt with (2^(6*32)).
    apply  encode_br_table_entry_field_order.
    change (2 ^ (6 * 32)) with (2 ^ (32+(32+(32+(32+(32+32)))))).
    repeat apply shift_plus_bound; auto.
  }
Qed.  
       
Lemma encode_br_table_entry_inj :
  forall fid fid' iid iid' index index' drop drop' keep keep' dst_pc dst_pc',
    0 <= fid < 2^32 ->
    0 <= fid' < 2^32 ->
    0 <= iid < 2^32 ->
    0 <= iid' < 2^32 ->
    0 <= index < 2^32 ->
    0 <= index' < 2^32 ->
    0 <= drop < 2^32 ->
    0 <= drop' < 2^32 ->
    0 <= keep < 2^32 ->
    0 <= keep' < 2^32 ->
    0 <= dst_pc < 2^32 ->
    0 <= dst_pc' < 2^32 ->
    encode_br_table_entry fid iid index drop keep dst_pc
    =  encode_br_table_entry fid' iid' index' drop' keep' dst_pc' ->
    fid=fid' /\ iid=iid' /\ index=index' /\ drop = drop' /\ keep=keep' /\ dst_pc = dst_pc'.
Proof.
  intros.
  rewrite !encode_br_table_entry'_spec in H11 by auto.
  unfold encode_br_table_entry' in H11.
  assert (nonneg32 : 0 <= 32) by lia.
  repeat match goal with
  | [ H:    Z.shiftl _ 32 + _
            = Z.shiftl _ 32 + _ |- _] => destruct (shift_plus_inj nonneg32 H); clear H; [eauto 7 with size_lemmas | eauto 7 with size_lemmas | ]
         end.
  lia.
Qed.


Lemma encode_BrTableEntry_inj :
  forall fid iid index drop keep dst_pc e,
    0 <= fid < 2^32 ->
    0 <= iid < 2^32 ->
    0 <= index < 2^32 ->
    0 <= drop < 2^32 ->
    0 <= keep < 2^32 ->
    0 <= dst_pc < 2^32 ->
    encode_br_table_entry fid iid index drop keep dst_pc
    =  encode_BrTableEntry e fid iid index ->
    drop = Wasm_int.Int32.unsigned (br_table_drop e) /\ keep=Z_of_bool (br_table_keep e) /\ dst_pc = Wasm_int.Int32.unsigned (br_table_dst_pc e).
Proof.
  intros.
  unfold encode_BrTableEntry in *.
  apply encode_br_table_entry_inj in H5;  auto using iscommon_is_2_32, bool_is_common;
  change ( 2 ^ 32) with Wasm_int.Int32.modulus; auto using Wasm_int.Int32.unsigned_range.
  lia.
Qed.

Lemma opcode_of_instruction_range : forall instr,
    0 <= opcode_of_instruction instr < 2^144.
Proof.
  destruct instr; simpl;
    change (Z.pow_pos 2 144) with (2^144);
    try rewrite <- !Zplus_assoc;
  try match goal with | [ |- context [ Z.shiftl ?x OPCODE_CLASS_SHIFT]] => (assert (0 <= x < 2^64) by lia) end;  
  eauto 7 with size_lemmas.
Qed.
  

Lemma encode_instruction_table_entry_inj : forall fid fid' iid iid' x x',
    0 <= fid < common ->
    0 <= iid < common ->
    0 <= x < 2^144 ->
    0 <= fid' < common ->
    0 <= iid' < common ->
    0 <= x' < 2^144 ->
    encode_instruction_table_entry fid iid x = encode_instruction_table_entry fid' iid' x' ->
    fid = fid' /\ iid = iid' /\ x = x'.
Proof.
  intros.
  unfold encode_instruction_table_entry in H5.
  replace  (fid * Z.shiftl 1 (144 + COMMON_RANGE_OFFSET) + iid * Z.shiftl 1 144)
      with ( Z.shiftl (Z.shiftl fid COMMON_RANGE_OFFSET + iid) 144) in H5.
    2: { unfold COMMON_RANGE_OFFSET.
         rewrite !Z.shiftl_mul_pow2 by lia.
         lia.
    }
  replace  (fid' * Z.shiftl 1 (144 + COMMON_RANGE_OFFSET) + iid' * Z.shiftl 1 144)
    with ( Z.shiftl (Z.shiftl fid' COMMON_RANGE_OFFSET + iid') 144) in H5.
    2: { unfold COMMON_RANGE_OFFSET.
         rewrite !Z.shiftl_mul_pow2 by lia.
         lia.
    }

  rewrite Z.mod_small in H5.
  2: {
    apply bound_lt with (2^208).
    apply  encode_instruction_table_entry_field_order.

    change (208) with (144 + (32 + 32)).
    apply shift_plus_bound; auto using iscommon_is_2_32.
    apply shift_plus_bound; auto using iscommon_is_2_32.
  }
  rewrite Z.mod_small in H5.
  2: {
    apply bound_lt with (2^208).
    apply  encode_instruction_table_entry_field_order.
    change (208) with (144 + (32 + 32)).
    apply shift_plus_bound; auto using iscommon_is_2_32.
    apply shift_plus_bound; auto using iscommon_is_2_32.
  }

  apply shift_plus_inj in H5; try lia.
  destruct H5.
  unfold COMMON_RANGE_OFFSET in H5.
  apply shift_plus_inj in H5; auto using iscommon_is_2_32; lia.
Qed.



Require OpBinModel OpBinBitModel OpBinShiftModel OpBrModel OpBrIfModel OpBrIfEqzModel OpBrTableModel OpCallModel OpCallIndirectModel
OpConstModel OpConversionModel OpGlobalGetModel OpGlobalSetModel OpLoadModel 
OpLocalGetModel OpLocalSetModel OpLocalTeeModel OpMemoryGrowModel OpMemorySizeModel OpRelModel OpReturnModel
OpSelectModel OpStoreModel OpTestModel OpUnaryModel.


Lemma options_1 : forall s,
    0 <= s ->
    forall a1,
  a1 * Z.shiftl 1 s = Z.shiftl a1 s.
Proof.
  intros.
  rewrite !Z.shiftl_mul_pow2 by lia.
  lia.
Qed.    

Lemma options_01 : forall s,
    0 <= s ->
    forall a0 a1  rest,
 a0 * Z.shiftl 0 s +
  (a1 * Z.shiftl 1 s + rest)
 = Z.shiftl (a1) s + rest.
Proof.
  intros.
  rewrite Z.shiftl_0_l.
  rewrite !Z.shiftl_mul_pow2 by lia.
  lia.
Qed.

Lemma options_2 : forall s,
    0 <= s ->
    forall a0 a1 a2 rest,
 a0 * Z.shiftl 0 s +
  (a1 * Z.shiftl 1 s +
   (a2 * Z.shiftl 2 s + rest))
 = Z.shiftl (a1 + a2*2) s + rest.
Proof.
  intros.
  rewrite Z.shiftl_0_l.
  rewrite !Z.shiftl_mul_pow2 by lia.
  lia.
Qed.

Lemma options_3 : forall s,
    0 <= s ->
    forall a0 a1 a2 a3 rest,
 a0 * Z.shiftl 0 s +
  (a1 * Z.shiftl 1 s +
   (a2 * Z.shiftl 2 s +
    (a3 * Z.shiftl 3 s + rest)))
 = Z.shiftl (a1 + a2*2 + a3*3) s + rest.
Proof.
  intros.
  rewrite Z.shiftl_0_l.
  rewrite !Z.shiftl_mul_pow2 by lia.
  lia.
Qed.    

Lemma options_4 : forall s,
    0 <= s ->
    forall a0 a1 a2 a3 a4 rest,
 a0 * Z.shiftl 0 s +
  (a1 * Z.shiftl 1 s +
   (a2 * Z.shiftl 2 s +
    (a3 * Z.shiftl 3 s +
     (a4 * Z.shiftl 4 s + rest))))
 = Z.shiftl (a1 + a2*2 + a3*3 + a4*4) s + rest.
Proof.
  intros.
  rewrite Z.shiftl_0_l.
  rewrite !Z.shiftl_mul_pow2 by lia.
  lia.
Qed.    

Lemma options_6 : forall s,
    0 <= s ->
    forall a0 a1 a2 a3 a4 a5 a6 rest,
 a0 * Z.shiftl 0 s +
  (a1 * Z.shiftl 1 s +
   (a2 * Z.shiftl 2 s +
    (a3 * Z.shiftl 3 s +
       (a4 * Z.shiftl 4 s +
          (a5 * Z.shiftl 5 s +
             (a6 * Z.shiftl 6 s
              + rest))))))
 = Z.shiftl (a1 + a2*2 + a3*3 + a4*4 + a5*5 + a6*6) s + rest.
Proof.
  intros.
  rewrite Z.shiftl_0_l.
  rewrite !Z.shiftl_mul_pow2 by lia.
  lia.
Qed.

Opaque Z.sub.

Lemma config_opcode_range : forall idx i,
    0 <= config_opcode (opcode_config idx i) < 2^144.
Proof.
  intros idx i.
  destruct idx; simpl;  change (Z.pow_pos 2 144) with (2^144); try rewrite <- !Zplus_assoc;
    eauto with size_lemmas;
    try (apply shift_16_class_shift_lt_144; [lia|]);
    try (apply shift_16_class_shift_lt_144_no_plus; lia).
  - rewrite (options_4 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).
    apply shift_arg1_64_lt_class_shift.
    {
      pose (OpBinShiftModel.is_shr_u_bit i).
      pose (OpBinShiftModel.is_shr_s_bit i).
      pose (OpBinShiftModel.is_rotl_bit i).
      pose (OpBinShiftModel.is_rotr_bit i).
      lia.
    }

    rewrite (options_1 OPCODE_ARG1_SHIFT OPCODE_ARG1_SHIFT_nonneg).
    apply  shift_arg1_lt_arg0.
    (* c.f. apply  shift_arg1_64_lt_arg0. *)
    {
      pose (OpBinShiftModel.is_i32_bit i).
      lia.
    }
  - rewrite (options_6 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).
    apply shift_arg1_64_lt_class_shift.
    {
      pose (OpBinModel.is_sub_bit i).
      pose (OpBinModel.is_mul_bit i).
      pose (OpBinModel.is_div_u_bit i).
      pose (OpBinModel.is_div_s_bit i).
      pose (OpBinModel.is_rem_u_bit i).
      pose (OpBinModel.is_rem_s_bit i).
      lia.
    }

    rewrite (options_1 OPCODE_ARG1_SHIFT OPCODE_ARG1_SHIFT_nonneg).
    apply  shift_arg1_lt_arg0.
    (* c.f. apply  shift_arg1_64_lt_arg0. *)
    {
      pose (OpBinModel.is_i32_bit i).
      lia.
    }
  - rewrite (options_1 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).
    apply shift_arg1_64_lt_class_shift.
    {
      pose (OpBrIfEqzModel.drop_cell_common i).
      auto using iscommon_is_2_32.
    }
    rewrite (options_1 OPCODE_ARG1_SHIFT OPCODE_ARG1_SHIFT_nonneg).
    apply  shift_arg1_64_lt_arg0. 
    {
      pose (OpBrIfEqzModel.keep_cell_bit i).
      lia.
    }
    pose  (OpBrIfEqzModel.dst_pc_cell_common i).
    auto with size_lemmas.
    
  - rewrite (options_1 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).
    apply shift_arg1_64_lt_class_shift.
    {
      pose (OpBrIfModel.drop_cell_common i).
      auto with size_lemmas.
    }
    rewrite (options_1 OPCODE_ARG1_SHIFT OPCODE_ARG1_SHIFT_nonneg).
    apply  shift_arg1_64_lt_arg0. 
    {
      pose (OpBrIfModel.keep_cell_bit i).
      lia.
    }
    pose  (OpBrIfModel.dst_pc_cell_common i).
    auto with size_lemmas.

  - rewrite (options_1 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).
    apply shift_arg1_64_lt_class_shift.
    {
      pose (OpBrModel.drop_cell_common i).
      auto with size_lemmas.
    }
    rewrite (options_1 OPCODE_ARG1_SHIFT OPCODE_ARG1_SHIFT_nonneg).
    apply  shift_arg1_64_lt_arg0. 
    {
      pose (OpBrModel.keep_cell_bit i).
      lia.
    }
    pose  (OpBrModel.dst_pc_cell_common i).
    auto with size_lemmas.

  - rewrite (options_1 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).    
    apply shift_arg0_lt_class_shift.
    pose (OpCallModel.index_common i).
    auto with size_lemmas.
  - rewrite (options_1 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).    
    apply shift_arg1_64_lt_class_shift.
    {
      pose (OpConstModel.is_i32_bit i).
      lia.
    }
    pose (OpConstModel.value_U64 i).
    change OPCODE_ARG0_SHIFT with 96.
    change Wasm_int.Int64.modulus with (2^64) in *.
    lia.
  - unfold encode_conversion.
    rewrite !Z.shiftl_mul_pow2 by lia.
    change OPCODE_CLASS_SHIFT with 128.

    Transparent Z.mul Z.pow.
    
    destruct (OpConversionModel.sign_op_bit i) as [H1|H1];
    destruct (OpConversionModel.value_type_is_i32_bit i) as [H2|H2];
    destruct (OpConversionModel.value_is_i8_bit i) as [H3|H3];
    destruct (OpConversionModel.value_is_i16_bit i) as [H4|H4];
    destruct (OpConversionModel.value_is_i32_bit i) as [H5|H5];
    destruct (OpConversionModel.value_is_i64_bit i) as [H6|H6];
    destruct (OpConversionModel.res_is_i32_bit i) as [H7|H7];
    destruct (OpConversionModel.res_is_i64_bit i) as [H8|H8];
      rewrite H1, H2, H3, H4, H5, H6, H7, H8; lia.
    Opaque Z.mul Z.pow.
  - pose (OpGlobalGetModel.idx_common i).
    auto with size_lemmas.
  - pose (OpGlobalSetModel.idx_common i).
    auto with size_lemmas.
  - rewrite (options_1 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).
    apply shift_arg1_64_lt_class_shift.
    {
      pose (OpLocalGetModel.is_i32_bit i).
      auto with size_lemmas.
    }
    pose (OpLocalGetModel.offset_common i).
    auto with size_lemmas.
  - rewrite (options_1 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).
    apply shift_arg1_64_lt_class_shift.
    {
      pose (OpLocalSetModel.is_i32_bit i).
      auto with size_lemmas.
    }
    pose (OpLocalSetModel.offset_common i).
    auto with size_lemmas.
  - rewrite (options_1 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).
    apply shift_arg1_64_lt_class_shift.
    {
      pose (OpLocalTeeModel.is_i32_bit i).
      auto with size_lemmas.
    }
    pose (OpLocalTeeModel.offset_common i).
    auto with size_lemmas.
  -
    replace ( etable_values op_rel_op_is_eq i * Z.shiftl 0 OPCODE_ARG0_SHIFT +
  (etable_values op_rel_op_is_ne i * Z.shiftl 1 OPCODE_ARG0_SHIFT +
   (etable_values op_rel_op_is_gt i * (1 - etable_values op_rel_is_sign i) *
    Z.shiftl 3 OPCODE_ARG0_SHIFT +
    (etable_values op_rel_op_is_ge i * (1 - etable_values op_rel_is_sign i) *
     Z.shiftl 5 OPCODE_ARG0_SHIFT +
     (etable_values op_rel_op_is_lt i * (1 - etable_values op_rel_is_sign i) *
      Z.shiftl 7 OPCODE_ARG0_SHIFT +
      (etable_values op_rel_op_is_le i * (1 - etable_values op_rel_is_sign i) *
       Z.shiftl 9 OPCODE_ARG0_SHIFT +
       (etable_values op_rel_op_is_gt i * etable_values op_rel_is_sign i *
        Z.shiftl 2 OPCODE_ARG0_SHIFT +
        (etable_values op_rel_op_is_ge i * etable_values op_rel_is_sign i *
         Z.shiftl 4 OPCODE_ARG0_SHIFT +
         (etable_values op_rel_op_is_lt i * etable_values op_rel_is_sign i *
          Z.shiftl 6 OPCODE_ARG0_SHIFT +
          (etable_values op_rel_op_is_le i * etable_values op_rel_is_sign i *
           Z.shiftl 8 OPCODE_ARG0_SHIFT +
             etable_values op_rel_is_i32 i * Z.shiftl 1 OPCODE_ARG1_SHIFT))))))))))
      with

      (Z.shiftl ((etable_values op_rel_op_is_ne i  +
   (etable_values op_rel_op_is_gt i * (1 - etable_values op_rel_is_sign i) *
    3  +
    (etable_values op_rel_op_is_ge i * (1 - etable_values op_rel_is_sign i) *
      5  +
     (etable_values op_rel_op_is_lt i * (1 - etable_values op_rel_is_sign i) *
      7  +
      (etable_values op_rel_op_is_le i * (1 - etable_values op_rel_is_sign i) *
       9  +
       (etable_values op_rel_op_is_gt i * etable_values op_rel_is_sign i *
         2  +
        (etable_values op_rel_op_is_ge i * etable_values op_rel_is_sign i *
          4  +
         (etable_values op_rel_op_is_lt i * etable_values op_rel_is_sign i *
          6  +
          (etable_values op_rel_op_is_le i * etable_values op_rel_is_sign i *
           8))))))))))  OPCODE_ARG0_SHIFT +
           etable_values op_rel_is_i32 i * Z.shiftl 1 OPCODE_ARG1_SHIFT). 
    2: {
        intros.
        rewrite !Z.shiftl_mul_pow2 by (apply OPCODE_ARG0_SHIFT_nonneg).
        lia.
    }
    apply shift_arg1_64_lt_class_shift.
    {
      pose (OpRelModel.op_is_ne_bit i).
      pose (OpRelModel.op_is_gt_bit i).
      pose (OpRelModel.op_is_ge_bit i).
      pose (OpRelModel.op_is_lt_bit i).
      pose (OpRelModel.op_is_le_bit i).
      pose (OpRelModel.op_is_gt_bit i).
      pose (OpRelModel.op_is_ge_bit i).
      pose (OpRelModel.is_sign_bit i).
      lia.
    }
    rewrite (options_1 OPCODE_ARG1_SHIFT OPCODE_ARG1_SHIFT_nonneg).
    apply shift_arg1_lt_arg0.
    {
      pose (OpRelModel.is_i32_bit i). 
      lia.
    }
  - rewrite (options_1 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).
    apply shift_arg1_64_lt_class_shift.
    {
      pose (OpReturnModel.drop_common i).
      auto with size_lemmas.
    }
    rewrite (options_1 OPCODE_ARG1_SHIFT OPCODE_ARG1_SHIFT_nonneg).
    apply shift_arg1_lt_arg0.
    {
      pose (ETableModel.op_return_keep_cell_bit i). 
      lia.
    }
  - rewrite Z.mul_0_l, Z.add_0_l.
    rewrite (options_1 OPCODE_ARG1_SHIFT OPCODE_ARG1_SHIFT_nonneg).
    apply shift_arg1_lt_class_shift.
    pose (OpTestModel.is_i32_cell_bit i).
    lia.
  - rewrite (options_1 OPCODE_ARG1_SHIFT OPCODE_ARG1_SHIFT_nonneg).
    rewrite Z.add_comm.
    rewrite <- !Z.add_assoc.
    rewrite (options_2 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).
    apply shift_arg1_64_lt_class_shift.
    {
      pose (OpUnaryModel.is_clz_bit i).
      pose (OpUnaryModel.is_popcnt_bit i).
      lia.
    }
  - pose (OpUnaryModel.is_i32_bit i).
    apply  shift_arg1_lt_arg0.
    lia.
  -  rewrite (options_1 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).
     apply shift_arg1_64_lt_class_shift.
     {
       pose (OpLoadModel.is_i32_bit i).
       lia.
     }
     replace  ((etable_values op_load_is_eight_bytes i * 6 +
                 (etable_values op_load_is_four_bytes i * 4 +
                    (etable_values op_load_is_two_bytes i * 2 + (etable_values op_load_is_sign i + 1)))) *
                 Z.shiftl 1 OPCODE_ARG1_SHIFT)
       with (Z.shiftl (etable_values op_load_is_eight_bytes i * 6 +
                 (etable_values op_load_is_four_bytes i * 4 +
                    (etable_values op_load_is_two_bytes i * 2 + (etable_values op_load_is_sign i + 1)))) OPCODE_ARG1_SHIFT).
     2: {
       rewrite !(Z.shiftl_mul_pow2) by (apply OPCODE_ARG1_SHIFT_nonneg).
       lia.
     }
     apply  shift_arg1_64_lt_arg0. 
     {
       pose  (OpLoadModel.is_eight_bytes_bit i).
       pose  (OpLoadModel.is_four_bytes_bit i).
       pose  (OpLoadModel.is_two_bytes_bit i).
       pose  (OpLoadModel.is_sign_bit i).
       lia.
     }
     pose  (OpLoadModel.opcode_load_offset_common i).
     eauto with size_lemmas.
  -  rewrite (options_1 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).
     apply shift_arg1_64_lt_class_shift.
     {
       pose (OpStoreModel.is_i32_bit i).
       lia.
     }
     rewrite (options_1 OPCODE_ARG1_SHIFT OPCODE_ARG1_SHIFT_nonneg).
     apply  shift_arg1_64_lt_arg0. 
     {
       pose  (OpStoreModel.is_eight_bytes_bit i).
       pose  (OpStoreModel.is_four_bytes_bit i).
       pose  (OpStoreModel.is_two_bytes_bit i).
       lia.
     }
     pose  (OpStoreModel.opcode_store_offset_common i).
     eauto with size_lemmas.     
  -  rewrite (options_1 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).
     apply shift_arg1_64_lt_class_shift.
     {
       pose (OpBinBitModel.op_class_common i).
       eauto with size_lemmas.
     }
     rewrite (options_1 OPCODE_ARG1_SHIFT OPCODE_ARG1_SHIFT_nonneg).
     apply  shift_arg1_lt_arg0. 
     {
       pose (OpBinBitModel.is_i32_bit i).
       lia.
     }
  - pose (OpBrTableModel.targets_len_common i).
    auto with size_lemmas.
  - rewrite (options_1 OPCODE_ARG0_SHIFT OPCODE_ARG0_SHIFT_nonneg).
    apply shift_arg0_lt_class_shift.
    pose (OpCallIndirectModel.type_index_common i).
    auto with size_lemmas.
Qed.
