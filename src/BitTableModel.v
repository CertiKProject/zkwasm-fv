(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Wasm.numerics.

Require Import Shared.
Require Import IntegerFunctions.
Require Import RTableModel.
Require Import RTable.

(* The bit_table . *)

Inductive bit_table_cols :=
  | block_sel
  | u32_sel
  | lookup_sel
  | op
  | helper
  | val_l
  | val_r
  | val_res.

Parameter bit_table_values : bit_table_cols -> Z -> Z.
Parameter bit_table_numRows : Z.

Definition bit_table := mkTable bit_table_cols bit_table_numRows bit_table_values.

Section gate_helpers.

  Variable get : bit_table_cols -> Z -> Z.

  Definition is_popcnt := get helper 0.
  Definition is_bit := 1 - is_popcnt.

  Fixpoint reduce_sum xs :=
   match xs with
   | nil => 0
   | x::xs => x+reduce_sum xs
   end.

  Definition compose_u32_helper col :=
   reduce_sum (List.map (fun x =>
                     if (Z.eqb x 0)
                       then (get col 1)
                       else (get col (x+1)) * (Z.shiftl 1 (8*x)))
                    (0::1::2::3::nil)).

  Definition acc_u32_helper col :=
    reduce_sum (List.map (fun x => get col (1+x)) (0::1::2::3::nil)).

  Definition compose_u32 col :=
      (get u32_sel 0) * (compose_u32_helper col - (get col 0)).

  Definition compose_u32_if_bit col :=
    compose_u32 col * is_bit.

  Definition acc_u32_if_popcnt col :=
    (get u32_sel 0) 
    * (acc_u32_helper col - (get col 0))
    * is_popcnt.

  Definition compose_u64 col :=
    (get block_sel 0) 
    * ((get col (-1))
       - (get col 0)
       - ((get col 5) * (Z.shiftl 1 32))).

  Definition compose_u64_if_bit col :=
     compose_u64 col * is_bit.

  Definition acc_u64_if_popcnt col :=
    (get block_sel 0)
    * is_popcnt
    * ((get col (-1)) - (get col 0) - (get col 5)).

End gate_helpers.

Axiom bit_table_configure_in_op_table :
  forall i enable bop left right res,
    bit_table_values lookup_sel i = enable ->
    bit_table_values op i = bop ->
    bit_table_values val_l i = left ->
    bit_table_values val_r i = right ->
    bit_table_values val_res i = res ->
    in_op_table (enable*bop) (enable*left) (enable*right) (enable*res).

Axiom bit_table_gate_1 :
  gate bit_table
  (fun get =>
   ((get u32_sel 0) + (get lookup_sel 0))
   * ((get op (-1)) - (get op 0))
 ::
   (get u32_sel 0)
   * (get helper 0)
   * ((get op 0) - Popcnt_index)
::
   (get u32_sel 0)
   * ((get helper 0) - 1)
   * ((get op 0) - BitOp_And)
   * ((get op 0) - BitOp_Or)
   * ((get op 0) - BitOp_Xor)
::
   (get u32_sel 0)
   * (get helper 0)
   * ((get helper 0) - 1)
:: nil).

Axiom bit_table_gate_2 :
  gate bit_table
    (fun get =>
      compose_u32 get val_l ::
      compose_u32 get val_r ::
      compose_u32_if_bit get val_res ::
      acc_u32_if_popcnt get val_res :: nil).

Axiom bit_table_gate_3 :
  gate bit_table
    (fun get =>
      compose_u64 get val_l ::
      compose_u64 get val_r ::
      compose_u64_if_bit get val_res ::
      acc_u64_if_popcnt get val_res :: nil).

(* The following axioms represent the Fixed columns
  assigned in  bit_table/assign.rs,

  impl<F: FieldExt> BitTableChip<F> {
   fn init(&self, ctx: &mut Context<'_, F>) -> Result<(), Error> *)

Parameter bit_table_start : Z.
Definition STEP_SIZE := 11.
Definition BLOCK_SEL_OFFSET := 1.
Definition U32_OFFSET := 1::6::nil.
Definition U8_OFFSET := 2::3::4::5::7::8::9::10::nil.

Axiom block_sel_spec : forall i,
    bit_table_values block_sel i =
      if (Z.eq_dec (Zmod (i-bit_table_start) STEP_SIZE) BLOCK_SEL_OFFSET)
           then 1 else 0.

Axiom u32_sel_spec : forall i,
    bit_table_values u32_sel i =
      if (List.In_dec Z.eq_dec (Zmod (i-bit_table_start) STEP_SIZE) U32_OFFSET)
           then 1 else 0.

Axiom lookup_sel_spec : forall i,
    bit_table_values lookup_sel i =
      if (List.In_dec Z.eq_dec (Zmod (i-bit_table_start) STEP_SIZE) U8_OFFSET)
           then 1 else 0.
