(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.
Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import CommonModel.
Require Export ImageTableModel.

Open Scope Z_scope.
 
(* jtable/mod.rs *)

Definition JOPS_SEPARATE :Z  := 128.
Definition encode_jops return_instructions call_instructions :=
   (Z.lor (Z.shiftl return_instructions JOPS_SEPARATE) call_instructions) mod field_order.

Definition JtableOffsetEnable := 0.
Definition JtableOffsetRest   := 1.
Definition JtableOffsetEntry  := 2.
Definition JtableOffsetMax    := 3.

Inductive jtable_cols :=
| sel_col
| static_bit_col
| data_col.

(* jtable/expression.rs *)

Definition enable (get : jtable_cols -> Z -> Z) :=
  get data_col JtableOffsetEnable.

Definition rest (get : jtable_cols -> Z -> Z) :=
  get data_col JtableOffsetRest.

Definition next_rest (get : jtable_cols -> Z -> Z) :=
  get data_col (JtableOffsetRest+JtableOffsetMax).

Definition entry (get : jtable_cols -> Z -> Z) :=
  get data_col JtableOffsetEntry.

(* jtable/configure.rs *)

Parameter jtable_values : jtable_cols -> Z -> Z.
Parameter jtable_numRow : Z.
Axiom jtable_numRow_nonneg : 0 <= jtable_numRow.
Axiom jtable_numRow_upper_bound: jtable_numRow < 2 ^ JOPS_SEPARATE. 

Definition jtable := mkTable jtable_cols jtable_numRow jtable_values.

(* "enable is bit" *)
Axiom jtable_enable_is_bit :
  gate jtable
    (fun get =>
       (enable get) * (enable get - 1) * (get sel_col 0)
       :: nil).

(* "c3. jtable rest decrease" *)
Axiom c3 :
  gate jtable
    (fun get =>
     (rest get - next_rest get - (encode_jops 1 1) + (get static_bit_col 0))
     * (enable get)
     * (get sel_col 0) ::
     (rest get - next_rest get)
     * (enable get - 1)
     * (get sel_col 0)
         :: nil).
                         
(* "c5. jtable ends up" *)
Axiom c5 :
  gate jtable
    (fun get =>
       (1 - enable get)
       * (1 - (get static_bit_col 0))
       * (rest get)
       * (get sel_col 0)
    :: nil).

(* "c6. jtable entry is zero on disabled" *)
Axiom c6 :
  gate jtable
    (fun get =>
       (1 - enable get)
       * (entry get)
       * (get sel_col 0)
      :: nil).

(* The following axioms represent the Fixed columns
  assigned in  jtable/assign.rs,
  fn init(&self, ctx: &mut Context<'_, F>) -> Result<(), Error> 
*)

Definition STATIC_FRAME_ENTRY_NUMBER := 2.

Axiom sel_spec : forall i,
    jtable_values sel_col i =
      if (Z.eq_dec (i mod JtableOffsetMax) 0)
           then 1 else 0.

Axiom rest_jops_terminates :
  jtable_values data_col (jtable_numRow - JtableOffsetMax + JtableOffsetRest)  = 0.

Axiom numRow_parity : (jtable_numRow mod JtableOffsetMax) = 0.

Axiom ajtable_numRow_lower_bound:
    STATIC_FRAME_ENTRY_NUMBER * JtableOffsetMax < jtable_numRow.

Axiom enable_terminates :
    jtable_values data_col (jtable_numRow - JtableOffsetMax + JtableOffsetEnable) = 0.

(* Known because it is a fixed column *)
Axiom static_is_bit  : forall i,
  jtable_values static_bit_col i = 0 \/ jtable_values static_bit_col i = 1.

Axiom jtable_numRow_lower_bound:
    STATIC_FRAME_ENTRY_NUMBER < jtable_numRow / JtableOffsetMax.

Definition entry_id (entry : Z) :=
  let IID_SHIFT := 0 in
  let FID_SHIFT := IID_SHIFT + COMMON_RANGE_OFFSET in
  let CALLEE_FID := FID_SHIFT + COMMON_RANGE_OFFSET in
  let LAST_JUMP_FRAME_ID_SHIFT := CALLEE_FID + COMMON_RANGE_OFFSET in
  let FRAME_ID_SHIFT := LAST_JUMP_FRAME_ID_SHIFT + COMMON_RANGE_OFFSET in  
  (Z.shiftr entry FRAME_ID_SHIFT).

Definition next_entry_id (entry : Z) :=
  let IID_SHIFT := 0 in
  let FID_SHIFT := IID_SHIFT + COMMON_RANGE_OFFSET in
  let CALLEE_FID := FID_SHIFT + COMMON_RANGE_OFFSET in
  let LAST_JUMP_FRAME_ID_SHIFT := CALLEE_FID + COMMON_RANGE_OFFSET in
  let FRAME_ID_SHIFT := LAST_JUMP_FRAME_ID_SHIFT + COMMON_RANGE_OFFSET in
  Z.land (Z.shiftr entry LAST_JUMP_FRAME_ID_SHIFT) (Z.ones COMMON_RANGE_OFFSET).

(* Represents configure_in_table  (jtable/configure.rs line 81) *)
Definition in_jtable (entry : Z) :=
  exists i,
      0 <= i < jtable_numRow
      /\ (value JTableModel.jtable JTableModel.data_col (i+JTableModel.JtableOffsetEntry)) * (value JTableModel.jtable JTableModel.sel_col i) = entry.

(**** Assumptions. These axioms do not directly correspond to lines of circuit, but rather about other parts of the system. *)

(* Assumption about the field order size versus the k value and entry size.
   Used to show that if the numbers are 0 <= x < common, then 
   encode_jops_entry is injective.  *)
Axiom common_is_COMMON_RANGE_OFFSET : common = 2 ^ COMMON_RANGE_OFFSET.
Axiom encode_frame_table_entry_order : 2 ^ (5 * COMMON_RANGE_OFFSET) < field_order.
Axiom encode_jops_order : 2 ^ (2 * JOPS_SEPARATE) <= field_order.

(* These four axioms are about the two "static" entries added to the JTable, which are ultimately created by Wasmi.
   From the zkWasm fixed assignments (jtable/assign.rs), we know there are exactly two entries in the first
   two rows. Further, for the JTable wellformedness property, we need to know that the id and next_id in them are zero
   (which is true based on how Wasmi generates them). *)
Axiom static_entries_first : forall i,
    jtable_values static_bit_col (JtableOffsetMax * i) = 1 <-> (i < STATIC_FRAME_ENTRY_NUMBER).

Axiom static_entries_id_zero : forall i,
    jtable_values static_bit_col (JtableOffsetMax * i) = 1 -> 
    entry_id (jtable_values data_col (JtableOffsetMax * i + JtableOffsetEntry)) = 0.

Axiom static_entries_next_id_zero : forall i,
    jtable_values static_bit_col (JtableOffsetMax * i) = 1 ->
    next_entry_id (jtable_values data_col (JtableOffsetMax * i + JtableOffsetEntry)) = 0.

Axiom frame_id_is_positive: forall i,
    jtable_values data_col (JtableOffsetMax * i + JtableOffsetEnable) = 1 -> 
    jtable_values static_bit_col (JtableOffsetMax * i) = 0 ->
    entry_id (jtable_values data_col (JtableOffsetMax * i + JtableOffsetEntry)) > 0.
