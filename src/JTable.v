(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

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



Opaque Z.mul Z.add.

Lemma rest_jops_change_enabled : forall i,
  0 <= i ->
  ajtable_values enabled_cell i = 1 ->
  ajtable_values rest_cell i
  = ajtable_values rest_cell (i+1)
     + (encode_jops 1 1) - (ajtable_values static_bit_cell i).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma rest_jops_change_disabled : forall i,
  0 <= i ->
  ajtable_values enabled_cell i = 0 ->
  ajtable_values rest_cell i = ajtable_values rest_cell (i+1).
Admitted. (* Proof omitted for release, present in original source. *)

(**
 * Entry ID
 *)

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


  Lemma gather_jops_nonnegative : forall i j,
    0 <= gather_jops i j.
Admitted. (* Proof omitted for release, present in original source. *)

  Lemma gather_jops_append : forall i j k,
      i <= j <= k ->
      gather_jops i k = (gather_jops i j) + gather_jops j k.
Admitted. (* Proof omitted for release, present in original source. *)

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
Admitted. (* Proof omitted for release, present in original source. *)

  (**
   * Rest and Gather rest
   *)
  
  (**
   * Call of and Gather call
   *)

  (* The right side of the jops column is meant to count call instructions,
     and we extract it with the Z.land. 
     In order to show that the counter doesn't overflow, we need to know that the number of
     rows are less than the common range. *)

  (* Number of call jops at a particular id. *)
  Definition jops_at eid  := 
    gather_jops eid (eid+1) 0 ajtable_numRow.

  (* Number of call jops that happen in a particular range of ids. *)
  Definition cum_jops from to :=
        gather_jops from to 0 ajtable_numRow.

  (* This lemma shows cum_jops is correctly defined. *)
  Theorem cum_jops_cons : forall eid to,
      0 <= eid < to ->
      cum_jops eid to =
        cum_jops (eid + 1) to
        + jops_at eid.
Admitted. (* Proof omitted for release, present in original source. *)

  (* This theorem proves that the rest_jops column is correct. *)
  Theorem rest_jops_correct : forall from to,
      cum_jops from to <= Z.land (ajtable_values rest_cell 0) (Z.ones JOPS_SEPARATE).
Admitted. (* Proof omitted for release, present in original source. *)

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
Admitted. (* Proof omitted for release, present in original source. *)

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
Admitted. (* Proof omitted for release, present in original source. *)

  Theorem jops_at_nonnegative : forall frame_id,
      jops_at frame_id >= 0.
Admitted. (* Proof omitted for release, present in original source. *)

  Theorem cum_jops_nonnegative  : forall from to,
      0 <= cum_jops from to.
Admitted. (* Proof omitted for release, present in original source. *)

  Theorem cum_jops_empty_range : forall i,
      cum_jops i i = 0.
Admitted. (* Proof omitted for release, present in original source. *)
  
End gather_jops.

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
Admitted. (* Proof omitted for release, present in original source. *)

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
Admitted. (* Proof omitted for release, present in original source. *)

Lemma id_zero_entries : forall {id next_id cfid fid iid},
    in_jtable (encode_frame_table_entry id next_id cfid fid iid) ->
    0 <= id < common ->
    0 <= next_id < common ->
    0 <= cfid < common ->
    0 <= fid < common ->
    0 <= iid < common ->
    id = 0 ->
    next_id = 0.
Admitted. (* Proof omitted for release, present in original source. *)
