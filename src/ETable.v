(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import Wasm.numerics.
Require        Wasm.datatypes.
Require Import Lia.

Require MTableModel MTable JTableModel JTable.

Require Export ETableModel.

(* Doesn't have to be a tight bound, it's used to prove rest_mops
    doesn't overflow. *)

(***** Definitions/lemmas about counting mops. *)

Definition instruction_mops i :=
  if (etable_values enabled_cell i =? 1) 
      then config_mops (opcode_config (class_of_row i) i)
      else 0. 

Fixpoint instructions_mops' i n :=
  match n with
  | O => 0
  | S n' =>
      instruction_mops i + instructions_mops' (i+1) n'
  end.

(* The sum of all the intended mops of the instructions in rows `i`-`etable_numRow`.   *)
Definition instructions_mops (i : Z) : Z :=
  instructions_mops' i (Z.to_nat (etable_numRow - i)).

(* In most cases, rest_mops[i] = instructions_mops(i).
   The inequality would happen if the final row of the etable had enabled=1,
   in which case the rest_mops_change gate for the final row would not apply
   and the mops for that instruction would not be counted. *)
Lemma rest_mops_correct : forall i,
    0 <= i <= etable_numRow ->
    etable_values rest_mops_cell i <= instructions_mops i.
Admitted. (* Proof omitted for release, present in original source. *)

Definition opcode_mops_correct (c : OpcodeClass) i :=
    etable_values (ops_cell c) i = 1 ->
      MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack
    + MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap
    + MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Global
    >= config_mops (opcode_config c i).

Lemma enabled_seq_mono : forall n,
    etable_values enabled_cell (Z.of_nat n) = 1 ->
    forall m,  (m < n)%nat ->
               etable_values enabled_cell (Z.of_nat m) = 1.
Admitted. (* Proof omitted for release, present in original source. *)

(* the maximum eid in an enabled row between i and i+n *)
Fixpoint max_eid' i n :=
  match n with
  | O => 0
  | S n => if (etable_values enabled_cell i =? 1)
           then Z.max (etable_values eid_cell i) (max_eid' (i+1) n)
           else 0
  end.

(* The maximum eid in an enabled row between 0 and etable_numRom. *)
Definition max_eid := max_eid' 0 (Z.to_nat (etable_numRow+1)).

Definition mops_at_correct i :=
    MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack
  + MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap
  + MTable.mops_at (etable_values eid_cell i) MTableModel.LocationType_Global
  = config_mops (opcode_config (class_of_row i) i).

Section mops_correct.
  Hypothesis all_opcode_mops_correct : forall c i,
      0 <= i ->
      etable_values enabled_cell i = 1 ->
      opcode_mops_correct c i.

  Theorem mops_correct : forall i,
      0 <= i < etable_numRow ->
      i+1 < etable_numRow -> 
      etable_values enabled_cell i = 1 ->
      mops_at_correct i.
Admitted. (* Proof omitted for release, present in original source. *)
End mops_correct.

Definition decode_call_jops (x : Z) : Z :=
  Z.land x ((Z.ones JTableModel.JOPS_SEPARATE)).


Definition opcode_jops_correct (c : OpcodeClass) i :=
    0 <= i ->
    etable_values enabled_cell i = 1 ->
    etable_values (ops_cell c) i = 1 ->
      JTable.jops_at (etable_values eid_cell i)
    >=  decode_call_jops (config_jops (opcode_config c i)).

Definition jops_at_correct i :=
    JTable.jops_at (etable_values eid_cell i)
  = decode_call_jops (config_jops (opcode_config (class_of_row i) i)).

Definition instruction_jops i :=
  if etable_values enabled_cell i =? 1
  then decode_call_jops (config_jops (opcode_config (class_of_row i) i))
  else 0.

Fixpoint instructions_jops' i n {struct n} :=
  match n with
  | O => 0
  | S n' =>
      instruction_jops i + instructions_jops' (i+1) n'
  end.


(* The sum of all the intended jops of the instructions in rows `i`-`etable_numRow`.   *)
Definition instructions_jops (i : Z) : Z :=
  instructions_jops' i (Z.to_nat (etable_numRow - i)).

Lemma rest_jops_correct : forall i,
    0 <= i <= etable_numRow ->
    decode_call_jops (etable_values rest_jops_cell i) <= instructions_jops i.
Admitted. (* Proof omitted for release, present in original source. *)

Section jops_correct.
  Hypothesis all_opcode_jops_correct : forall c i, opcode_jops_correct c i.

  Theorem jops_correct : forall i,
      0 <= i < etable_numRow ->
      i+1 < etable_numRow -> 
      etable_values enabled_cell i = 1 ->
      jops_at_correct i.
Admitted. (* Proof omitted for release, present in original source. *)
End jops_correct.

Import JTableModel.


Require OpCallModel.
Require OpCallIndirectModel.
Require CallReturnHelper.

Section jops_at_bounded.

Theorem jtable_wellformedness : forall n,
    (Z.of_nat n) + 1 < etable_numRow ->
    etable_values enabled_cell (Z.of_nat n) = 1 ->    
    (0 <= (etable_values frame_id_cell (Z.of_nat n))
     /\ etable_values frame_id_cell (Z.of_nat n) <= etable_values eid_cell (Z.of_nat n))
     /\ (forall frame_id last_frame_id callee_fid fid iid,
            0 <= frame_id < etable_values eid_cell (Z.of_nat n) ->
            JTableModel.in_jtable (encode_frame_table_entry frame_id last_frame_id callee_fid fid iid) ->
            0 <= last_frame_id < common ->
            0 <= callee_fid < common ->
            0 <= fid < common ->
            0 <= iid < common ->
          0 <= last_frame_id /\ last_frame_id <= frame_id).
Admitted. (* Proof omitted for release, present in original source. *)

Corollary jops_at_bounded : forall i,
      0 <= i < etable_numRow ->
      i+1 < etable_numRow -> 
      etable_values enabled_cell i = 1 ->
      etable_values frame_id_cell i > 0 ->
      JTable.jops_at (etable_values frame_id_cell i) <= 1.
Admitted. (* Proof omitted for release, present in original source. *)

End jops_at_bounded.

Lemma eid_nonzero : forall i,
 0 <= i ->
 etable_values enabled_cell i = 1 ->
 etable_values eid_cell i > 0.
Admitted. (* Proof omitted for release, present in original source. *)
