(* Copyright (C) CertiK 2024-2026 *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import JTableModel JTable.
Require Import ETableModel.

Require Import OpCallModel.

(* Proofs about op_call.rs, op_call_indirect.rs, and op_return.rs
   that are needed as a precondition for the jtable wellformedness
   lemmas in ETable.v *)

Require Import Wasm.numerics.
Require Import Lia.
Require Import MTable.


Lemma Call_jtable_entry : forall i,
    0 <= i ->
    etable_values enabled_cell i = 1 ->
    etable_values (ops_cell Call) i = 1 ->
    in_jtable (encode_frame_table_entry (etable_values eid_cell i)
                                        (etable_values frame_id_cell i)
                                        (etable_values op_call_index i)
                                        (etable_values fid_cell i)
                                        (etable_values iid_cell i + 1)).
Proof.
  intros i Hrange Henabled Hclass.
  replace (encode_frame_table_entry
                  (etable_values eid_cell i)
                  (etable_values frame_id_cell i)
                  (etable_values index_cell i)
                  (etable_values fid_cell i) (etable_values iid_cell i + 1))
        with (etable_values frame_table_lookup i).
  2: {
        destruct (return_frame_table_lookup i Hrange) as [Hgate _].
        replace (i+0) with i in * by lia.
        simpl in Hgate.
        lia.
      }
      apply c8c; auto.
Qed.

Require Import OpCallIndirectModel.

Lemma CallIndirect_jtable_entry : forall i,
    0 <= i ->
    etable_values enabled_cell i = 1 ->
    etable_values (ops_cell CallIndirect) i = 1 ->
    in_jtable (encode_frame_table_entry
                 (etable_values eid_cell i)
                 (etable_values frame_id_cell i)
                 (etable_values op_call_indirect_func_index i)
                 (etable_values fid_cell i) (etable_values iid_cell i + 1)).
Proof.
  intros i Hrange Henabled Hclass.
  replace  (encode_frame_table_entry
                 (etable_values eid_cell i)
                 (etable_values frame_id_cell i)
                 (etable_values op_call_indirect_func_index i)
                 (etable_values fid_cell i) (etable_values iid_cell i + 1))
    with (etable_values frame_table_lookup i).
  2: {
        destruct (return_frame_table_lookup i Hrange) as [Hgate _].
        replace (i+0) with i in * by lia.
        simpl in Hgate.
        lia.
  }
  apply c8c; auto.
Qed.

Require Import OpReturnModel.

Lemma Return_jtable_entry : forall i,
    0 <= i ->
    etable_values enabled_cell i = 1 ->
    etable_values (ops_cell Return) i = 1 ->
    in_jtable  (encode_frame_table_entry
                  (etable_values frame_id_cell i)
                  (etable_values frame_id_cell (i+1))
                  (etable_values fid_cell i)
                  (etable_values fid_cell (i+1))
                  (etable_values iid_cell (i+1))).
Proof.
  intros i Hrange Henabled Hclass.
  replace  (encode_frame_table_entry
                  (etable_values frame_id_cell i)
                  (etable_values frame_id_cell (i+1))
                  (etable_values fid_cell i)
                  (etable_values fid_cell (i+1))
                  (etable_values iid_cell (i+1)))
    with (etable_values frame_table_lookup i).
  2: {
        destruct (return_frame_table_lookup i Hrange) as [Hgate _].
        replace (i+0) with i in * by lia.
        simpl in Hgate.
        lia.
  }
  apply c8c; auto.
Qed.
