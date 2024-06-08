(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

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
Admitted. (* Proof omitted for release, present in original source. *)

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
Admitted. (* Proof omitted for release, present in original source. *)

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
Admitted. (* Proof omitted for release, present in original source. *)
