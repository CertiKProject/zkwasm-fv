(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETableModel.
Require Import JTableModel.

(* Translation of the constrains in op_call.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_call.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::Call], which is written (ops_cell Call) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation index_cell := op_call_index.
Notation frame_table_lookup := jtable_lookup_cell.
Notation fid_cell := fid_cell.
Notation iid_cell := iid_cell.
Notation frame_id_cell := frame_id_cell.
(* Notation eid := eid_cell. *)

Axiom index_common : iscommon index_cell.

Axiom return_frame_table_lookup :
  gate etable
    (fun get =>
      (get (ops_cell Call) 0) *
       (get frame_table_lookup 0
       - (encode_frame_table_entry
            (get eid_cell 0)
            (get frame_id_cell 0)
            (get index_cell 0)
            (get fid_cell 0)
            (get iid_cell 0 + 1)))
           :: nil).
