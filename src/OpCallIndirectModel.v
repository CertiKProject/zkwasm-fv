(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETableModel.
Require Import JTableModel.

(* Translation of the constrains in op_call_indirect.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_call_indirect.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::CallIndirect], which is written (ops_cell CallIndirect) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation type_index := op_call_indirect_type_index.
Notation table_index := op_call_indirect_table_index.
Notation offset := op_call_indirect_offset.
Notation func_index := op_call_indirect_func_index.
Notation memory_table_lookup_stack_read := op_call_indirect_memory_table_lookup_stack_read.
Notation elem_lookup := brtable_lookup_cell.
Notation frame_table_lookup := jtable_lookup_cell.

Axiom type_index_common : iscommon type_index.
Axiom table_index_common : iscommon table_index.
Axiom offset_common : iscommon offset.
Axiom func_index_common : iscommon func_index.

Axiom stack_read :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => 1)
    (fun get => get offset)
    (fun get => get (ops_cell CallIndirect)).

Axiom table_index_gate :
  gate etable
    (fun get =>
      (get (ops_cell CallIndirect) 0) * (get table_index 0)
    ::nil).

Axiom op_call_indirect_elem_table_lookup :
  gate etable
    (fun get =>
      (get (ops_cell CallIndirect) 0) *
      (get elem_lookup 0 - 
      encode_elem_entry 
        (get table_index 0)
        (get type_index 0)
        (get offset 0)
        (get func_index 0))
    ::nil).

Axiom return_frame_table_lookup :
  gate etable
    (fun get =>
      (get (ops_cell CallIndirect) 0) *
       (get frame_table_lookup 0
       - (encode_frame_table_entry
            (get eid_cell 0)
            (get frame_id_cell 0)
            (get func_index 0)
            (get fid_cell 0)
            (get iid_cell 0 + 1)))
           :: nil).
