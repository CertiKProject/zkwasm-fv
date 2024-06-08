(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETableModel.
Require MTable.
Require Import JTableModel.

(* Translation of the constrains in op_return.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_return.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::BinBit], which is written (ops_cell BinBit) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation keep := op_return_keep.
Notation drop := op_return_drop.
Notation is_i32 := op_return_is_i32.
Notation value_u64_cell := op_return_value_u64_cell.

Notation frame_table_lookup := jtable_lookup_cell.
Notation fid_cell := fid_cell.
Notation iid_cell := iid_cell.
Notation frame_id_cell := frame_id_cell.
(* Notation eid := eid_cell. *) (* Use the longer names in the constraint *)
(* Notation sp := sp_cell. *) 
Notation memory_table_lookup_stack_read := op_return_memory_table_lookup_stack_read.
Notation memory_table_lookup_stack_write := op_return_memory_table_lookup_stack_write.

(* Axiom op_return_keep_cell_bit is in EtableModel.v *)
Axiom drop_common : iscommon drop.
Axiom is_i32_bit : isbit is_i32.
Axiom value_64 : is64 value_u64_cell.

Axiom stack_read :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => get is_i32)
    (fun get => get value_u64_cell)
    (fun get => get keep * get (ops_cell Return)).

Axiom stack_write:
  alloc_memory_table_lookup_write_cell
    memory_table_lookup_stack_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + get drop + 1)
    (fun get => get is_i32)
    (fun get => get value_u64_cell)
    (fun get => get keep * get (ops_cell Return)).

Axiom return_frame_table_lookup :
  gate etable
    (fun get =>
       get frame_table_lookup 0
       - (encode_frame_table_entry
            (get frame_id_cell 0)
            (get frame_id_cell 1)
            (get fid_cell 0)
            (get fid_cell 1)
            (get iid_cell 1))
           :: nil).
