(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETable.
Require MTable.
Require MTableModel.

(* Translation of the constraints in op_global_set.rs 
   See comment at the beginning of OpBinBit.v for details about our translation strategy. *)

Notation idx_cell    :=   op_global_set_idx_cell.
Notation is_i32_cell := op_global_set_is_i32_cell.
Notation value_u64_cell  := op_global_set_value_u64_cell.
Notation memory_table_lookup_stack_read :=  op_global_set_memory_table_lookup_stack_read.
Notation memory_table_lookup_global_write :=  op_global_set_memory_table_lookup_global_write.

Axiom idx_common : iscommon idx_cell.
Axiom is_i32_bit : isbit is_i32_cell.
Axiom value_64 : is64 value_u64_cell.  (*Or possibly change this to constrain the u16 cells instead.*)

Axiom stack_read :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => get is_i32_cell)
    (fun get => get (value_u64_cell))
    (fun get => get (ops_cell GlobalSet)).
    
Axiom global_write :
  alloc_memory_table_lookup_write_cell
    memory_table_lookup_global_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Global)
    (fun get => get idx_cell)
    (fun get => get is_i32_cell)
    (fun get => get (value_u64_cell))
    (fun get => get (ops_cell GlobalSet)).
