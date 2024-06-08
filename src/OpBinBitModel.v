(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETable.
Require MTable.

(* Translation of the constrains in op_bin_bit.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_bin_bit.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::BinBit], which is written (ops_cell BinBit) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation is_i32 := op_bin_bit_is_i32.
Notation op_class := op_bin_bit_op_class.
Notation memory_table_lookup_stack_read_lhs := op_bin_bit_memory_table_lookup_stack_read_lhs.
Notation memory_table_lookup_stack_read_rhs := op_bin_bit_memory_table_lookup_stack_read_rhs.
Notation memory_table_lookup_stack_write := op_bin_bit_memory_table_lookup_stack_write.

Axiom is_i32_bit : isbit is_i32.
Axiom op_class_common : iscommon op_class.

Axiom stack_read_rhs :
  alloc_memory_table_lookup_read_cell_with_value
    memory_table_lookup_stack_read_rhs
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => get is_i32)
    (fun get => get (ops_cell BinBit)).
Notation rhs := (memory_table_lookup_stack_read_rhs AMTLRC_value_cell).

Axiom stack_read_lhs :
  alloc_memory_table_lookup_read_cell_with_value
    memory_table_lookup_stack_read_lhs
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    (fun get => get is_i32)
    (fun get => get (ops_cell BinBit)).
Notation lhs := (memory_table_lookup_stack_read_lhs AMTLRC_value_cell).

Axiom stack_write :
  alloc_memory_table_lookup_write_cell_with_value
    memory_table_lookup_stack_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    (fun get => get is_i32)
    (fun get => get (ops_cell BinBit)).
Notation res := (memory_table_lookup_stack_write AMTLWC_value_cell).

(* "op_bin_bit: lookup" *)
Axiom op_bin_bit_lookup :
  gate etable
    (fun get =>
       (get (ops_cell BinBit) 0) * (get (bit_table_lookup_cells ABTLC_op) 0     - get op_class 0)
    :: (get (ops_cell BinBit) 0) * (get (bit_table_lookup_cells ABTLC_left) 0   - get lhs 0)
    :: (get (ops_cell BinBit) 0) * (get (bit_table_lookup_cells ABTLC_right) 0  - get rhs 0)
    :: (get (ops_cell BinBit) 0) * (get (bit_table_lookup_cells ABTLC_result) 0 - get res 0)
    :: nil).
