(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETable.
Require MTable.
Require IntegerFunctions.
Require BitTableModel.

(* Translation of the constrains in op_unary.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_unary.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::Unary], which is written (ops_cell Unary) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation operand_inv := op_unary_operand_inv.
Notation bits:= op_unary_bits.
Notation operand_is_zero := op_unary_operand_is_zero.
Notation is_ctz := op_unary_is_ctz.
Notation is_clz := op_unary_is_clz.
Notation is_popcnt := op_unary_is_popcnt.
Notation is_i32 := op_unary_is_i32.
Notation aux1 := op_unary_aux1.
Notation aux2 := op_unary_aux2.
Notation lookup_pow_modulus := pow_table_lookup_modulus_cell.
Notation lookup_pow_power := pow_table_lookup_power_cell.
Notation ctz_degree_helper := op_unary_ctz_degree_helper.
Notation memory_table_lookup_stack_read := op_unary_memory_table_lookup_stack_read.
Notation memory_table_lookup_stack_write := op_unary_memory_table_lookup_stack_write.

Notation popcnt_op_class := RTableModel.Popcnt_index.

Axiom operand_is_zero_bit : isbit operand_is_zero.
Axiom is_ctz_bit : isbit is_ctz.
Axiom is_clz_bit : isbit is_clz.
Axiom is_popcnt_bit : isbit is_popcnt.
Axiom is_i32_bit : isbit is_i32.

Axiom is64_aux1: is64 aux1.
Axiom is64_aux2: is64 aux2.

Axiom stack_read :
  alloc_memory_table_lookup_read_cell_with_value
    memory_table_lookup_stack_read
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => get is_i32)
    (fun get => get (ops_cell Unary)).
Notation operand := (memory_table_lookup_stack_read AMTLRC_value_cell).

Axiom stack_write :
  alloc_memory_table_lookup_write_cell_with_value
    memory_table_lookup_stack_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => get is_i32)
    (fun get => get (ops_cell Unary)).
Notation result := (memory_table_lookup_stack_write AMTLWC_value_cell).

(* "op_unary: selector" *)
Axiom op_unary_selector :
  gate etable
    (fun get =>
    (get (ops_cell Unary) 0) 
  * ((get is_ctz 0) + (get is_clz 0) + (get is_popcnt 0) - 1)
    ::nil).

(* "op_unary: zero cond" *)
Axiom op_unary_zero_cond :
  gate etable
    (fun get =>
      (get (ops_cell Unary) 0) * (get operand_is_zero 0) * (get operand 0)
    ::(get (ops_cell Unary) 0)
    * ((get operand 0) * (get operand_inv 0) - 1 + (get operand_is_zero 0))
    ::nil).

(* "op_unary: bits" *)
Axiom op_unary_bits_gate :
  gate etable
    (fun get =>
      (get (ops_cell Unary) 0) * ((get bits 0) - 64 + 32 * (get is_i32 0))
    ::nil).

(* "op_unary: clz" *)
Axiom op_unary_clz :
  gate etable
    (fun get =>
      let operand_is_not_zero := 1 - (get operand_is_zero 0) in
      (get (ops_cell Unary) 0) * (get is_clz 0) * (get operand_is_zero 0) 
    * ((get result 0) - (get bits 0))
    ::(get (ops_cell Unary) 0) * (get is_clz 0) * operand_is_not_zero 
    * ((get lookup_pow_modulus 0) + (get aux1 0) - (get operand 0))
    ::(get (ops_cell Unary) 0) * (get is_clz 0) * operand_is_not_zero 
    * ((get aux1 0) + (get aux2 0) + 1 - (get lookup_pow_modulus 0))
    ::(get (ops_cell Unary) 0) * (get is_clz 0) * operand_is_not_zero 
    * ((get lookup_pow_power 0) - ((get bits 0) - (get result 0) - 1 + 128))
    ::nil).

(* "op_unary: ctz" *)
Axiom op_unary_ctz :
  gate etable
    (fun get =>
      let operand_is_not_zero := 1 - (get operand_is_zero 0) in
      (get (ops_cell Unary) 0) * (get is_ctz 0) 
    * ((get ctz_degree_helper 0) - (get aux1 0) * (get lookup_pow_modulus 0) * 2)
    ::(get (ops_cell Unary) 0) * (get is_ctz 0) * (get operand_is_zero 0) 
    * ((get result 0) - (get bits 0))
    ::(get (ops_cell Unary) 0) * (get is_ctz 0) * operand_is_not_zero 
    * ((get ctz_degree_helper 0) + (get lookup_pow_modulus 0) - (get operand 0))
    ::(get (ops_cell Unary) 0) * (get is_ctz 0) 
    * ((get lookup_pow_power 0) - (get result 0 + 128))
    :: nil).

(* "op_unary: lookup popcnt" *)
Axiom op_unary_popcnt_lookup :
  gate etable
    (fun get =>
       (get (ops_cell Unary) 0) * (get is_popcnt 0) * (get (bit_table_lookup_cells ABTLC_op) 0     - popcnt_op_class)
    :: (get (ops_cell Unary) 0) * (get is_popcnt 0) * (get (bit_table_lookup_cells ABTLC_left) 0   - get operand 0)
    :: (get (ops_cell Unary) 0) * (get is_popcnt 0) * (get (bit_table_lookup_cells ABTLC_right) 0  - 0)
    :: (get (ops_cell Unary) 0) * (get is_popcnt 0) * (get (bit_table_lookup_cells ABTLC_result) 0 - get result 0)
    :: nil).
