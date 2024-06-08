(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Wasm.numerics.

Require Import Shared.
Require Import ImageTableModel.
Require Import ETable.
Require MTable.
Require MTableModel.

(* Translation of the constrains in op_conversion.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_conversion.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::Conversion], which is written (ops_cell Conversion) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Notation value_u64_cell := op_conversion_value_u64_cell.
Notation value_u16_cells_le_0 := op_conversion_value_u16_cells_le_0.
Notation value_u16_cells_le_1 := op_conversion_value_u16_cells_le_1.
Notation value_u16_cells_le_2 := op_conversion_value_u16_cells_le_2.
Notation value_u16_cells_le_3 := op_conversion_value_u16_cells_le_3.
Notation value_is_i8 := op_conversion_value_is_i8.
Notation value_is_i16 := op_conversion_value_is_i16.
Notation value_is_i32 := op_conversion_value_is_i32.
Notation value_is_i64 := op_conversion_value_is_i64.
Notation value_type_is_i32 := op_conversion_value_type_is_i32.
Notation res_is_i32 := op_conversion_res_is_i32.
Notation res_is_i64 := op_conversion_res_is_i64.
Notation sign_op := op_conversion_sign_op.
Notation is_i32_wrap_i64 := op_conversion_is_i32_wrap_i64.
Notation flag_bit := op_conversion_flag_bit.
Notation shift := op_conversion_shift.
Notation padding := op_conversion_padding.
Notation d := op_conversion_d.
Notation rem := op_conversion_rem.
Notation rem_helper := op_conversion_rem_helper.
Notation modulus := op_conversion_modulus.
Notation memory_table_lookup_stack_read := op_conversion_memory_table_lookup_stack_read.
Notation memory_table_lookup_stack_write := op_conversion_memory_table_lookup_stack_write.

Axiom stack_read :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => get value_type_is_i32)
    (fun get => get value_u64_cell)
    (fun get => get (ops_cell Conversion)).

Axiom stack_write :
  alloc_memory_table_lookup_write_cell_with_value
    memory_table_lookup_stack_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => get res_is_i32)
    (fun get => get (ops_cell Conversion)).
Notation res := (memory_table_lookup_stack_write AMTLWC_value_cell).

Axiom value_is_i8_bit : isbit value_is_i8.
Axiom value_is_i16_bit : isbit value_is_i16.
Axiom value_is_i32_bit : isbit value_is_i32.
Axiom value_is_i64_bit : isbit value_is_i64.
Axiom value_type_is_i32_bit : isbit value_type_is_i32.
Axiom res_is_i32_bit : isbit res_is_i32.
Axiom res_is_i64_bit : isbit res_is_i64.
Axiom sign_op_bit : isbit sign_op.
Axiom is_i32_wrap_i64_bit : isbit is_i32_wrap_i64.
Axiom flag_bit_bit : isbit flag_bit.

Axiom value_U16_cells : 
    is16 value_u16_cells_le_0 /\
    is16 value_u16_cells_le_1 /\
    is16 value_u16_cells_le_2 /\
    is16 value_u16_cells_le_3.

Axiom value_U64 : is64_from16
    value_u64_cell
    value_u16_cells_le_0
    value_u16_cells_le_1
    value_u16_cells_le_2
    value_u16_cells_le_3.

Axiom d_U64 : is64 d.
Axiom rem_U64 : is64 rem.
Axiom rem_helper_U64 : is64 rem_helper.

Axiom op_conversion_i32_wrap_i64 :
  gate etable
    (fun get =>
    (get (ops_cell Conversion) 0) * (get is_i32_wrap_i64 0)
  * ((get value_is_i64 0) + (get res_is_i32 0) - 2)
  ::(get (ops_cell Conversion) 0) * (get is_i32_wrap_i64 0)
  * ((get value_u16_cells_le_1 0) * 2^16 + (get value_u16_cells_le_0 0) - (get res 0))
    ::nil).

Axiom op_conversion_helper :
  gate etable
    (fun get =>
    (get (ops_cell Conversion) 0)
  * (get shift 0 - ((get value_is_i8 0) * 2^7 + (get value_is_i16 0) 
  * 2^15 + (get value_is_i32 0 + get value_is_i64 0) * 2^31))
  ::(get (ops_cell Conversion) 0)
  * (get padding 0 - ((get value_is_i8 0) * 0xFFFFFF00 (* u32::MAX << 8 *)
  + (get value_is_i16 0) * 0xFFFF0000 (* u32::MAX << 16 *)
  + (get res_is_i64 0) * 0xFFFFFFFF00000000)) (* u64::MAX << 32 *)
  ::(get (ops_cell Conversion) 0)
  * (get modulus 0 - (get shift 0 * 2))
  ::nil).

Axiom op_conversion_split_operand :
  gate etable
    (fun get =>
    (get (ops_cell Conversion) 0) 
  * (get value_u64_cell 0 - (get d 0) * (get modulus 0)
  - (get flag_bit 0) * (get shift 0) - (get rem 0))
  ::(get (ops_cell Conversion) 0)
  * (get rem 0 + 1 + get rem_helper 0 - get shift 0)
  :: nil).

Axiom op_conversion_sign_extension :
  gate etable
    (fun get =>
    (get (ops_cell Conversion) 0) 
  * (get flag_bit 0 * get padding 0 * get sign_op 0
  + get flag_bit 0 * get shift 0 + get rem 0
  - get res 0)
  :: nil).

Axiom allowed_opcodes_val : forall j fid iid sign val_type_is_i32 val_is_i8 val_is_i16 val_is_i32 val_is_i64 res_is_i32 res_is_i64,
  image_table_values col j = 
  encode_instruction_table_entry fid iid 
    (Z.shiftl (OpcodeClass_u64 Conversion) OPCODE_CLASS_SHIFT
    + encode_conversion sign val_type_is_i32 val_is_i8 val_is_i16 val_is_i32 val_is_i64 res_is_i32 res_is_i64) ->
  image_table_values col j =
  encode_instruction_table_entry fid iid
    (Z.shiftl (OpcodeClass_u64 Conversion) OPCODE_CLASS_SHIFT
    + encode_conversion sign val_type_is_i32 1 0 0 0 res_is_i32 res_is_i64) \/
  image_table_values col j =
  encode_instruction_table_entry fid iid
    (Z.shiftl (OpcodeClass_u64 Conversion) OPCODE_CLASS_SHIFT
    + encode_conversion sign val_type_is_i32 0 1 0 0 res_is_i32 res_is_i64) \/
  image_table_values col j =
  encode_instruction_table_entry fid iid
    (Z.shiftl (OpcodeClass_u64 Conversion) OPCODE_CLASS_SHIFT
    + encode_conversion sign val_type_is_i32 0 0 1 0 res_is_i32 res_is_i64) \/
  image_table_values col j =
  encode_instruction_table_entry fid iid
    (Z.shiftl (OpcodeClass_u64 Conversion) OPCODE_CLASS_SHIFT
    + encode_conversion sign val_type_is_i32 0 0 0 1 res_is_i32 res_is_i64).

Axiom allowed_opcodes_res : forall j fid iid sign val_type_is_i32 val_is_i8 val_is_i16 val_is_i32 val_is_i64 res_is_i32 res_is_i64,
  image_table_values col j = 
  encode_instruction_table_entry fid iid 
    (Z.shiftl (OpcodeClass_u64 Conversion) OPCODE_CLASS_SHIFT
    + encode_conversion sign val_type_is_i32 val_is_i8 val_is_i16 val_is_i32 val_is_i64 res_is_i32 res_is_i64) ->
  image_table_values col j =
  encode_instruction_table_entry fid iid
    (Z.shiftl (OpcodeClass_u64 Conversion) OPCODE_CLASS_SHIFT
    + encode_conversion sign val_type_is_i32 val_is_i8 val_is_i16 val_is_i32 val_is_i64 1 0) \/
  image_table_values col j =
  encode_instruction_table_entry fid iid
    (Z.shiftl (OpcodeClass_u64 Conversion) OPCODE_CLASS_SHIFT
    + encode_conversion sign val_type_is_i32 val_is_i8 val_is_i16 val_is_i32 val_is_i64 0 1).