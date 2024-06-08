(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.

Open Scope Z_scope.

Inductive image_table_cols :=
| col.

Parameter image_table_values : image_table_cols -> Z -> Z.

Definition COMMON_RANGE_OFFSET := 32.



Definition INDIRECT_CLASS_SHIFT := Z.shiftl 1 192.

Definition encode_br_table_entry fid iid index drop keep dst_pc :=
  let DST_PC_SHIFT := 0 in
  let COMMON_RANGE_OFFSET := 32 in
  let KEEP_SHIFT := DST_PC_SHIFT + COMMON_RANGE_OFFSET in
  let DROP_SHIFT := KEEP_SHIFT + COMMON_RANGE_OFFSET in
  let INDEX_SHIFT := DROP_SHIFT + COMMON_RANGE_OFFSET in 
  let IID_SHIFT := INDEX_SHIFT + COMMON_RANGE_OFFSET in
  let FID_SHIFT := IID_SHIFT + COMMON_RANGE_OFFSET in

  (0 * INDIRECT_CLASS_SHIFT 
    + fid * Z.shiftl 1 FID_SHIFT
    + iid * Z.shiftl 1 IID_SHIFT
    + index * Z.shiftl 1 INDEX_SHIFT
    + drop * Z.shiftl 1 DROP_SHIFT
    + keep * Z.shiftl 1 KEEP_SHIFT
    + dst_pc) mod field_order.

Definition encode_elem_entry table_idx type_idx offset func_idx :=
  let FUNC_INDEX := 0 in
  let OFFSET_INDEX := FUNC_INDEX + COMMON_RANGE_OFFSET in
  let TYPE_INDEX_SHIFT := OFFSET_INDEX + COMMON_RANGE_OFFSET in
  let TABLE_INDEX_SHIFT := TYPE_INDEX_SHIFT + COMMON_RANGE_OFFSET in

  (1 * INDIRECT_CLASS_SHIFT
    + table_idx * Z.shiftl 1 TABLE_INDEX_SHIFT
    + type_idx * Z.shiftl 1 TYPE_INDEX_SHIFT
    + offset * Z.shiftl 1 OFFSET_INDEX
    + func_idx) mod field_order.

Definition encode_init_memory_table_entry ltype is_mutable start_offset end_offset value :=
  let VALUE_SHIFT := 0 in
  let END_OFFSET_SHIFT := VALUE_SHIFT + 64 in
  let START_OFFSET_SHIFT := END_OFFSET_SHIFT + 64 in
  let IS_MUTABLE_SHIFT := START_OFFSET_SHIFT + COMMON_RANGE_OFFSET in
  let LTYPE_SHIFT := IS_MUTABLE_SHIFT + COMMON_RANGE_OFFSET in

  (ltype * (Z.shiftl 1 LTYPE_SHIFT)
    + is_mutable * (Z.shiftl 1 IS_MUTABLE_SHIFT)
    + start_offset * (Z.shiftl 1 START_OFFSET_SHIFT)
    + end_offset * (Z.shiftl 1 END_OFFSET_SHIFT)
    + value) mod field_order.

Definition encode_frame_table_entry frame_id last_frame_id callee_fid fid iid :=
  let IID_SHIFT := 0 in
  let FID_SHIFT := IID_SHIFT + COMMON_RANGE_OFFSET in
  let CALLEE_FID := FID_SHIFT + COMMON_RANGE_OFFSET in 
  let LAST_JUMP_FRAME_ID_SHIFT := CALLEE_FID + COMMON_RANGE_OFFSET in 
  let FRAME_ID_SHIFT := LAST_JUMP_FRAME_ID_SHIFT + COMMON_RANGE_OFFSET in

  (frame_id * Z.shiftl 1 FRAME_ID_SHIFT
    + last_frame_id * Z.shiftl 1 LAST_JUMP_FRAME_ID_SHIFT
    + callee_fid * Z.shiftl 1 CALLEE_FID
    + fid * Z.shiftl 1 FID_SHIFT
    + iid) mod field_order.

Definition OPCODE_ARG1_SHIFT := 64.
Definition OPCODE_ARG0_SHIFT := OPCODE_ARG1_SHIFT + COMMON_RANGE_OFFSET.
Definition OPCODE_CLASS_SHIFT := OPCODE_ARG0_SHIFT + COMMON_RANGE_OFFSET.
Definition OPCODE_SHIFT := OPCODE_CLASS_SHIFT + 16.

Definition encode_instruction_table_entry fid iid opcode :=
  let OPCODE_SHIFT := 144 in
  let IID_SHIFT := OPCODE_SHIFT in
  let FID_SHIFT := IID_SHIFT + COMMON_RANGE_OFFSET in

  (fid * Z.shiftl 1 FID_SHIFT
    + iid * Z.shiftl 1 IID_SHIFT
    + opcode) mod field_order.

Definition encode_conversion sign val_type_is_i32 val_is_i8 val_is_i16 val_is_i32 val_is_i64 res_is_i32 res_is_i64 :=
    sign * Z.shiftl 1 7
  + val_type_is_i32 * Z.shiftl 1 6
  + val_is_i8 * Z.shiftl 1 5
  + val_is_i16 * Z.shiftl 1 4
  + val_is_i32 * Z.shiftl 1 3
  + val_is_i64 * Z.shiftl 1 2
  + res_is_i32 * Z.shiftl 1 1
  + res_is_i64.
  
Definition in_itable (entry : Z) :=
  exists j, entry = image_table_values col j.
