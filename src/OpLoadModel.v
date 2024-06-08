(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Wasm.numerics.

Require Import Shared.
Require Import ETable.
Require MTable.
Require MTableModel.

(* Translation of the constrains in op_load.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_load.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::Load], which is written (ops_cell Load) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Definition WASM_BLOCK_BYTE_SIZE := 8.
Definition WASM_BLOCKS_PER_PAGE := 8192.

Notation opcode_load_offset := op_load_opcode_load_offset.
Notation load_block_index := op_load_load_block_index.
Notation load_inner_pos := op_load_load_inner_pos.
Notation load_inner_pos_diff := op_load_load_inner_pos_diff.

Notation is_cross_block := op_load_is_cross_block.
Notation cross_block_rem := op_load_cross_block_rem.
Notation cross_block_rem_diff := op_load_cross_block_rem_diff.

Notation is_one_byte := op_load_is_one_byte.
Notation is_two_bytes := op_load_is_two_bytes.
Notation is_four_bytes := op_load_is_four_bytes.
Notation is_eight_bytes := op_load_is_eight_bytes.

Notation len := op_load_len.
Notation len_modulus := op_load_len_modulus.

Notation load_tailing_u16_cells_le_0 := op_load_load_tailing_u16_cells_le_0.
Notation load_tailing_u16_cells_le_1 := op_load_load_tailing_u16_cells_le_1.
Notation load_tailing_u16_cells_le_2 := op_load_load_tailing_u16_cells_le_2.
Notation load_tailing_u16_cells_le_3 := op_load_load_tailing_u16_cells_le_3.
Notation load_tailing_u64_cell := op_load_load_tailing_u64_cell.

Notation load_tailing_diff_u16_cells_le_0 := op_load_load_tailing_diff_u16_cells_le_0.
Notation load_tailing_diff_u16_cells_le_1 := op_load_load_tailing_diff_u16_cells_le_1.
Notation load_tailing_diff_u16_cells_le_2 := op_load_load_tailing_diff_u16_cells_le_2.
Notation load_tailing_diff_u16_cells_le_3 := op_load_load_tailing_diff_u16_cells_le_3.
Notation load_tailing_diff_u64_cell := op_load_load_tailing_diff_u64_cell.

Notation load_picked_u16_cells_le_0 := op_load_load_picked_u16_cells_le_0.
Notation load_picked_u16_cells_le_1 := op_load_load_picked_u16_cells_le_1.
Notation load_picked_u16_cells_le_2 := op_load_load_picked_u16_cells_le_2.
Notation load_picked_u16_cells_le_3 := op_load_load_picked_u16_cells_le_3.
Notation load_picked_u64_cell := op_load_load_picked_u64_cell.

Notation load_leading_u16_cells_le_0 := op_load_load_leading_u16_cells_le_0.
Notation load_leading_u16_cells_le_1 := op_load_load_leading_u16_cells_le_1.
Notation load_leading_u16_cells_le_2 := op_load_load_leading_u16_cells_le_2.
Notation load_leading_u16_cells_le_3 := op_load_load_leading_u16_cells_le_3.
Notation load_leading_u64_cell := op_load_load_leading_u64_cell.

Notation lookup_pow_modulus := pow_table_lookup_modulus_cell.

Notation load_picked_leading_u16 := op_load_load_picked_leading_u16.
Notation load_picked_leading_u16_u8_high := op_load_load_picked_leading_u16_u8_high.
Notation load_picked_leading_u16_u8_low := op_load_load_picked_leading_u16_u8_low.
Notation load_picked_flag := op_load_load_picked_flag.
Notation load_picked_leading_u8_rem := op_load_load_picked_leading_u8_rem.
Notation load_picked_leading_u8_rem_diff := op_load_load_picked_leading_u8_rem_diff.

Notation res := op_load_res.
Notation is_sign := op_load_is_sign.
Notation is_i32 := op_load_is_i32.
Notation degree_helper := op_load_degree_helper.

Notation memory_table_lookup_stack_read := op_load_memory_table_lookup_stack_read.
Notation memory_table_lookup_heap_read1 := op_load_memory_table_lookup_heap_read1.
Notation memory_table_lookup_heap_read2 := op_load_memory_table_lookup_heap_read2.
Notation memory_table_lookup_stack_write := op_load_memory_table_lookup_stack_write.

Notation lookup_pow_power := pow_table_lookup_power_cell.
Notation current_memory_page_size := mpages_cell.
Notation address_within_allocated_pages_helper := op_load_address_within_allocated_pages_helper.

Axiom stack_read :
  alloc_memory_table_lookup_read_cell_with_value
    memory_table_lookup_stack_read
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => 1)
    (fun get => get (ops_cell Load)).
Notation load_base := (memory_table_lookup_stack_read AMTLRC_value_cell).

Axiom heap_read1 :
  alloc_memory_table_lookup_read_cell_with_value
    memory_table_lookup_heap_read1
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Heap)
    (fun get => get load_block_index)
    (fun get => 0)
    (fun get => get (ops_cell Load)).
Notation load_value_in_heap1 := (memory_table_lookup_heap_read1 AMTLRC_value_cell).

Axiom heap_read2 :
  alloc_memory_table_lookup_read_cell_with_value
    memory_table_lookup_heap_read2
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Heap)
    (fun get => get load_block_index + 1)
    (fun get => 0)
    (fun get => get (ops_cell Load) * get is_cross_block).
Notation load_value_in_heap2 := (memory_table_lookup_heap_read2 AMTLRC_value_cell).

Axiom stack_write :
  alloc_memory_table_lookup_write_cell
    memory_table_lookup_stack_write
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => get is_i32)
    (fun get => get res)
    (fun get => get (ops_cell Load)).

Axiom op_load_length :
  gate etable
    (fun get =>
    (get (ops_cell Load) 0) *
        ((get is_one_byte 0) + (get is_two_bytes 0)
      + (get is_four_bytes 0) + (get is_eight_bytes 0)
      - 1)
     :: nil).

Axiom op_load_len_gate :
  gate etable
    (fun get =>
    (get (ops_cell Load) 0) *
        ((get len 0 - 1) - (get is_two_bytes 0) 
      - (get is_four_bytes 0 * 3) - (get is_eight_bytes 0 * 7))
     :: nil).

Axiom op_load_load_block_index_gate :
  gate etable
    (fun get =>
    (get (ops_cell Load) 0) *
        ((get load_block_index 0 * WASM_BLOCK_BYTE_SIZE) + (get load_inner_pos 0)
      - (get opcode_load_offset 0) - (get load_base 0))
     :: (get (ops_cell Load) 0) * ((get load_inner_pos 0)
      + (get load_inner_pos_diff 0) - 7)
     :: nil).

Axiom op_load_cross_bloc :
  gate etable
    (fun get =>
    (get (ops_cell Load) 0) *
        ((get is_cross_block 0 * WASM_BLOCK_BYTE_SIZE) + (get cross_block_rem 0)
      - (get load_inner_pos 0) - (get len 0) + 1)
     :: (get (ops_cell Load) 0) * ((get cross_block_rem 0)
      + (get cross_block_rem_diff 0) - (WASM_BLOCK_BYTE_SIZE - 1))
     :: (get (ops_cell Load) 0) * (get is_cross_block 0 - 1)
      * (get load_value_in_heap2 0)
     :: nil).

Axiom op_load_pick_value :
  gate etable
    (fun get =>
    (get (ops_cell Load) 0) *
        ((get len_modulus 0)
      - (get is_one_byte 0 * (Z.shiftl 1 8))
      - (get is_two_bytes 0 * (Z.shiftl 1 16))
      - (get is_four_bytes 0 * (Z.shiftl 1 32))
      - (get is_eight_bytes 0 * (Z.shiftl 1 64)))
     :: (get (ops_cell Load) 0) * ((get load_tailing_u64_cell 0)
      + (get load_picked_u64_cell 0 * get lookup_pow_modulus 0)
      + (get load_leading_u64_cell 0 * get lookup_pow_modulus 0 * get len_modulus 0)
      - (get load_value_in_heap1 0)
      - (get load_value_in_heap2 0 * (Z.shiftl 1 64)))
     :: (get (ops_cell Load) 0) * ((get load_tailing_u64_cell 0)
      + (get load_tailing_diff_u64_cell 0)
      + 1
      - (get lookup_pow_modulus 0))
     :: nil).

Axiom op_load_pick_value_size_check :
  gate etable
    (fun get =>
    (get (ops_cell Load) 0) *
        (get is_four_bytes 0)
      * (get load_picked_u16_cells_le_2 0 + get load_picked_u16_cells_le_3 0)
     :: (get (ops_cell Load) 0) * (get is_two_bytes 0)
      * (get load_picked_u64_cell 0 - get load_picked_leading_u16 0)
     :: (get (ops_cell Load) 0) * (get is_one_byte 0)
      * (get load_picked_u64_cell 0 - get load_picked_leading_u16_u8_low 0)
     :: nil).

Axiom op_load_pick_u16_decompose1 :
  gate etable
    (fun get =>
    (get (ops_cell Load) 0) *
        ((get load_picked_leading_u16 0)
      - (get is_two_bytes 0 + get is_one_byte 0)
      * (get load_picked_u16_cells_le_0 0)
      - (get is_four_bytes 0 * get load_picked_u16_cells_le_1 0)
      - (get is_eight_bytes 0 * get load_picked_u16_cells_le_3 0))
     :: nil).

Axiom op_load_pick_u16_decompose2 :
  gate etable
    (fun get =>
    (get (ops_cell Load) 0) *
        ((get load_picked_leading_u16_u8_high 0 * (Z.shiftl 1 8))
      + (get load_picked_leading_u16_u8_low 0)
      - (get load_picked_leading_u16 0))
     :: nil).

Axiom op_load_flag :
  gate etable
    (fun get =>
        let value_leading_u8 := 
        (get is_one_byte 0 * get load_picked_leading_u16_u8_low 0)
      + (1 - get is_one_byte 0) * (get load_picked_leading_u16_u8_high 0) in

    (get (ops_cell Load) 0) *
        ((get load_picked_flag 0 * 128)
      + (get load_picked_leading_u8_rem 0)
      - value_leading_u8)
     :: (get (ops_cell Load) 0) * ((get load_picked_leading_u8_rem 0)
      + (get load_picked_leading_u8_rem_diff 0)
      - 127)
     :: nil).

Axiom op_load_extension :
  gate etable
    (fun get =>
    (get (ops_cell Load) 0) *
        ((get load_picked_flag 0)
      * (get is_sign 0)
      - (get degree_helper 0))
     :: (get (ops_cell Load) 0) * ((get degree_helper 0)
      * (get is_one_byte 0 * 0xFFFFFF00 
      +  get is_two_bytes 0 * 0xFFFF0000
      + (1 - get is_eight_bytes 0)
      * (1 - get is_i32 0)
      * (0xFFFFFFFF00000000))
      + (get load_picked_u64_cell 0)
      - (get res 0))
     :: nil). 

Axiom op_load_pos_modulus :
  gate etable
    (fun get =>
    (get (ops_cell Load) 0) *
        ((get lookup_pow_power 0) - (get load_inner_pos 0 * 8 + 128))
     :: nil).

Axiom op_load_allocated_address :
  gate etable
    (fun get =>
    (get (ops_cell Load) 0) *
        ((get load_block_index 0)
      + (get is_cross_block 0 + 1)
      + (get address_within_allocated_pages_helper 0)
      - (get current_memory_page_size 0 * WASM_BLOCKS_PER_PAGE))
     :: nil).

(* Common Range Cells *)
Axiom opcode_load_offset_common : iscommon opcode_load_offset.
Axiom load_block_index_common : iscommon load_block_index.
Axiom cross_block_rem_common: iscommon cross_block_rem.
Axiom cross_block_rem_diff_common: iscommon cross_block_rem_diff.
Axiom load_picked_leading_u8_rem_common: iscommon load_picked_leading_u8_rem.
Axiom load_picked_leading_u8_rem_diff_common: iscommon load_picked_leading_u8_rem_diff.
Axiom address_within_allocated_pages_helper_common: iscommon address_within_allocated_pages_helper.

(* Bit Cells *)
Axiom is_cross_block_bit : isbit is_cross_block.
Axiom is_one_byte_bit: isbit is_one_byte.
Axiom is_two_bytes_bit: isbit is_two_bytes.
Axiom is_four_bytes_bit: isbit is_four_bytes.
Axiom is_eight_bytes_bit: isbit is_eight_bytes.
Axiom load_picked_flag_bit: isbit load_picked_flag.
Axiom is_sign_bit: isbit is_sign.
Axiom is_i32_bit: isbit is_i32.
Axiom degree_helper_bit: isbit degree_helper.

(* U8 Cells *)
Axiom load_inner_pos_U8 : is8 load_inner_pos.
Axiom load_inner_pos_diff_U8 : is8 load_inner_pos_diff.
Axiom load_picked_leading_u16_u8_high_U8 : is8 load_picked_leading_u16_u8_high.
Axiom load_picked_leading_u16_u8_low_U8 : is8 load_picked_leading_u16_u8_low.

(* U16 Cells *)
Axiom load_tailing_U16_cells:
    is16 load_tailing_u16_cells_le_0 /\
    is16 load_tailing_u16_cells_le_1 /\
    is16 load_tailing_u16_cells_le_2 /\
    is16 load_tailing_u16_cells_le_3.

Axiom load_tailing_diff_U16_cells:
    is16 load_tailing_diff_u16_cells_le_0 /\
    is16 load_tailing_diff_u16_cells_le_1 /\
    is16 load_tailing_diff_u16_cells_le_2 /\
    is16 load_tailing_diff_u16_cells_le_3.

Axiom load_picked_U16_cells:
    is16 load_picked_u16_cells_le_0 /\
    is16 load_picked_u16_cells_le_1 /\
    is16 load_picked_u16_cells_le_2 /\
    is16 load_picked_u16_cells_le_3.

Axiom load_leading_U16_cells:
    is16 load_leading_u16_cells_le_0 /\
    is16 load_leading_u16_cells_le_1 /\
    is16 load_leading_u16_cells_le_2 /\
    is16 load_leading_u16_cells_le_3.

(* U64 Cells *)
Axiom load_tailing_U64: is64_from16
    load_tailing_u64_cell 
    load_tailing_u16_cells_le_0
    load_tailing_u16_cells_le_1
    load_tailing_u16_cells_le_2
    load_tailing_u16_cells_le_3.

Axiom load_tailing_diff_U64: is64_from16
    load_tailing_diff_u64_cell
    load_tailing_diff_u16_cells_le_0
    load_tailing_diff_u16_cells_le_1
    load_tailing_diff_u16_cells_le_2
    load_tailing_diff_u16_cells_le_3.

Axiom load_picked_U64: is64_from16
    load_picked_u64_cell
    load_picked_u16_cells_le_0
    load_picked_u16_cells_le_1
    load_picked_u16_cells_le_2
    load_picked_u16_cells_le_3.

Axiom load_leading_U64: is64_from16
    load_leading_u64_cell
    load_leading_u16_cells_le_0
    load_leading_u16_cells_le_1
    load_leading_u16_cells_le_2
    load_leading_u16_cells_le_3.
