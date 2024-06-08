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

(* Translation of the constrains in op_store.rs  *)

(* These axioms represent the definitions in etable/op_configure/op_store.rs .
   However, compared to the Rust source code one difference is that we have multiplied 
   all the constraints by ops[OpcodeClass::Store], which is written (ops_cell Store) here. 
   In the real zkwasm source code that multiplication instead happens in the macro
   sum_ops_expr in etable/mod.rs, but because we use a "shallow embedding" into Coq
   it is difficult to split the definition into two places, and we do the multiplication here instead.
 *)

Definition WASM_BLOCK_BYTE_SIZE := 8.
Definition WASM_BLOCKS_PER_PAGE := 8192.

Notation opcode_store_offset := op_store_opcode_store_offset.
Notation load_block_index := op_store_load_block_index.
Notation load_block_inner_pos_bits_0 := op_store_load_block_inner_pos_bits_0.
Notation load_block_inner_pos_bits_1 := op_store_load_block_inner_pos_bits_1.
Notation load_block_inner_pos_bits_2 := op_store_load_block_inner_pos_bits_2.
Notation load_block_inner_pos := op_store_load_block_inner_pos.
Notation is_cross_block := op_store_is_cross_block.
Notation cross_block_rem := op_store_cross_block_rem.
Notation cross_block_rem_diff := op_store_cross_block_rem_diff.
Notation len := op_store_len.
Notation len_modulus := op_store_len_modulus.
Notation load_tailing := op_store_load_tailing.
Notation load_tailing_diff := op_store_load_tailing_diff.
Notation load_picked_u64_cell := op_store_load_picked_u64_cell.
Notation load_picked_u16_cells_le_0 := op_store_load_picked_u16_cells_le_0.
Notation load_picked_u16_cells_le_1 := op_store_load_picked_u16_cells_le_1.
Notation load_picked_u16_cells_le_2 := op_store_load_picked_u16_cells_le_2.
Notation load_picked_u16_cells_le_3 := op_store_load_picked_u16_cells_le_3.
Notation load_picked_byte_proof := op_store_load_picked_byte_proof.
Notation load_leading := op_store_load_leading.
Notation store_value_u64_cell := op_store_store_value_u64_cell.
Notation store_value_u16_cells_le_0 := op_store_store_value_u16_cells_le_0.
Notation store_value_u16_cells_le_1 := op_store_store_value_u16_cells_le_1.
Notation store_value_u16_cells_le_2 := op_store_store_value_u16_cells_le_2.
Notation store_value_u16_cells_le_3 := op_store_store_value_u16_cells_le_3.
Notation store_value_wrapped := op_store_store_value_wrapped.
Notation is_one_byte := op_store_is_one_byte.
Notation is_two_bytes := op_store_is_two_bytes.
Notation is_four_bytes := op_store_is_four_bytes.
Notation is_eight_bytes := op_store_is_eight_bytes.
Notation is_i32 := op_store_is_i32.
Notation memory_table_lookup_stack_read_val := op_store_memory_table_lookup_stack_read_val.
Notation memory_table_lookup_stack_read_pos := op_store_memory_table_lookup_stack_read_pos.
Notation memory_table_lookup_heap_read1 := op_store_memory_table_lookup_heap_read1.
Notation memory_table_lookup_heap_read2 := op_store_memory_table_lookup_heap_read2.
Notation memory_table_lookup_heap_write1 := op_store_memory_table_lookup_heap_write1.
Notation memory_table_lookup_heap_write2 := op_store_memory_table_lookup_heap_write2.
Notation unchanged_value := op_store_unchanged_value.
Notation store_value_tailing_u16_u8_high := op_store_store_value_tailing_u16_u8_high.
Notation store_value_tailing_u16_u8_low := op_store_store_value_tailing_u16_u8_low.
Notation address_within_allocated_pages_helper := op_store_address_within_allocated_pages_helper.
Notation lookup_pow_modulus := pow_table_lookup_modulus_cell.
Notation lookup_pow_power := pow_table_lookup_power_cell.
Notation current_memory_page_size := mpages_cell.

Axiom stack_read_val :
  alloc_memory_table_lookup_read_cell
    memory_table_lookup_stack_read_val
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    (fun get => get is_i32)
    (fun get => get store_value_u64_cell)
    (fun get => get (ops_cell Store)).

Axiom stack_read_pos :
  alloc_memory_table_lookup_read_cell_with_value
    memory_table_lookup_stack_read_pos
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    (fun get => 1)
    (fun get => get (ops_cell Store)).
Notation store_base := (memory_table_lookup_stack_read_pos AMTLRC_value_cell).

Axiom heap_read1 :
  alloc_memory_table_lookup_read_cell_with_value
    memory_table_lookup_heap_read1
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Heap)
    (fun get => get load_block_index)
    (fun get => 0)
    (fun get => get (ops_cell Store)).
Notation load_value_in_heap1 := (memory_table_lookup_heap_read1 AMTLRC_value_cell).

Axiom heap_read2 :
  alloc_memory_table_lookup_read_cell_with_value
    memory_table_lookup_heap_read2
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Heap)
    (fun get => get load_block_index + 1)
    (fun get => 0)
    (fun get => get (ops_cell Store) * get is_cross_block).
Notation load_value_in_heap2 := (memory_table_lookup_heap_read2 AMTLRC_value_cell).

Axiom heap_write1 :
  alloc_memory_table_lookup_write_cell_with_value
    memory_table_lookup_heap_write1
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Heap)
    (fun get => get load_block_index)
    (fun get => 0)
    (fun get => get (ops_cell Store)).
Notation store_value_in_heap1 := (memory_table_lookup_heap_write1 AMTLWC_value_cell).

Axiom heap_write2 :
  alloc_memory_table_lookup_write_cell_with_value
    memory_table_lookup_heap_write2
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Heap)
    (fun get => get load_block_index + 1)
    (fun get => 0)
    (fun get => get (ops_cell Store) * get is_cross_block).
Notation store_value_in_heap2 := (memory_table_lookup_heap_write2 AMTLWC_value_cell).

Axiom op_store_length :
  gate etable
    (fun get =>
    (get (ops_cell Store) 0) *
        ((get is_one_byte 0) + (get is_two_bytes 0)
      + (get is_four_bytes 0) + (get is_eight_bytes 0)
      - 1)
     :: nil).

Axiom op_store_len_gate :
  gate etable
    (fun get =>
    (get (ops_cell Store) 0) *
        ((get len 0 - 1) - (get is_two_bytes 0) 
      - (get is_four_bytes 0 * 3) - (get is_eight_bytes 0 * 7))
     :: nil).

Axiom op_store_load_block_index_gate :
  gate etable
    (fun get =>
    (get (ops_cell Store) 0) *
        ((get load_block_index 0 * WASM_BLOCK_BYTE_SIZE) + (get load_block_inner_pos 0)
      - (get opcode_store_offset 0) - (get store_base 0))
     :: (get (ops_cell Store) 0) * ((get load_block_inner_pos 0)
      - (get load_block_inner_pos_bits_0 0)
      - (get load_block_inner_pos_bits_1 0) * 2
      - (get load_block_inner_pos_bits_2 0) * 4)
     :: nil).

Axiom op_store_cross_bloc :
  gate etable
    (fun get =>
    (get (ops_cell Store) 0) *
        ((get is_cross_block 0 * WASM_BLOCK_BYTE_SIZE) + (get cross_block_rem 0)
      - (get load_block_inner_pos 0) - (get len 0) + 1)
     :: (get (ops_cell Store) 0) * ((get cross_block_rem 0)
      + (get cross_block_rem_diff 0) - (WASM_BLOCK_BYTE_SIZE - 1))
     :: (get (ops_cell Store) 0) * (get is_cross_block 0 - 1)
      * (get load_value_in_heap2 0)
     :: nil).

Axiom op_store_len_modulus_gate :
  gate etable
    (fun get =>
    (get (ops_cell Store) 0) *
        ((get len_modulus 0)
      - (get is_one_byte 0 * (Z.shiftl 1 8))
      - (get is_two_bytes 0 * (Z.shiftl 1 16))
      - (get is_four_bytes 0 * (Z.shiftl 1 32))
      - (get is_eight_bytes 0 * (Z.shiftl 1 64)))
  ::nil).

Axiom op_store_pick_value1 :
  gate etable
    (fun get =>
      (get (ops_cell Store) 0)
    * (get unchanged_value 0 - get load_tailing 0
    - get load_leading 0 * get lookup_pow_modulus 0 * get len_modulus 0)
    ::nil).

Axiom op_store_pick_value2 :
  gate etable
    (fun get =>
      (get (ops_cell Store) 0)
    * (get unchanged_value 0 + get load_picked_u64_cell 0 * get lookup_pow_modulus 0
    - get load_value_in_heap1 0 - get load_value_in_heap2 0 * Z.shiftl 1 64)
    ::nil).

Axiom op_store_pick_value3 :
  gate etable
    (fun get =>
      (get (ops_cell Store) 0)
    * (get unchanged_value 0 + get store_value_wrapped 0 * get lookup_pow_modulus 0
    - get store_value_in_heap1 0 - get store_value_in_heap2 0 * Z.shiftl 1 64)
    ::nil).

Axiom op_store_pick_helper_value_check :
  gate etable
    (fun get =>
      (get (ops_cell Store) 0)
    * (get load_tailing 0 + get load_tailing_diff 0 + 1
    - get lookup_pow_modulus 0)
    ::nil).

Axiom op_store_pick_value_size_check :
  gate etable
    (fun get =>
    (get (ops_cell Store) 0) *
        (get is_four_bytes 0)
      * (get load_picked_u16_cells_le_2 0 + get load_picked_u16_cells_le_3 0)
     :: (get (ops_cell Store) 0) * (get is_two_bytes 0)
      * (get load_picked_u64_cell 0 - get load_picked_u16_cells_le_0 0)
     :: (get (ops_cell Store) 0) * (get is_one_byte 0)
      * (get load_picked_u64_cell 0 - get load_picked_byte_proof 0)
     :: nil).

Axiom op_store_tailing_u16_decompose :
  gate etable
    (fun get =>
      (get (ops_cell Store) 0)
    * (get store_value_tailing_u16_u8_high 0 * Z.shiftl 1 8
    + get store_value_tailing_u16_u8_low 0 - get store_value_u16_cells_le_0 0)
    ::nil).

Axiom op_store_value_wrap :
  gate etable
    (fun get =>
      (get (ops_cell Store) 0)
    * (get store_value_wrapped 0
    - (get is_one_byte 0 * get store_value_tailing_u16_u8_low 0
    + get is_two_bytes 0 * get store_value_u16_cells_le_0 0
    + get is_four_bytes 0 
    * (get store_value_u16_cells_le_0 0 + get store_value_u16_cells_le_1 0 * Z.shiftl 1 16)
    + get is_eight_bytes 0 * get store_value_u64_cell 0))
    ::nil).

Axiom op_store_pow_lookup :
  gate etable
    (fun get =>
    (get (ops_cell Store) 0) *
        ((get lookup_pow_power 0) - (get load_block_inner_pos 0 * 8 + 128))
     :: nil).

Axiom op_store_allocated_address :
  gate etable
    (fun get =>
    (get (ops_cell Store) 0) *
        ((get load_block_index 0)
      + (get is_cross_block 0 + 1)
      + (get address_within_allocated_pages_helper 0)
      - (get current_memory_page_size 0 * WASM_BLOCKS_PER_PAGE))
     :: nil).

(* Common Range Cells *)
Axiom opcode_store_offset_common : iscommon opcode_store_offset.
Axiom load_block_index_common : iscommon load_block_index.
Axiom cross_block_rem_common: iscommon cross_block_rem.
Axiom cross_block_rem_diff_common: iscommon cross_block_rem_diff.
Axiom address_within_allocated_pages_helper_common: iscommon address_within_allocated_pages_helper.

(* Bit Cells *)
Axiom load_block_inner_pos_bits_0_bit : isbit load_block_inner_pos_bits_0.
Axiom load_block_inner_pos_bits_1_bit : isbit load_block_inner_pos_bits_1.
Axiom load_block_inner_pos_bits_2_bit : isbit load_block_inner_pos_bits_2.
Axiom is_cross_block_bit : isbit is_cross_block.
Axiom is_one_byte_bit: isbit is_one_byte.
Axiom is_two_bytes_bit: isbit is_two_bytes.
Axiom is_four_bytes_bit: isbit is_four_bytes.
Axiom is_eight_bytes_bit: isbit is_eight_bytes.
Axiom is_i32_bit: isbit is_i32.

(* U8 Cells *)
Axiom load_picked_byte_proof_U8 : is8 load_picked_byte_proof.
Axiom store_value_tailing_u16_u8_high_U8 : is8 store_value_tailing_u16_u8_high.
Axiom store_value_tailing_u16_u8_low_U8 : is8 store_value_tailing_u16_u8_low.

(* U16 Cells *)
Axiom load_picked_u16_cells_le_0_U16 : is16 load_picked_u16_cells_le_0.
Axiom load_picked_u16_cells_le_1_U16 : is16 load_picked_u16_cells_le_1.
Axiom load_picked_u16_cells_le_2_U16 : is16 load_picked_u16_cells_le_2.
Axiom load_picked_u16_cells_le_3_U16 : is16 load_picked_u16_cells_le_3.
Axiom store_value_u16_cells_le_0_U16 : is16 store_value_u16_cells_le_0.
Axiom store_value_u16_cells_le_1_U16 : is16 store_value_u16_cells_le_1.
Axiom store_value_u16_cells_le_2_U16 : is16 store_value_u16_cells_le_2.
Axiom store_value_u16_cells_le_3_U16 : is16 store_value_u16_cells_le_3.

(* U64 Cells *)
Axiom load_tailing_U64 : is64 load_tailing.
Axiom load_tailing_diff_U64 : is64 load_tailing_diff.
Axiom load_picked_U64 : is64_from16
    load_picked_u64_cell
    load_picked_u16_cells_le_0
    load_picked_u16_cells_le_1
    load_picked_u16_cells_le_2
    load_picked_u16_cells_le_3.
Axiom load_leading_U64 : is64 load_leading.
Axiom store_value_U64 : is64_from16
    store_value_u64_cell
    store_value_u16_cells_le_0
    store_value_u16_cells_le_1
    store_value_u16_cells_le_2
    store_value_u16_cells_le_3.
