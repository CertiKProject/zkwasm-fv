(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

(* This file models the constraints from etable/mod.rs, as well as
   the EventTableOpcodeConfigBuilder traits for each instruction (i.e., `opcode`,
   `sp_diff`, etc; in this file the traits are modeled by the EventTableOpcodeConfig record. 

  Except for the traits, the circuits in the opcode specific files (etable/op_configure/op_XX.rs)
  are not in this file but in the OpXxxModel.v files. 

  Compared to other circuit definitions, the circuits from `etable/mod.rs` are translated in a 
  less literal way. That is because in the rust file they are created with the 
  `sum_ops_expr_with_init` macro, which processes a collection of Rust syntax trees to create 
  a big sum expression. In our shallow translation into Coq we do not represent the Rust AST
  so we can not translate the macro literally. Instead we paraphrase each gate as a set of 
  lemmas expressing the property ensured  by the circuit.
   (see e.g. rest_mops_change_enabled below for a representative example).
*)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import Wasm.numerics.
Require        Wasm.datatypes.
Require Import Lia.

Require Import ImageTableModel.
Require MTableModel MTable.
Require JTableModel.

Inductive OpcodeClass :=
| BinShift
| Bin
| BrIfEqz
| BrIf
| Br
| Call
| CallHost
| Const
| Conversion
| Drop
| GlobalGet
| GlobalSet
| LocalGet
| LocalSet
| LocalTee
| Rel
| Return
| Select
| Test
| Unary
| Load
| Store
| BinBit
| MemorySize
| MemoryGrow
| BrTable
| CallIndirect.

Definition OpcodeClass_u64 cls :=
  match cls with
  | LocalGet => 1
  | LocalSet => 2
  | LocalTee => 3
  | GlobalGet => 4
  | GlobalSet => 5
  | Const => 6
  | Drop => 7
  | Select => 8
  | Return => 9
  | Bin => 10
  | Unary => 11
  | BinShift => 12
  | BinBit => 13
  | Test => 14
  | Rel => 15
  | Br => 16
  | BrIf => 17
  | BrIfEqz => 18
  | BrTable => 19
  (* | Unreachable => 20 *)
  | Call => 21
  | CallHost => 22
  | CallIndirect => 23
  | Load => 24
  | Store => 25
  | MemorySize => 26
  | MemoryGrow => 27
  | Conversion => 28
  (* | ForeignPluginStart => 29 *)
  end.

Inductive AllocatedMemoryTableLookupReadCell :=
| AMTLRC_encode_cell
| AMTLRC_start_eid_cell
| AMTLRC_end_eid_cell
| AMTLRC_start_eid_diff_cell
| AMTLRC_end_eid_diff_cell
| AMTLRC_value_cell.

Inductive AllocatedMemoryTableLookupWriteCell :=
| AMTLWC_encode_cell
| AMTLWC_start_eid_cell
| AMTLWC_end_eid_cell
| AMTLWC_value_cell.

Inductive AllocatedBitTableLookupCells :=
| ABTLC_op
| ABTLC_left
| ABTLC_right
| ABTLC_result.

Inductive etable_cols :=
(* Common config, from etable/mod.rs *)
| enabled_cell
| ops_cell : OpcodeClass -> etable_cols
| rest_mops_cell
| rest_jops_cell
| input_index_cell
| context_input_index_cell
| context_output_index_cell
| external_host_call_index_cell
| sp_cell
| mpages_cell
| frame_id_cell
| eid_cell
| fid_cell
| iid_cell
| maximal_memory_pages_cell
| itable_lookup_cell
| brtable_lookup_cell
| jtable_lookup_cell       (* Todo: specify lookup relation *)
| pow_table_lookup_modulus_cell
| pow_table_lookup_power_cell
| bit_table_lookup_cells : AllocatedBitTableLookupCells -> etable_cols
| external_foreign_call_lookup_cell

(* cells from op_bin.rs. Circuits and range axioms are in OpBin.v *)
| op_bin_is_i32
| op_bin_lhs_u64_cell
| op_bin_lhs_u16_cells_le_0
| op_bin_lhs_u16_cells_le_1
| op_bin_lhs_u16_cells_le_2
| op_bin_lhs_u16_cells_le_3
| op_bin_lhs_flag_bit_cell
| op_bin_lhs_flag_u16_rem_cell
| op_bin_lhs_flag_u16_rem_diff_cell
| op_bin_rhs_u64_cell
| op_bin_rhs_u16_cells_le_0
| op_bin_rhs_u16_cells_le_1
| op_bin_rhs_u16_cells_le_2
| op_bin_rhs_u16_cells_le_3
| op_bin_rhs_flag_bit_cell
| op_bin_rhs_flag_u16_rem_cell
| op_bin_rhs_flag_u16_rem_diff_cell
| op_bin_d_u64_cell
| op_bin_d_u16_cells_le_0
| op_bin_d_u16_cells_le_1
| op_bin_d_u16_cells_le_2
| op_bin_d_u16_cells_le_3
| op_bin_d_flag_helper_diff
| op_bin_aux1
| op_bin_aux2
| op_bin_overflow
| op_bin_is_add
| op_bin_is_sub
| op_bin_is_mul
| op_bin_is_div_u
| op_bin_is_div_s
| op_bin_is_rem_u
| op_bin_is_rem_s
| op_bin_is_div_s_or_rem_s
| op_bin_d_leading_u16
| op_bin_normalized_lhs
| op_bin_normalized_rhs
| op_bin_res_flag
| op_bin_size_modulus
| op_bin_degree_helper1
| op_bin_degree_helper2
| op_bin_memory_table_lookup_stack_read_rhs : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_bin_memory_table_lookup_stack_read_lhs : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_bin_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_bin_bit.rs. Circuits and range axioms are in OpBinBit.v *)
| op_bin_bit_is_i32
| op_bin_bit_op_class
| op_bin_bit_memory_table_lookup_stack_read_lhs : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_bin_bit_memory_table_lookup_stack_read_rhs : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_bin_bit_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_bin_shift.rs. Circuits and range axioms are in OpBinShift.v *)
| op_bin_shift_is_i32
| op_bin_shift_lhs_u64_cell
| op_bin_shift_lhs_u16_cells_le_0
| op_bin_shift_lhs_u16_cells_le_1
| op_bin_shift_lhs_u16_cells_le_2
| op_bin_shift_lhs_u16_cells_le_3
| op_bin_shift_lhs_flag_bit_cell
| op_bin_shift_lhs_flag_u16_rem_cell
| op_bin_shift_lhs_flag_u16_rem_diff_cell
| op_bin_shift_rhs_u64_cell
| op_bin_shift_rhs_u16_cells_le_0
| op_bin_shift_rhs_u16_cells_le_1
| op_bin_shift_rhs_u16_cells_le_2
| op_bin_shift_rhs_u16_cells_le_3
| op_bin_shift_round
| op_bin_shift_rem
| op_bin_shift_diff
| op_bin_shift_pad
| op_bin_shift_rhs_modulus
| op_bin_shift_size_modulus
| op_bin_shift_rhs_round
| op_bin_shift_rhs_rem
| op_bin_shift_rhs_rem_diff
| op_bin_shift_is_shl
| op_bin_shift_is_shr_u
| op_bin_shift_is_shr_s
| op_bin_shift_is_rotl
| op_bin_shift_is_rotr
| op_bin_shift_is_l
| op_bin_shift_is_r
| op_bin_shift_degree_helper
| op_bin_shift_memory_table_lookup_stack_read_rhs : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_bin_shift_memory_table_lookup_stack_read_lhs : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_bin_shift_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_br_if_eqz.rs. Circuits and range axioms are in OpBrIfEqz.v *)
| op_br_if_eqz_cond_inv_cell
| op_br_if_eqz_cond_is_zero_cell
| op_br_if_eqz_cond_is_not_zero_cell
| op_br_if_eqz_keep_cell
| op_br_if_eqz_is_i32_cell
| op_br_if_eqz_drop_cell
| op_br_if_eqz_dst_pc_cell
| op_br_if_eqz_memory_table_lookup_stack_read_cond : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_br_if_eqz_memory_table_lookup_stack_read_return_value : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_br_if_eqz_memory_table_lookup_stack_write_return_value : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_br_if.rs. Circuits and range axioms are in OpBrIf.v *)
| op_br_if_cond_cell
| op_br_if_cond_inv_cell
| op_br_if_cond_is_zero_cell
| op_br_if_cond_is_not_zero_cell
| op_br_if_keep_cell
| op_br_if_is_i32_cell
| op_br_if_drop_cell
| op_br_if_dst_pc_cell
| op_br_if_value_cell
| op_br_if_memory_table_lookup_stack_read_cond : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_br_if_memory_table_lookup_stack_read_return_value : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_br_if_memory_table_lookup_stack_write_return_value : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_br_table.rs. Circuits and range axioms are in OpBrTable.v *)
| op_br_table_keep
| op_br_table_keep_is_i32
| op_br_table_keep_value
| op_br_table_drop
| op_br_table_dst_iid
| op_br_table_expected_index
| op_br_table_effective_index
| op_br_table_targets_len
| op_br_table_is_out_of_bound
| op_br_table_is_not_out_of_bound
| op_br_table_diff
| op_br_table_memory_table_lookup_stack_read_index : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_br_table_memory_table_lookup_stack_read_return_value : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_br_table_memory_table_lookup_stack_write_return_value : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_br.rs. Circuits and range axioms are in OpBr.v *)
| op_br_keep_cell
| op_br_is_i32_cell
| op_br_drop_cell
| op_br_dst_pc_cell
| op_br_value_cell
| op_br_memory_table_lookup_stack_read : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_br_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_call_indirect.rs. Circuits and range axioms are in OpCallIndirect.v *)
| op_call_indirect_type_index
| op_call_indirect_table_index
| op_call_indirect_offset
| op_call_indirect_func_index
| op_call_indirect_memory_table_lookup_stack_read : AllocatedMemoryTableLookupReadCell -> etable_cols

(* cells from op_call.rs. Circuits and range axioms are in OpCall.v *)
| op_call_index

(* cells from op_const.rs. Circuits and range axioms are in OpConst.v *)
| op_const_is_i32
| op_const_value
| op_const_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_conversion.rs. Circuits and range axioms are in OpConversion.v *)
| op_conversion_value_u64_cell
| op_conversion_value_u16_cells_le_0
| op_conversion_value_u16_cells_le_1
| op_conversion_value_u16_cells_le_2
| op_conversion_value_u16_cells_le_3
| op_conversion_value_is_i8
| op_conversion_value_is_i16
| op_conversion_value_is_i32
| op_conversion_value_is_i64
| op_conversion_value_type_is_i32
| op_conversion_res_is_i32
| op_conversion_res_is_i64
| op_conversion_sign_op
| op_conversion_is_i32_wrap_i64
| op_conversion_flag_bit
| op_conversion_shift
| op_conversion_padding
| op_conversion_d
| op_conversion_rem
| op_conversion_rem_helper
| op_conversion_modulus 
| op_conversion_memory_table_lookup_stack_read : AllocatedMemoryTableLookupReadCell  -> etable_cols
| op_conversion_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_global_get.rs. Circuits and range axioms are in OpGlobalGet.v *)
|  op_global_get_idx_cell
|  op_global_get_is_i32_cell
|  op_global_get_value_u64_cell
|  op_global_get_value_u16_cells_le0
|  op_global_get_value_u16_cells_le1
|  op_global_get_value_u16_cells_le2
|  op_global_get_value_u16_cells_le3
|  op_global_get_memory_table_lookup_global_read : AllocatedMemoryTableLookupReadCell  -> etable_cols
|  op_global_get_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_global_set.rs. Circuits and range axioms are in OpGlobalSet.v *)
|  op_global_set_idx_cell
|  op_global_set_is_i32_cell
|  op_global_set_value_u64_cell
|  op_global_set_value_u16_cells_le0
|  op_global_set_value_u16_cells_le1
|  op_global_set_value_u16_cells_le2
|  op_global_set_value_u16_cells_le3
|  op_global_set_memory_table_lookup_stack_read   : AllocatedMemoryTableLookupReadCell  -> etable_cols
|  op_global_set_memory_table_lookup_global_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_local_get.rs. Circuits and range axioms are in OpLocalGet.v *)
| op_local_get_is_i32_cell
| op_local_get_offset_cell
| op_local_get_value_cell
| op_local_get_memory_table_lookup_stack_read : AllocatedMemoryTableLookupReadCell  -> etable_cols
| op_local_get_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_local_set.rs. Circuits and range axioms are in OpLocalSet.v *)
| op_local_set_is_i32_cell
| op_local_set_offset_cell
| op_local_set_value_cell
| op_local_set_memory_table_lookup_stack_read : AllocatedMemoryTableLookupReadCell  -> etable_cols
| op_local_set_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_local_tee.rs. Circuits and range axioms are in OpLocalTee.v *)
| op_local_tee_is_i32_cell
| op_local_tee_offset_cell
| op_local_tee_value_cell
| op_local_tee_memory_table_lookup_stack_read : AllocatedMemoryTableLookupReadCell  -> etable_cols
| op_local_tee_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_load.rs. Circuits and range axioms are in OpLoad.v *)
| op_load_opcode_load_offset
| op_load_load_block_index
| op_load_load_inner_pos
| op_load_load_inner_pos_diff
| op_load_is_cross_block
| op_load_cross_block_rem
| op_load_cross_block_rem_diff
| op_load_is_one_byte
| op_load_is_two_bytes
| op_load_is_four_bytes
| op_load_is_eight_bytes
| op_load_len
| op_load_len_modulus
| op_load_load_tailing_u16_cells_le_0
| op_load_load_tailing_u16_cells_le_1
| op_load_load_tailing_u16_cells_le_2
| op_load_load_tailing_u16_cells_le_3
| op_load_load_tailing_u64_cell
| op_load_load_tailing_diff_u16_cells_le_0
| op_load_load_tailing_diff_u16_cells_le_1
| op_load_load_tailing_diff_u16_cells_le_2
| op_load_load_tailing_diff_u16_cells_le_3
| op_load_load_tailing_diff_u64_cell
| op_load_load_picked_u16_cells_le_0
| op_load_load_picked_u16_cells_le_1
| op_load_load_picked_u16_cells_le_2
| op_load_load_picked_u16_cells_le_3
| op_load_load_picked_u64_cell
| op_load_load_leading_u16_cells_le_0
| op_load_load_leading_u16_cells_le_1
| op_load_load_leading_u16_cells_le_2
| op_load_load_leading_u16_cells_le_3
| op_load_load_leading_u64_cell
| op_load_load_picked_leading_u16
| op_load_load_picked_leading_u16_u8_high
| op_load_load_picked_leading_u16_u8_low
| op_load_load_picked_flag
| op_load_load_picked_leading_u8_rem
| op_load_load_picked_leading_u8_rem_diff
| op_load_res
| op_load_is_sign
| op_load_is_i32
| op_load_degree_helper
| op_load_memory_table_lookup_stack_read : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_load_memory_table_lookup_heap_read1 : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_load_memory_table_lookup_heap_read2 : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_load_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols
| op_load_address_within_allocated_pages_helper

(* cells from op_memory_grow.rs. Circuits and range axioms are in OpMemoryGrow.v *)
| op_memory_grow_grow_size
| op_memory_grow_result
| op_memory_grow_current_maximal_diff
| op_memory_grow_success
| op_memory_grow_memory_table_lookup_stack_read : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_memory_grow_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_memory_size.rs. Circuits and range axioms are in OpMemorySize.v *)
| op_memory_size_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_rel.rs.  Circuits and range axioms are in OpRel.v *)
| op_rel_is_i32
| op_rel_is_sign
| op_rel_lhs_u16_le0
| op_rel_lhs_u16_le1
| op_rel_lhs_u16_le2
| op_rel_lhs_u16_le3
| op_rel_lhs_u64
| op_rel_lhs_flag_bit
| op_rel_lhs_flag_rem
| op_rel_lhs_flag_rem_diff
| op_rel_rhs_u16_le0
| op_rel_rhs_u16_le1
| op_rel_rhs_u16_le2
| op_rel_rhs_u16_le3
| op_rel_rhs_u64
| op_rel_rhs_flag_bit
| op_rel_rhs_flag_rem
| op_rel_rhs_flag_rem_diff
| op_rel_diff_u16_le0
| op_rel_diff_u16_le1
| op_rel_diff_u16_le2
| op_rel_diff_u16_le3
| op_rel_diff_u64
| op_rel_diff_inv
| op_rel_res_is_eq
| op_rel_res_is_lt
| op_rel_res_is_gt
| op_rel_op_is_eq
| op_rel_op_is_ne
| op_rel_op_is_lt
| op_rel_op_is_gt
| op_rel_op_is_le
| op_rel_op_is_ge
| op_rel_l_pos_r_pos 
| op_rel_l_pos_r_neg
| op_rel_l_neg_r_pos
| op_rel_l_neg_r_neg
| op_rel_memory_table_lookup_stack_read_lhs : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_rel_memory_table_lookup_stack_read_rhs : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_rel_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_return.rs.  Circuits and range axioms are in OpReturn.v *)
| op_return_keep
| op_return_drop
| op_return_is_i32
| op_return_value_u64_cell
| op_return_memory_table_lookup_stack_read : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_return_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols   
    
(* cells from op_select.rs. Circuits and range axioms are in OpSelect.v *)
| op_select_cond
| op_select_cond_inv
| op_select_val1
| op_select_val2
| op_select_res
| op_select_is_i32
| op_select_memory_table_lookup_stack_read_cond : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_select_memory_table_lookup_stack_read_val2 : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_select_memory_table_lookup_stack_read_val1 : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_select_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_store.rs. Circuits and range axioms are in OpStore.v *)
| op_store_opcode_store_offset
| op_store_load_block_index
| op_store_load_block_inner_pos_bits_0
| op_store_load_block_inner_pos_bits_1
| op_store_load_block_inner_pos_bits_2
| op_store_load_block_inner_pos
| op_store_is_cross_block
| op_store_cross_block_rem
| op_store_cross_block_rem_diff
| op_store_len
| op_store_len_modulus
| op_store_load_tailing
| op_store_load_tailing_diff
| op_store_load_picked_u64_cell
| op_store_load_picked_u16_cells_le_0
| op_store_load_picked_u16_cells_le_1
| op_store_load_picked_u16_cells_le_2
| op_store_load_picked_u16_cells_le_3
| op_store_load_picked_byte_proof
| op_store_load_leading
| op_store_store_value_u64_cell
| op_store_store_value_u16_cells_le_0
| op_store_store_value_u16_cells_le_1
| op_store_store_value_u16_cells_le_2
| op_store_store_value_u16_cells_le_3
| op_store_store_value_wrapped
| op_store_is_one_byte
| op_store_is_two_bytes
| op_store_is_four_bytes
| op_store_is_eight_bytes
| op_store_is_i32
| op_store_memory_table_lookup_stack_read_val : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_store_memory_table_lookup_stack_read_pos : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_store_memory_table_lookup_heap_read1 : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_store_memory_table_lookup_heap_read2 : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_store_memory_table_lookup_heap_write1 : AllocatedMemoryTableLookupWriteCell -> etable_cols
| op_store_memory_table_lookup_heap_write2 : AllocatedMemoryTableLookupWriteCell -> etable_cols
| op_store_unchanged_value
| op_store_store_value_tailing_u16_u8_high
| op_store_store_value_tailing_u16_u8_low
| op_store_address_within_allocated_pages_helper

(* cells from op_test.rs. Circuits and range axioms are in OpTest.v *)
| op_test_is_i32_cell
| op_test_res_cell
| op_test_value_cell
| op_test_value_inv_cell
| op_test_memory_table_lookup_stack_read : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_test_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols

(* cells from op_unary.rs. Circuits and range axioms are in OpUnary.v *)
| op_unary_operand_inv
| op_unary_bits
| op_unary_operand_is_zero
| op_unary_is_ctz
| op_unary_is_clz
| op_unary_is_popcnt
| op_unary_is_i32
| op_unary_aux1
| op_unary_aux2
| op_unary_ctz_degree_helper
| op_unary_memory_table_lookup_stack_read : AllocatedMemoryTableLookupReadCell -> etable_cols
| op_unary_memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell -> etable_cols
.

Parameter etable_values : etable_cols -> Z -> Z.
Parameter etable_numRow : Z.
Axiom etable_numRow_le_common : etable_numRow <= common.

Record EventTableOpcodeConfig := {
    config_mops : Z;
    config_jops : Z;
    config_sp_diff : Z;
    config_allocated_memory_pages_diff :   Z;
    config_next_frame_id :          option Z;
    config_next_iid :               option Z;
    config_next_fid :               option Z;
    config_opcode :                        Z;
}.

Definition opcode_config (cls : OpcodeClass) (i : Z) :=
  match cls with
  | Bin        => {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := 1; 
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 Bin) OPCODE_CLASS_SHIFT
                     + (etable_values op_bin_is_add i) * Z.shiftl 0 OPCODE_ARG0_SHIFT
                     + (etable_values op_bin_is_sub i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_bin_is_mul i) * Z.shiftl 2 OPCODE_ARG0_SHIFT
                     + (etable_values op_bin_is_div_u i) * Z.shiftl 3 OPCODE_ARG0_SHIFT
                     + (etable_values op_bin_is_rem_u i) * Z.shiftl 4 OPCODE_ARG0_SHIFT
                     + (etable_values op_bin_is_div_s i) * Z.shiftl 5 OPCODE_ARG0_SHIFT
                     + (etable_values op_bin_is_rem_s i) * Z.shiftl 6 OPCODE_ARG0_SHIFT
                     + (etable_values op_bin_is_i32 i) * Z.shiftl 1 OPCODE_ARG1_SHIFT |}
  | BinBit     => {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := 1; 
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 BinBit) OPCODE_CLASS_SHIFT
                     + (etable_values op_bin_bit_op_class i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_bin_bit_is_i32 i) * Z.shiftl 1 OPCODE_ARG1_SHIFT |}
  | BinShift   => {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := 1; 
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 BinShift) OPCODE_CLASS_SHIFT
                     + (etable_values op_bin_shift_is_shl i) * Z.shiftl 0 OPCODE_ARG0_SHIFT
                     + (etable_values op_bin_shift_is_shr_u i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_bin_shift_is_shr_s i) * Z.shiftl 2 OPCODE_ARG0_SHIFT
                     + (etable_values op_bin_shift_is_rotl i) * Z.shiftl 3 OPCODE_ARG0_SHIFT
                     + (etable_values op_bin_shift_is_rotr i) * Z.shiftl 4 OPCODE_ARG0_SHIFT
                     + (etable_values op_bin_shift_is_i32 i) * Z.shiftl 1 OPCODE_ARG1_SHIFT |}
  | BrIfEqz  =>   {| config_mops := 
                     (etable_values op_br_if_eqz_cond_is_zero_cell i) 
                   * (etable_values op_br_if_eqz_keep_cell i);
                     config_jops := 0;
                     config_sp_diff := 1
                   + (etable_values op_br_if_eqz_cond_is_zero_cell i)
                   * (etable_values op_br_if_eqz_drop_cell i);
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := 
                     Some ((etable_values op_br_if_eqz_cond_is_zero_cell i)
                   * (etable_values op_br_if_eqz_dst_pc_cell i)
                   + (etable_values op_br_if_eqz_cond_is_not_zero_cell i)
                   * (etable_values iid_cell i + 1)); 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 BrIfEqz) OPCODE_CLASS_SHIFT
                     + (etable_values op_br_if_eqz_drop_cell i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_br_if_eqz_keep_cell i) * Z.shiftl 1 OPCODE_ARG1_SHIFT
                     + (etable_values op_br_if_eqz_dst_pc_cell i) |}
  | BrIf  =>      {| config_mops := 
                     (etable_values op_br_if_cond_is_not_zero_cell i) 
                   * (etable_values op_br_if_keep_cell i);
                     config_jops := 0;
                     config_sp_diff := 1
                   + (etable_values op_br_if_cond_is_not_zero_cell i)
                   * (etable_values op_br_if_drop_cell i);
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := 
                     Some ((etable_values op_br_if_cond_is_not_zero_cell i)
                   * (etable_values op_br_if_dst_pc_cell i)
                   + (etable_values op_br_if_cond_is_zero_cell i)
                   * (etable_values iid_cell i + 1)); 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 BrIf) OPCODE_CLASS_SHIFT
                     + (etable_values op_br_if_drop_cell i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_br_if_keep_cell i) * Z.shiftl 1 OPCODE_ARG1_SHIFT
                     + (etable_values op_br_if_dst_pc_cell i) |}
  | BrTable  =>      {| config_mops := etable_values op_br_table_keep i;
                     config_jops := 0;
                     config_sp_diff := 1
                   + (etable_values op_br_table_drop i);
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := 
                     Some (etable_values op_br_table_dst_iid i); 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 BrTable) OPCODE_CLASS_SHIFT
                     + (etable_values op_br_table_targets_len i) |}
  | Br  =>        {| config_mops := etable_values op_br_keep_cell i;
                     config_jops := 0;
                     config_sp_diff := etable_values op_br_drop_cell i;
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := 
                     Some (etable_values op_br_dst_pc_cell i); 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 Br) OPCODE_CLASS_SHIFT
                     + (etable_values op_br_drop_cell i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_br_keep_cell i) * Z.shiftl 1 OPCODE_ARG1_SHIFT
                     + (etable_values op_br_dst_pc_cell i) |}
  | CallIndirect => {| config_mops := 0;
                     config_jops := JTableModel.encode_jops 0 1;
                     config_sp_diff := 1;
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := Some (etable_values eid_cell i); 
                     config_next_iid := Some(0); 
                     config_next_fid := Some (etable_values op_call_indirect_func_index i);
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 CallIndirect) OPCODE_CLASS_SHIFT
                     + (etable_values op_call_indirect_type_index i) * Z.shiftl 1 OPCODE_ARG0_SHIFT |}
  | Call  =>      {| config_mops := 0;
                     config_jops := JTableModel.encode_jops 0 1;
                     config_sp_diff := 0;
                     config_allocated_memory_pages_diff := 0;
                     config_next_frame_id := Some (etable_values eid_cell i); 
                     config_next_iid := Some 0;
                     config_next_fid := Some (etable_values op_call_index i);
                     config_opcode := Z.shiftl (OpcodeClass_u64 Call) OPCODE_CLASS_SHIFT
                                      + (etable_values op_call_index i) * Z.shiftl 1 OPCODE_ARG0_SHIFT |}
  | Const  =>     {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := -1;
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 Const) OPCODE_CLASS_SHIFT
                     + (etable_values op_const_is_i32 i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_const_value i) |}
  | Conversion => {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := 0;
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 Conversion) OPCODE_CLASS_SHIFT
                     + (encode_conversion
                         (etable_values op_conversion_sign_op i)
                         (etable_values op_conversion_value_type_is_i32 i)
                         (etable_values op_conversion_value_is_i8 i)
                         (etable_values op_conversion_value_is_i16 i)
                         (etable_values op_conversion_value_is_i32 i)
                         (etable_values op_conversion_value_is_i64 i)
                         (etable_values op_conversion_res_is_i32 i)
                         (etable_values op_conversion_res_is_i64 i)) |}
  | Drop  =>      {| config_mops := 0;
                     config_jops := 0;
                     config_sp_diff := 1;
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 Drop) OPCODE_CLASS_SHIFT |}
  | GlobalGet  => {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := -1;
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 GlobalGet) OPCODE_CLASS_SHIFT
                     + (etable_values op_global_get_idx_cell i) |}
  | GlobalSet  => {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := 1;
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 GlobalSet) OPCODE_CLASS_SHIFT
                     + (etable_values op_global_set_idx_cell i) |}
  | Load  =>      {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := 0; 
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 Load) OPCODE_CLASS_SHIFT
                     + (etable_values op_load_is_i32 i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_load_is_eight_bytes i * 6
                        + etable_values op_load_is_four_bytes i * 4
                        + etable_values op_load_is_two_bytes i * 2
                        + etable_values op_load_is_sign i + 1) * Z.shiftl 1 OPCODE_ARG1_SHIFT
                     + (etable_values op_load_opcode_load_offset i) |}
  | LocalGet  =>  {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := -1; 
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 LocalGet) OPCODE_CLASS_SHIFT
                     + (etable_values op_local_get_is_i32_cell i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_local_get_offset_cell i) |}
  | LocalSet  =>  {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := 1; 
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 LocalSet) OPCODE_CLASS_SHIFT
                     + (etable_values op_local_set_is_i32_cell i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_local_set_offset_cell i) |}
  | LocalTee  =>  {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := 0; 
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 LocalTee) OPCODE_CLASS_SHIFT
                     + (etable_values op_local_tee_is_i32_cell i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_local_tee_offset_cell i) |}
  | MemoryGrow => {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := 0; 
                     config_allocated_memory_pages_diff := 
                     (etable_values op_memory_grow_success i) 
                   * (etable_values op_memory_grow_grow_size i); 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 MemoryGrow) OPCODE_CLASS_SHIFT |}  
  | MemorySize => {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := -1; 
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 MemorySize) OPCODE_CLASS_SHIFT |}
  | Rel     =>    {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := 1; 
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 Rel) OPCODE_CLASS_SHIFT
                     + (etable_values op_rel_op_is_eq i) * Z.shiftl 0 OPCODE_ARG0_SHIFT
                     + (etable_values op_rel_op_is_ne i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_rel_op_is_gt i) 
                     * (1 - etable_values op_rel_is_sign i) * Z.shiftl 3 OPCODE_ARG0_SHIFT
                     + (etable_values op_rel_op_is_ge i) 
                        * (1 - etable_values op_rel_is_sign i) * Z.shiftl 5 OPCODE_ARG0_SHIFT
                     + (etable_values op_rel_op_is_lt i) 
                        * (1 - etable_values op_rel_is_sign i) * Z.shiftl 7 OPCODE_ARG0_SHIFT
                     + (etable_values op_rel_op_is_le i) 
                        * (1 - etable_values op_rel_is_sign i) * Z.shiftl 9 OPCODE_ARG0_SHIFT
                     + (etable_values op_rel_op_is_gt i) 
                        * (etable_values op_rel_is_sign i) * Z.shiftl 2 OPCODE_ARG0_SHIFT
                     + (etable_values op_rel_op_is_ge i) 
                        * (etable_values op_rel_is_sign i) * Z.shiftl 4 OPCODE_ARG0_SHIFT
                     + (etable_values op_rel_op_is_lt i) 
                        * (etable_values op_rel_is_sign i) * Z.shiftl 6 OPCODE_ARG0_SHIFT
                     + (etable_values op_rel_op_is_le i) 
                        * (etable_values op_rel_is_sign i) * Z.shiftl 8 OPCODE_ARG0_SHIFT
                       + (etable_values op_rel_is_i32 i) * Z.shiftl 1 OPCODE_ARG1_SHIFT |}
  | Return  =>    {| config_mops := etable_values op_return_keep i;
                     config_jops := JTableModel.encode_jops 1 0;
                     config_sp_diff := etable_values op_return_drop i;
                     config_allocated_memory_pages_diff := 0;
                     config_next_frame_id := Some (etable_values frame_id_cell (i+1)); 
                     config_next_iid := Some (etable_values iid_cell (i+1));
                     config_next_fid := Some (etable_values fid_cell (i+1));
                     config_opcode := Z.shiftl (OpcodeClass_u64 Return) OPCODE_CLASS_SHIFT
                                      + (etable_values op_return_drop i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                                      + (etable_values op_return_keep i) * Z.shiftl 1 OPCODE_ARG1_SHIFT  |}
  | Select  =>    {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := 2; 
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 Select) OPCODE_CLASS_SHIFT |}   
  | Store  =>     {| config_mops := 1 + 
                     (etable_values op_store_is_cross_block i);
                     config_jops := 0;
                     config_sp_diff := 2; 
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 Store) OPCODE_CLASS_SHIFT
                     + (etable_values op_store_is_i32 i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_store_is_eight_bytes i * 3
                        + etable_values op_store_is_four_bytes i * 2
                        + etable_values op_store_is_two_bytes i * 1 + 1) * Z.shiftl 1 OPCODE_ARG1_SHIFT
                     + (etable_values op_store_opcode_store_offset i) |}  
  | Test  =>      {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := 0; 
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 Test) OPCODE_CLASS_SHIFT
                     + 0 * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_test_is_i32_cell i) * Z.shiftl 1 OPCODE_ARG1_SHIFT |}           
  | Unary  =>     {| config_mops := 1;
                     config_jops := 0;
                     config_sp_diff := 0; 
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode :=
                       Z.shiftl (OpcodeClass_u64 Unary) OPCODE_CLASS_SHIFT
                     + (etable_values op_unary_is_i32 i) * Z.shiftl 1 OPCODE_ARG1_SHIFT
                     + (etable_values op_unary_is_ctz i) * Z.shiftl 0 OPCODE_ARG0_SHIFT
                     + (etable_values op_unary_is_clz i) * Z.shiftl 1 OPCODE_ARG0_SHIFT
                     + (etable_values op_unary_is_popcnt i) * Z.shiftl 2 OPCODE_ARG0_SHIFT |}
  | _      =>     {| config_mops := 0;
                     config_jops := 0;
                     config_sp_diff := 0; 
                     config_allocated_memory_pages_diff := 0; 
                     config_next_frame_id := None; 
                     config_next_iid := None; 
                     config_next_fid := None;
                     config_opcode := 0 |}  (* todo *)
  end.

Definition etable := mkTable etable_cols etable_numRow etable_values.

Definition iscommon c := forall i, 0 <= etable_values c i < common.
Definition isbit c := forall i, etable_values c i = 0 \/ etable_values c i = 1.
Definition is8 c := forall i, 0 <= etable_values c i < 2^8.
Definition is16 c := forall i, 0 <= etable_values c i < 2^16.
Definition is64 c := forall i,  0 <= etable_values c i < Wasm_int.Int64.modulus.
Definition is64_from16 c64 c16_0 c16_1 c16_2 c16_3 := forall i,
      etable_values c64 i = (etable_values c16_0 i)
                          + (etable_values c16_1 i) * (2^16)
                          + (etable_values c16_2 i) * (2^32)
                          + (etable_values c16_3 i) * (2^48).

Axiom enabled_bit : isbit enabled_cell.
Axiom ops_bit : forall cls, isbit (ops_cell cls).
Axiom rest_mops_common : iscommon rest_mops_cell.                     
Axiom rest_jops_common : iscommon  rest_jops_cell.
Axiom input_index_common : iscommon  input_index_cell.
Axiom context_input_index_common : iscommon  context_input_index_cell.
Axiom context_output_index_common: iscommon context_output_index_cell.
Axiom external_host_call_index_common: iscommon external_host_call_index_cell. 
Axiom sp_common: iscommon sp_cell.
Axiom mpages_common: iscommon mpages_cell.
Axiom frame_id_common: iscommon frame_id_cell.
Axiom eid_common: iscommon eid_cell. 
Axiom fid_common: iscommon fid_cell.
Axiom iid_common: iscommon iid_cell.
Axiom maximal_memory_pages_common: iscommon maximal_memory_pages_cell.

(* Range axioms to deal with mops *)
Axiom op_br_if_eqz_cond_is_zero_cell_bit : isbit op_br_if_eqz_cond_is_zero_cell.
Axiom op_br_if_eqz_keep_cell_bit : isbit op_br_if_eqz_keep_cell.
Axiom op_br_if_cond_is_not_zero_cell_bit : isbit op_br_if_cond_is_not_zero_cell.
Axiom op_br_if_keep_cell_bit : isbit op_br_if_keep_cell.
Axiom op_br_keep_cell_bit : isbit op_br_keep_cell.
Axiom op_br_table_keep_bit : isbit op_br_table_keep.
Axiom op_return_keep_cell_bit : isbit op_return_keep.
Axiom op_store_is_cross_block_bit : isbit op_store_is_cross_block.

(* These two axioms represent lines 78 and 85 in etable/assign.rs. *)
Axiom rest_mops_terminates :
  etable_values rest_mops_cell etable_numRow = 0.
Axiom rest_jops_terminates :  
  etable_values rest_jops_cell etable_numRow = 0.

(* These lines represent the fixed assignments in etable/assign.rs lines 169-173. *)
Definition DEFAULT_VALUE_STACK_LIMIT := 4096.
Axiom initial_sp : etable_values sp_cell 0 = DEFAULT_VALUE_STACK_LIMIT-1.
Axiom initial_frame_id : etable_values frame_id_cell 0 = 0.
Axiom initial_eid : etable_values eid_cell 0 = 1.
Axiom initial_iid : etable_values iid_cell 0 = 1.

(* Represents the `constraint_rest_mops_permutation` constraint from
     mtable/assign.rs (line 49). *)
Axiom constraint_rest_mops : etable_values rest_mops_cell 0
                               = MTableModel.mtable_values MTableModel.rest_mops_cell 0.

(* Represents the `constraint_to_etable_jops` constraint from
     jtable/assign.rs (line 210). *)
Axiom constraint_rest_jops : etable_values rest_jops_cell 0
                               = JTableModel.jtable_values JTableModel.data_col JTableModel.JtableOffsetRest.

(* These definitions are written at the higher level of abstraction provided by the "allocator" code.
   That is, we assume rows of "logical" cells (which are returned by the allocator, and 
   when we write `get c 1` the 1 means means `c.next_expr(meta)`, as opposed to a rotation of 1 in 
   the underlying physical table. 

   We omit all mentions of step_sel, since it will be set for each "logical" cell.
*)

(* "c1. enable seq" *)
Axiom gate_c1 :
  gate etable
    (fun get =>
       get enabled_cell 1 * (get enabled_cell 0 - 1)
       :: nil
    ).

(* The following Axioms represent gates written using the `sum_ops_expr_with_init` macro,
   so they are paraphrased less literally.*)

(* compare "c5a. rest_mops change" *)
Axiom rest_mops_change_enabled : forall i idx,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  etable_values (ops_cell idx) i = 1 ->
  etable_values rest_mops_cell i
    = (etable_values rest_mops_cell (i+1) + config_mops (opcode_config idx i)).

Axiom rest_mops_change_disabled : forall i,
  0 <= i ->
  etable_values enabled_cell i = 0 ->
  etable_values rest_mops_cell i
    = etable_values rest_mops_cell (i+1).

(* compare "c5b. rest_jops change" *)
Axiom rest_jops_change_enabled : forall i idx,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  etable_values (ops_cell idx) i = 1 ->
  etable_values rest_jops_cell i
    = (etable_values rest_jops_cell (i+1) + config_jops (opcode_config idx i)).

Axiom rest_jops_change_disabled : forall i,
  0 <= i ->
  etable_values enabled_cell i = 0 ->
  etable_values rest_jops_cell i
    = etable_values rest_jops_cell (i+1).

(* Compare "c5e. sp change" *)
Axiom sp_change : forall i idx,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  etable_values (ops_cell idx) i = 1 ->
  etable_values sp_cell (i+1)
    = (etable_values sp_cell i + config_sp_diff (opcode_config idx i)).

(* Compare "c5f. mpages change" *)
Axiom mpages_change : forall i idx,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  etable_values (ops_cell idx) i = 1 ->
  etable_values mpages_cell (i+1)
    = (etable_values mpages_cell i + config_allocated_memory_pages_diff (opcode_config idx i)).

(* compare "c6a. eid change" *)
Axiom eid_change : forall i,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  etable_values eid_cell (i+1) = (etable_values eid_cell i) + 1.

(* compare "c6a. eid change" *)
Axiom iid_change : forall i idx,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  etable_values (ops_cell idx) i = 1 ->
  etable_values iid_cell (i+1)
    = match config_next_iid (opcode_config idx i) with 
      | None => etable_values iid_cell i + 1
      | Some(iid) => iid
      end.

(* compare "c6b. fid change" *)
Axiom fid_change : forall i idx,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  etable_values (ops_cell idx) i = 1 ->
  etable_values fid_cell (i+1)
    = match config_next_fid (opcode_config idx i) with 
      | None => etable_values fid_cell i
      | Some(fid) => fid
      end.

(* compare "c6d. frame_id change" *)
Axiom frame_id_change : forall i idx,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  etable_values (ops_cell idx) i = 1 ->
  etable_values frame_id_cell (i+1)
    = match config_next_frame_id (opcode_config idx i) with 
      | None => etable_values frame_id_cell i
      | Some(id) => id
      end.

Axiom itable_lookup_encode : forall i idx,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  etable_values (ops_cell idx) i = 1 ->
  etable_values itable_lookup_cell i = 
  encode_instruction_table_entry 
    (etable_values fid_cell i)
    (etable_values iid_cell i)
    (config_opcode (opcode_config idx i)).

Axiom itable_lookup_in_itable : forall i,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  exists j, 
    etable_values itable_lookup_cell i =
    image_table_values col j.

Require Import RTableModel.
(*  "c8d. pow_table_lookup in pow_table" *)
Axiom c8d : forall i, 
    0 <= i ->
    in_op_table Power_index 0 (etable_values pow_table_lookup_power_cell i) (etable_values pow_table_lookup_modulus_cell i).

Require Import BitTableModel.

(* "c8f: bit_table_lookup in bit_table" *)
Axiom c8f : forall i,
  0 <= i ->
  exists j,
    0 <= j
    /\ value bit_table block_sel (j + 1) = 1
    /\ value bit_table op j              = etable_values (bit_table_lookup_cells ABTLC_op) i
    /\ value bit_table val_l j           = etable_values (bit_table_lookup_cells ABTLC_left) i
    /\ value bit_table val_r j           = etable_values (bit_table_lookup_cells ABTLC_right) i
    /\ value bit_table val_res j         = etable_values (bit_table_lookup_cells ABTLC_result) i.

(* "c8c. jtable_lookup in jtable" *)
Axiom c8c : forall i,
  0 <= i -> JTableModel.in_jtable (etable_values jtable_lookup_cell i).

(* compare "c9. maximal memory pages consistent" *)
Axiom maximal_memory_pages_change : forall i,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  etable_values maximal_memory_pages_cell (i+1) = etable_values maximal_memory_pages_cell i.

(* Translation of the constraints for alloc_memory_table_lookup_read_cell *)
Record alloc_memory_table_lookup_read_cell (c : AllocatedMemoryTableLookupReadCell -> etable_cols) (eid location_type offset is_i32 value enabled : (etable_cols -> Z) -> Z) := {
    read_start_eid_diff_common : iscommon (c AMTLRC_start_eid_diff_cell);
    read_end_eid_diff_common   : iscommon (c AMTLRC_end_eid_diff_cell);

    read_lookup: forall i, exists j,
       0 <= j
    /\ MTableModel.mtable_values MTableModel.start_eid_cell j = etable_values (c AMTLRC_start_eid_cell) i
    /\ MTableModel.mtable_values MTableModel.end_eid_cell j   = etable_values (c AMTLRC_end_eid_cell) i
    /\ MTableModel.mtable_values MTableModel.encode_cell j    = etable_values (c AMTLRC_encode_cell) i
    /\ MTableModel.mtable_values MTableModel.value_u64_cell j = etable_values (c AMTLRC_value_cell) i;
        
    read_gate: 
    forall i, 0 <= i ->
      let get c := etable_values c i in
      (enabled get)*(eid get - get (c AMTLRC_start_eid_cell) - get (c AMTLRC_start_eid_diff_cell) - 1) = 0
      /\ (enabled get)*(eid get + get (c AMTLRC_end_eid_diff_cell) - get (c AMTLRC_end_eid_cell)) = 0
      /\ (enabled get)*((MTableModel.encode_memory_table_entry (offset get) (location_type get) (is_i32 get)) - get (c AMTLRC_encode_cell)) = 0
      /\ (enabled get)*(get (c AMTLRC_value_cell) - (value get)) = 0 
  }.

(* Translation of the constraints for alloc_memory_table_lookup_read_cell_with_value *)
Record alloc_memory_table_lookup_read_cell_with_value (c : AllocatedMemoryTableLookupReadCell -> etable_cols) (eid location_type offset is_i32 enabled : (etable_cols -> Z) -> Z) := {
    readv_start_eid_diff_common : iscommon (c AMTLRC_start_eid_diff_cell);
    readv_end_eid_diff_common   : iscommon (c AMTLRC_end_eid_diff_cell);

    readv_lookup: forall i, exists j,
       0 <= j
    /\ MTableModel.mtable_values MTableModel.start_eid_cell j = etable_values (c AMTLRC_start_eid_cell) i
    /\ MTableModel.mtable_values MTableModel.end_eid_cell j   = etable_values (c AMTLRC_end_eid_cell) i
    /\ MTableModel.mtable_values MTableModel.encode_cell j    = etable_values (c AMTLRC_encode_cell) i
    /\ MTableModel.mtable_values MTableModel.value_u64_cell j = etable_values (c AMTLRC_value_cell) i;
        
    readv_gate: 
    forall i, 0 <= i ->
      let get c := etable_values c i in
      (enabled get)*(eid get - get (c AMTLRC_start_eid_cell) - get (c AMTLRC_start_eid_diff_cell) - 1) = 0
      /\ (enabled get)*(eid get + get (c AMTLRC_end_eid_diff_cell) - get (c AMTLRC_end_eid_cell)) = 0
      /\ (enabled get)*((MTableModel.encode_memory_table_entry (offset get) (location_type get) (is_i32 get)) - get (c AMTLRC_encode_cell)) = 0
  }.

(* Translation of the constraints for alloc_memory_table_lookup_write_cell *)
Record alloc_memory_table_lookup_write_cell  (c : AllocatedMemoryTableLookupWriteCell -> etable_cols) (eid location_type offset is_i32 value enabled : (etable_cols -> Z) -> Z) := {
    write_start_eid_cell: Z;
    write_end_eid_cell: Z;
    write_encode_cell : Z;
    write_value_cell: Z;

    write_lookup: forall i, exists j,
       0 <= j
    /\ MTableModel.mtable_values MTableModel.start_eid_cell j = etable_values (c AMTLWC_start_eid_cell) i
    /\ MTableModel.mtable_values MTableModel.end_eid_cell j   = etable_values (c AMTLWC_end_eid_cell) i
    /\ MTableModel.mtable_values MTableModel.encode_cell j    = etable_values (c AMTLWC_encode_cell) i
    /\ MTableModel.mtable_values MTableModel.value_u64_cell j = etable_values (c AMTLWC_value_cell) i;

    write_gate:
    forall i, 0 <= i ->
      let get c := etable_values c i in      
    (enabled get)*((MTableModel.encode_memory_table_entry (offset get) (location_type get) (is_i32 get)) - get (c AMTLWC_encode_cell)) = 0
    /\ (enabled get)*(get (c AMTLWC_start_eid_cell) - (eid get)) = 0
    /\ (enabled get)*(get (c AMTLWC_value_cell) - (value get)) = 0
  }.

(* Translation of the constraints for alloc_memory_table_lookup_write_cell_with_value *)
Record alloc_memory_table_lookup_write_cell_with_value  (c : AllocatedMemoryTableLookupWriteCell -> etable_cols) (eid location_type offset is_i32 enabled : (etable_cols -> Z) -> Z) := {
    writev_start_eid_cell: Z;
    writev_end_eid_cell: Z;
    writev_encode_cell : Z;
    writev_value_cell: Z;

    writev_lookup: forall i, exists j,
       0 <= j
    /\ MTableModel.mtable_values MTableModel.start_eid_cell j = etable_values (c AMTLWC_start_eid_cell) i
    /\ MTableModel.mtable_values MTableModel.end_eid_cell j   = etable_values (c AMTLWC_end_eid_cell) i
    /\ MTableModel.mtable_values MTableModel.encode_cell j    = etable_values (c AMTLWC_encode_cell) i
    /\ MTableModel.mtable_values MTableModel.value_u64_cell j = etable_values (c AMTLWC_value_cell) i;

    writev_gate:
    forall i, 0 <= i ->
      let get c := etable_values c i in      
    (enabled get)*((MTableModel.encode_memory_table_entry (offset get) (location_type get) (is_i32 get)) - get (c AMTLWC_encode_cell)) = 0
    /\ (enabled get)*(get (c AMTLWC_start_eid_cell) - (eid get)) = 0
  }.

(* This could be defined as a huge if-statement, testing each of the ops_cell columns and returning the first one that is nonzero. *)
Parameter class_of_row : Z -> OpcodeClass.

(* compare "c4. opcode_bit lvl sum equals to 1" *)
Axiom class_of_row_op : forall i c,
    etable_values enabled_cell i = 1 ->
    (etable_values (ops_cell c) i = 1 <-> class_of_row i = c).

(**** Assumptions. These axioms do not directly correspond to lines of circuit, but rather about other parts of the system. *)

(* We use this axiom to prove that the address pushed by call instruction (iid+1) is still 
   in the common range. 
 
   The issue would be a function that is extremely long (exactly 2^k-1
   instructions, ie. 262143 instructions for k=18) and ends with a call. 
   However, the Wasm typechecker ensures that no function ends on call, 
   there will be a return instruction after it, so iid+1 must also be a valid number. *)
Axiom call_iid_small : forall i fid iid opcode,
    0 <= fid < common ->
    0 <= iid < common ->
    ImageTableModel.in_itable (ImageTableModel.encode_instruction_table_entry fid iid opcode) ->
    (opcode = config_opcode (opcode_config Call i)
     \/ opcode = config_opcode (opcode_config CallIndirect i)) ->
    0 <= iid+1 < common.
