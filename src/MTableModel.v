(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import ImageTableModel.

Open Scope Z_scope.

(* encoding *)

Definition encode_memory_table_entry offset location_type is_i32 :=
  let IS_I32_SHIFT := 0 in
  let LOCATION_TYPE_SHIFT := IS_I32_SHIFT + 1 in
  let OFFSET_SHIFT := LOCATION_TYPE_SHIFT + COMMON_RANGE_OFFSET in
  let END_SHIFT := OFFSET_SHIFT + COMMON_RANGE_OFFSET in

  (offset * (Z.shiftl 1 OFFSET_SHIFT)
      + location_type * (Z.shiftl 1 LOCATION_TYPE_SHIFT)
      + is_i32 * (Z.shiftl 1 IS_I32_SHIFT)) mod field_order.

(* mtable/mod.rs *)

 Definition LocationType_Stack := 1.
 Definition LocationType_Heap := 2.
 Definition LocationType_Global := 3.

Inductive mtable_cols :=
(* | entry_sel *) (* Omitted because we work at the "allocator" abstraction level *)
| enabled_cell
| is_stack_cell
| is_heap_cell
| is_global_cell
| is_next_same_ltype_cell
| is_next_same_offset_cell
| is_mutable_cell (* added _cell for consistency *)
 
| is_i32_cell
| is_i64_cell
| is_init_cell
 
| start_eid_cell
| end_eid_cell
| eid_diff_cell
| rest_mops_cell
 
| offset_align_left_cell
| offset_align_right_cell
| offset_cell
| offset_align_left_diff_cell
| offset_align_right_diff_cell
 
| offset_diff_cell
| offset_diff_inv_cell
| offset_diff_inv_helper_cell
| encode_cell
 | init_encode_cell
| value_u16_cells_le0
| value_u16_cells_le1
| value_u16_cells_le2
| value_u16_cells_le3
| value_u64_cell.

Parameter mtable_values : mtable_cols -> Z -> Z.
Parameter mtable_numRow : Z.
Axiom mtable_numRow_nonneg : 0 <= mtable_numRow.

Definition mtable := mkTable mtable_cols mtable_numRow mtable_values.

(* These definitions are written at the higher level of abstraction provided by the "allocator" code.
   That is, we assume rows of "logical" cells (which are returned by the allocator, and 
   when we write `get c 1` the 1 means means `c.next_expr(meta)`, as opposed to a rotation of 1 in 
   the underlying physical table. 

   We also omit all mentions of entry_sel, since it will be set for each "logical" cell.
*)

(* "mc1. enable seq" *)
Axiom gate_mc1 :
  gate mtable
    (fun get =>
       (get enabled_cell 0 - 1)
     * (get enabled_cell 1)
       :: nil).

(* "mc2. ltype unique" *)
Axiom gate_mc2 :
  gate mtable
    (fun get =>  (get is_global_cell 0)
                 + (get is_heap_cell 0)
                 + (get is_stack_cell 0)
                 - (get enabled_cell 0)
                     :: nil).
(* "mc3. ltype group" *)
Axiom gate_mc3 :
  gate mtable
    (fun get =>
          (get is_stack_cell 0 - 1) * (get is_stack_cell 1)
       :: (get is_heap_cell 0 - 1) * (get is_heap_cell 1) * (get is_stack_cell 0 - 1)
       :: nil).

(* "mc4a. is_next_same_ltype" *)
Axiom gate_mc4a :
  gate mtable
    (fun get =>
       ((get is_next_same_ltype_cell 0)
        - (get is_stack_cell 0) * (get is_stack_cell 1)
        - (get is_global_cell 0) * (get is_global_cell 1)
        - (get is_heap_cell 0) * (get is_heap_cell 1))
       :: nil).

(* "mc4b. is_next_same_offset" *)
Axiom gate_mc4b :
  pgate mtable
    (fun get =>
           (get is_next_same_offset_cell 0)
         * (get is_next_same_ltype_cell 0 - 1)
      :: (get is_next_same_offset_cell 0) * (get offset_diff_cell 0)
      :: (get offset_diff_cell 0) * (get offset_diff_inv_cell 0)
                    - (get offset_diff_inv_helper_cell 0)
      ::   (get is_next_same_offset_cell 0 - 1)
         * (get is_next_same_ltype_cell 0)
         * (get offset_diff_inv_helper_cell 0 - 1)
      :: nil).

(* "mc5. offset sort" *)
Axiom gate_mc5 :
  gate mtable
    (fun get =>
       ((get offset_cell 0) + (get offset_diff_cell 0)
                            - (get offset_cell 1))
                    * (get is_next_same_ltype_cell 0)
                        :: nil).
(* "mc6. eid sort" *)
Axiom gate_mc6 :
  gate mtable
    (fun get =>
         (get start_eid_cell 0
             + get eid_diff_cell 0
             + 1
             - get end_eid_cell 0)
    ::   (get end_eid_cell 0 - get start_eid_cell 1)
             * (get is_next_same_offset_cell 0)
    :: nil).

(* "mc7a. init" *)
Axiom gate_mc7 :
  gate mtable
    (fun get =>
      get is_init_cell 0 * get start_eid_cell 0
                (* offset_left_align <= offset && offset <= offset_right_align *)
      :: (get is_init_cell 0)
                    * (get offset_align_left_cell 0
                        + get offset_align_left_diff_cell 0
                        - get offset_cell 0)
      ::  (get is_init_cell 0)
                    * (get offset_cell 0 + get offset_align_right_diff_cell 0
                       - get offset_align_right_cell 0)
      :: nil).

(* "mc7b. global must has init (because of mutability check)." *)
Axiom gate_mc7b :
  gate mtable
    (fun get =>
       (get is_next_same_offset_cell 0 - 1)
       * get is_global_cell 1
       * (get is_init_cell 1 - 1)
           :: nil).

(* "mc7c. init encode." *)
Axiom gate_mc7c :
  gate mtable
    (fun get => 
       get is_init_cell 0
                    * (encode_init_memory_table_entry
                        (get is_stack_cell 0 * LocationType_Stack
                            + get is_heap_cell 0
                                * LocationType_Heap
                            + get is_global_cell 0
                                * LocationType_Global)
                         (get is_mutable_cell 0)
                         (get offset_align_left_cell 0)
                         (get offset_align_right_cell 0)
                         (get value_u64_cell 0))
                    - get init_encode_cell 0
                        :: nil).

Axiom init_memory_lookup : forall i e,
    mtable_values init_encode_cell i = e ->
    exists j, image_table_values col j = e.

(* "mc8. vtype" *)
Axiom gate_mc8 :
  gate mtable
    (fun get =>
         get is_i32_cell 0 + get is_i64_cell 0 - get enabled_cell 0
      :: get is_heap_cell 0  * get is_i32_cell 0
      :: get is_i32_cell 0
          * (get value_u16_cells_le2 0
             + get value_u16_cells_le3 0)
      :: get is_global_cell 0
         * get is_next_same_offset_cell 0
         * (get is_i32_cell 0 - get is_i32_cell 1)
      :: nil).

(* "mc9. value" *)
Axiom gate_mc9 :
  gate mtable
    (fun get =>
       (get value_u64_cell 0
        - (get value_u16_cells_le0 0)
        - (get value_u16_cells_le1 0) * (Z.shiftl 1 16)
        - (get value_u16_cells_le2 0) * (Z.shiftl 1 32)
        - (get value_u16_cells_le3 0) * (Z.shiftl 1 48))
         :: nil).

(* "mc10b. rest_mops" *)
Axiom gate_mc10b :
  gate mtable
    (fun get =>
          get is_init_cell 0
                    * (get rest_mops_cell 1 - get rest_mops_cell 0)
       :: (get is_init_cell 0 - 1)
                    * (get rest_mops_cell 1 + get enabled_cell 0
                        - get rest_mops_cell 0)
                        :: nil).

(* "mc10c. rest_mops decrease to zero" *)
Axiom gate_mc10c :
  gate mtable
    (fun get =>
       (get enabled_cell 0 - 1) * get rest_mops_cell 0
     :: nil).

(* "mc11. mutable" *)
Axiom gate_mc11 :
  gate mtable
    (fun get =>
        (get is_init_cell 0 - 1)
        * (get is_mutable_cell 0 - 1)
     :: (get is_mutable_cell 0 - get is_mutable_cell 1)
        * (get is_next_same_offset_cell 0)
     :: nil).

(* "mc12. lookup encode" *)
Axiom gate_mc12 :
  gate mtable
    (fun get =>
       (1 - get enabled_cell 0) * get encode_cell 0
     ::  encode_memory_table_entry
           (get offset_cell 0)
           (get is_stack_cell 0 * LocationType_Stack
               + get is_global_cell 0 * LocationType_Global
               + get is_heap_cell 0 * LocationType_Heap)
           (get is_i32_cell 0)
        - get encode_cell 0
            :: nil).

Definition iscommon c := forall i, 0 <= mtable_values c i < common.
Definition isbit c := forall i, mtable_values c i = 0 \/ mtable_values c i = 1.
Definition is16 c := forall i, 0 <= mtable_values c i < 2^16.

Axiom enabled_bit : isbit enabled_cell.
Axiom is_global_bit    : isbit is_global_cell.
Axiom is_heap_bit      : isbit is_heap_cell.
Axiom is_stack_bit     : isbit is_stack_cell.
Axiom is_next_same_ltype_bit      : isbit is_next_same_ltype_cell.
Axiom is_next_same_offset_bit     : isbit is_next_same_offset_cell.
Axiom is_mutable_bit     : isbit is_mutable_cell.

Axiom is_i32_bit     : isbit is_i32_cell.
Axiom is_i64_bit     : isbit is_i64_cell.
Axiom is_init_bit     : isbit is_init_cell.

Axiom start_eid_common : iscommon start_eid_cell.
Axiom end_eid_common : iscommon end_eid_cell.
Axiom eid_diff_common : iscommon eid_diff_cell.
Axiom rest_mops_common : iscommon rest_mops_cell.

Axiom offset_align_left_common  : iscommon offset_align_left_cell.
Axiom offset_align_right_common : iscommon offset_align_right_cell.
Axiom offset_align_left_diff_common  : iscommon offset_align_left_diff_cell.
Axiom offset_align_right_diff_common : iscommon offset_align_right_diff_cell.

Axiom offset_common  : iscommon offset_cell.
Axiom offset_diff_common  : iscommon offset_diff_cell.

Axiom value_u16_cells_le0_U16 : is16 value_u16_cells_le0.
Axiom value_u16_cells_le1_U16 : is16 value_u16_cells_le1.
Axiom value_u16_cells_le2_U16 : is16 value_u16_cells_le2.
Axiom value_u16_cells_le3_U16 : is16 value_u16_cells_le3.

(* Todo: review how we can justify this axiom, or if it is needed. *)
Axiom mtable_end : forall i,
    mtable_numRow <= i -> mtable_values enabled_cell i = 0.

