(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

(* This file contains lemmas about the refinement relation *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import Wasm.numerics.
Require        Wasm.datatypes.
Require Import Lia.

Require Import MTableModel MTable.
Require Export ETableModel.
Require Import ETable.
Require Export Relation.

Require Import Wasm.operations.

Lemma globals_update_stack : forall st a,
    wasm_globals (update_stack st a) = wasm_globals st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma globals_update_callstack : forall st a,
    wasm_globals (update_callstack st a) = wasm_globals st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma stack_update_stack : forall st a,
    wasm_stack (update_stack st a) = a.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma stack_update_callstack : forall st a,
    wasm_stack (update_callstack st a) = (wasm_stack st).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma memory_update_stack : forall st a,
    wasm_memory (update_stack st a) = wasm_memory st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma memory_update_callstack : forall st a,
    wasm_memory (update_callstack st a) = wasm_memory st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma pc_update_stack : forall st a,
    wasm_pc (update_stack st a) = wasm_pc st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma pc_update_callstack : forall st a,
    wasm_pc (update_callstack st a) = wasm_pc st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma callstack_update_stack : forall st a,
    wasm_callstack (update_stack st a) = wasm_callstack st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma stack_update_globals : forall st a,
    wasm_stack (update_globals st a) = wasm_stack st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma globals_update_globals : forall st a,
    wasm_globals (update_globals st a) = a.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma memory_update_globals : forall st a,
    wasm_memory (update_globals st a) = wasm_memory st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma pc_update_globals : forall st a,
    wasm_pc (update_globals st a) = wasm_pc st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma callstack_update_globals : forall st a,
    wasm_callstack (update_globals st a) = wasm_callstack st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma stack_update_memory : forall st a,
    wasm_stack (update_memory st a) = wasm_stack st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma globals_update_memory : forall st a,
    wasm_globals (update_memory st a) = wasm_globals st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma memory_update_memory : forall st a,
    wasm_memory (update_memory st a) = a.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma pc_update_memory : forall st a,
    wasm_pc (update_memory st a) = wasm_pc st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma callstack_update_memory : forall st a,
    wasm_callstack (update_memory st a) = wasm_callstack st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma callstack_update_callstack : forall st a,
    wasm_callstack (update_callstack st a) = a.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma pc_incr_iid : forall st,
    let (fid, iid) := wasm_pc st in
    wasm_pc (incr_iid st) = (fid, iid + 1).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma globals_incr_iid : forall st,
    wasm_globals (incr_iid st) = wasm_globals st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma memory_incr_iid : forall st,
    wasm_memory (incr_iid st) = wasm_memory st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma callstack_incr_iid : forall st,
    wasm_callstack (incr_iid st) = wasm_callstack st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma incr_iid_update_stack : forall st a,
    wasm_pc (incr_iid (update_stack st a)) = wasm_pc (incr_iid st).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma move_iid_update_stack : forall st a niid,
    wasm_pc (move_to_iid (update_stack st a) niid) = wasm_pc (move_to_iid st niid).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma pc_move_iid : forall st niid,
    let (fid, iid) := wasm_pc st in
    wasm_pc (move_to_iid st niid) = (fid, niid).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma globals_move_iid : forall st niid,
    wasm_globals (move_to_iid st niid) = wasm_globals st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma memory_move_iid : forall st niid,
    wasm_memory (move_to_iid st niid) = wasm_memory st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma callstack_move_iid : forall st niid,
    wasm_callstack (move_to_iid st niid) = wasm_callstack st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma pc_move_label : forall st l,
    wasm_pc (move_to_label st l) = l.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma globals_move_label : forall st l,
    wasm_globals (move_to_label st l) = wasm_globals st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma stack_move_label : forall st l,
    wasm_stack (move_to_label st l) = wasm_stack st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma memory_move_label : forall st l,
    wasm_memory (move_to_label st l) = wasm_memory st.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma stack_update_stack_incr_iid : forall st a,
    wasm_stack (update_stack (incr_iid st) a) = wasm_stack (update_stack st a).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma globals_update_stack_incr_iid : forall st a,
    wasm_globals (update_stack (incr_iid st) a) = wasm_globals (update_stack st a).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma memory_update_stack_incr_iid : forall st a,
    wasm_memory (update_stack (incr_iid st) a) = wasm_memory (update_stack st a).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma pc_update_stack_incr_iid : forall st a,
    wasm_pc (update_stack (incr_iid st) a) = wasm_pc (incr_iid st).
Admitted. (* Proof omitted for release, present in original source. *)

(*** The abstract stack/global map is unchanged if there are no writes to it. *)

Theorem globals_no_write : forall eid,
      eid > 0 ->
      MTable.mops_at eid MTableModel.LocationType_Global = 0 ->
      (globals_map (eid+1)) = (globals_map eid). 
Admitted. (* Proof omitted for release, present in original source. *)

Theorem stack_no_write : forall eid,
      eid > 0 ->
      MTable.mops_at eid MTableModel.LocationType_Stack = 0 ->
      (stk_map (eid+1)) = (stk_map eid). 
Admitted. (* Proof omitted for release, present in original source. *)

Theorem memory_no_write : forall eid,
      eid > 0 ->
      MTable.mops_at eid MTableModel.LocationType_Heap = 0 ->
      (heap_map (eid+1)) = (heap_map eid). 
Admitted. (* Proof omitted for release, present in original source. *)

Theorem alloc_memory_table_lookup_read_cell_with_value_correct: forall c eid location_type offset is_i32 enabled,
    alloc_memory_table_lookup_read_cell_with_value c eid location_type offset is_i32 enabled
    ->
      forall i,
        0 <= i ->
        let get c := etable_values c i in
           0 <= eid get < common  ->
           (location_type get = MTableModel.LocationType_Stack \/
            location_type get = MTableModel.LocationType_Heap \/
            location_type get = MTableModel.LocationType_Global) ->
           (is_i32 get = 0 \/ is_i32 get = 1) ->
           0 <= offset get < 2 * common +10  ->           
           enabled get = 1 ->
      MTable.memory_table_lookup_read_cell (eid get) (location_type get) (offset get) (is_i32 get) (etable_values (c AMTLRC_value_cell) i).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem alloc_memory_table_lookup_write_cell_correct: forall c eid location_type offset is_i32 value enabled,
    alloc_memory_table_lookup_write_cell c eid location_type offset is_i32 value enabled
    ->
      forall i,
        0 <= i ->
        let get c := etable_values c i in
           0 <= eid get < common ->
           (location_type get = MTableModel.LocationType_Stack \/
            location_type get = MTableModel.LocationType_Heap \/
            location_type get = MTableModel.LocationType_Global) ->
           (is_i32 get = 0 \/ is_i32 get = 1) ->
           0 <= offset get < 2 * common + 10 ->
           enabled get = 1 ->
      MTable.memory_table_lookup_write_cell (eid get) (location_type get) (offset get) (is_i32 get) (value get).
Admitted. (* Proof omitted for release, present in original source. *)

(**** Lemmas about reading/writing elements from the stack. *)

Require Import Lia.
Require Import MTable.

Theorem stack_rel_read_without_value : forall col i n is_i32 value enable v st stk,
    0 <= i ->
    (n < 10)%nat ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    state_rel i st ->
    wasm_stack st = stk ->
    List.nth_error stk n = Some v ->
  alloc_memory_table_lookup_read_cell
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1 + Z.of_nat n)
    is_i32
    value
    enable ->
    (value (fun c : etable_cols => etable_values c i)) = v.
Admitted. (* Proof omitted for release, present in original source. *)

(* the same as above, but with a more generous bound for n. *)
Theorem stack_rel_read_without_value_large : forall col i n offset is_i32 value enable v st stk,
    0 <= i ->
    Z.of_nat n < common ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    state_rel i st ->
    wasm_stack st = stk ->
    List.nth_error stk n = Some v ->
    offset (fun c : etable_cols => etable_values c i) = etable_values sp_cell i + 1 + Z.of_nat n ->
  alloc_memory_table_lookup_read_cell
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    offset
    is_i32
    value
    enable ->
    (value (fun c : etable_cols => etable_values c i)) = v.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem stack_rel_read : forall col i n is_i32 enable v st stk,
    0 <= i ->
    (n < 10)%nat ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->    
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    state_rel i st ->
    wasm_stack st = stk ->
    List.nth_error stk n = Some v ->
  alloc_memory_table_lookup_read_cell_with_value
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1 + Z.of_nat n)
    is_i32
    enable ->
   (etable_values (col AMTLRC_value_cell) i) = v.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem stack_rel_write_without_value : forall col i n is_i32 value enable eid sp stk1 v stk2,
    0 <= i ->
    eid > 0 ->
    mops_at eid MTableModel.LocationType_Stack = 1 ->    
    (n < 10)%nat ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->    
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    stack_rel (stk_map eid) (sp+1) (stk1++v::stk2) ->
    etable_values eid_cell i = eid ->
    etable_values sp_cell i  = sp ->
    List.length stk1 = n ->
  alloc_memory_table_lookup_write_cell
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1 + Z.of_nat n)
    is_i32
    value
    enable ->
  stack_rel (stk_map (eid+1)) (sp+1) (stk1++(value (fun c : etable_cols => etable_values c i))::stk2).
Admitted. (* Proof omitted for release, present in original source. *)

(* The same as above, but with a more generous bound for n *)
Theorem stack_rel_write_without_value_large : forall col i n offset is_i32 value enable eid stk1 v stk2,
    0 <= i ->
    eid > 0 ->
    mops_at eid MTableModel.LocationType_Stack = 1 ->
    Z.of_nat n < common + 10 ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->    
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    stack_rel (stk_map eid) (etable_values sp_cell i + 1) (stk1++v::stk2) ->
    etable_values eid_cell i = eid ->
    offset (fun c : etable_cols => etable_values c i) = (etable_values sp_cell i + 1 + Z.of_nat n) ->
    List.length stk1 = n ->
  alloc_memory_table_lookup_write_cell
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    offset
    is_i32
    value
    enable ->
  stack_rel (stk_map (eid+1)) (etable_values sp_cell i + 1) (stk1++(value (fun c : etable_cols => etable_values c i))::stk2).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem stack_rel_write : forall col i n is_i32 enable eid sp stk1 v stk2,
    0 <= i ->
    eid > 0 ->
    mops_at eid MTableModel.LocationType_Stack = 1 ->    
    (n < 10)%nat ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->    
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    stack_rel (stk_map eid) (sp+1) (stk1++v::stk2) ->
    etable_values eid_cell i = eid ->
    etable_values sp_cell i  = sp ->
    List.length stk1 = n ->
  alloc_memory_table_lookup_write_cell_with_value
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1 + Z.of_nat n)
    is_i32
    enable ->
  stack_rel (stk_map (eid+1)) (sp+1) (stk1++(etable_values (col AMTLWC_value_cell) i)::stk2).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem stack_rel_write_with_value_negative : forall col i is_i32 enable eid sp stk2,
    0 <= i ->
    eid > 0 ->
    mops_at eid MTableModel.LocationType_Stack = 1 ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    stack_rel (stk_map eid) (sp+1) (stk2) ->
    etable_values eid_cell i = eid ->
    etable_values sp_cell i  = sp ->
  alloc_memory_table_lookup_write_cell_with_value
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell)
    is_i32
    enable ->
  stack_rel (stk_map (eid+1)) (sp) ((etable_values (col AMTLWC_value_cell) i)::stk2).
Admitted. (* Proof omitted for release, present in original source. *)

Require Import FunctionalExtensionality.

(* Write to sp+0 and decrementing sp. *)
Theorem stack_rel_write_negative : forall col i is_i32 enable st value stk,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0 ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    state_rel i st ->
    wasm_stack st = (stk) ->
    (etable_values sp_cell (i+1))  = ((etable_values sp_cell i) - 1) ->
    (etable_values mpages_cell (i+1))  = (etable_values mpages_cell i)  ->
    (etable_values frame_id_cell (i+1)) = (etable_values frame_id_cell i) -> 
    (etable_values fid_cell (i+1)) = (etable_values fid_cell i) -> 
    wasm_pc (update_stack (incr_iid st) ((value (fun c => etable_values c i))::stk))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1)) ->
  alloc_memory_table_lookup_write_cell
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell)
    is_i32
    value
    enable ->
    state_rel (i+1) (update_stack (incr_iid st) ((value (fun c => etable_values c i))::stk)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Write to sp+1 without value *)
Theorem stack_rel_write_1_without_value : forall col i is_i32 value enable u st stk,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0 ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->    
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    state_rel i st ->    
    wasm_stack st = (u::stk) ->
    (etable_values sp_cell (i+1))  = (etable_values sp_cell i) ->
    (etable_values mpages_cell (i+1))  = (etable_values mpages_cell i)  ->
    (etable_values frame_id_cell (i+1)) = (etable_values frame_id_cell i) -> 
    (etable_values fid_cell (i+1)) = (etable_values fid_cell i) -> 
    wasm_pc (update_stack (incr_iid st) (value (fun c : etable_cols => etable_values c i) :: stk)) =
    (etable_values fid_cell (i + 1), etable_values iid_cell (i + 1)) ->
  alloc_memory_table_lookup_write_cell
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    is_i32
    value
    enable ->
  state_rel (i+1) (update_stack (incr_iid st) ((value (fun c : etable_cols => etable_values c i))::stk)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Write to sp+3 without value *)
Theorem stack_rel_write_3_without_value : forall col i is_i32 value enable u v w st stk,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0 ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->    
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    state_rel i st ->    
    wasm_stack st = (u::v::w::stk) ->
    (etable_values sp_cell (i+1))  = (etable_values sp_cell i) + 2 ->
    (etable_values mpages_cell (i+1))  = (etable_values mpages_cell i)  ->    
    (etable_values frame_id_cell (i+1)) = (etable_values frame_id_cell i) -> 
    (etable_values fid_cell (i+1)) = (etable_values fid_cell i) -> 
    wasm_pc (update_stack (incr_iid st) (value (fun c : etable_cols => etable_values c i) :: stk)) =
    (etable_values fid_cell (i + 1), etable_values iid_cell (i + 1)) ->
  alloc_memory_table_lookup_write_cell
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 3)
    is_i32
    value
    enable ->
  state_rel (i+1) (update_stack (incr_iid st) ((value (fun c : etable_cols => etable_values c i))::stk)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Write to sp+1 *)
Theorem stack_rel_write_1 : forall col i is_i32 enable u st stk,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0 ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->    
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    state_rel i st ->    
    wasm_stack st = (u::stk) ->
    (etable_values sp_cell (i+1))  = (etable_values sp_cell i) ->
    (etable_values mpages_cell (i+1))  = (etable_values mpages_cell i)  ->    
    (etable_values frame_id_cell (i+1)) = (etable_values frame_id_cell i) -> 
    (etable_values fid_cell (i+1)) = (etable_values fid_cell i) -> 
    wasm_pc (update_stack (incr_iid st) (etable_values (col AMTLWC_value_cell) i :: stk)) =
    (etable_values fid_cell (i + 1), etable_values iid_cell (i + 1)) ->
  alloc_memory_table_lookup_write_cell_with_value
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    is_i32
    enable ->
  state_rel (i+1) (update_stack (incr_iid st) ((etable_values (col AMTLWC_value_cell) i)::stk)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Write to sp+2 *)
Theorem stack_rel_write_2 : forall col i is_i32 enable u v st stk,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1 ->    
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0 ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->    
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    state_rel i st ->
    wasm_stack st = (u::v::stk) ->
    (etable_values sp_cell (i+1))  = (etable_values sp_cell i) + 1 ->
    (etable_values mpages_cell (i+1))  = (etable_values mpages_cell i)  ->    
    (etable_values frame_id_cell (i+1)) = (etable_values frame_id_cell i) -> 
    (etable_values fid_cell (i+1)) = (etable_values fid_cell i) -> 
    wasm_pc (update_stack (incr_iid st) (etable_values (col AMTLWC_value_cell) i :: stk)) =
    (etable_values fid_cell (i + 1), etable_values iid_cell (i + 1)) ->
  alloc_memory_table_lookup_write_cell_with_value
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    is_i32
    enable ->
  state_rel (i+1) (update_stack (incr_iid st) ((etable_values (col AMTLWC_value_cell) i)::stk)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem stack_rel_read_1_without_value : forall col i is_i32 value enable v st stk,
    0 <= i ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    state_rel i st ->
    wasm_stack st = (v::stk) ->
  alloc_memory_table_lookup_read_cell
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    is_i32
    value
    enable ->
    (value (fun c : etable_cols => etable_values c i)) = v.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem stack_rel_read_2_without_value : forall col i is_i32 value enable u v st stk,
    0 <= i ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    state_rel i st ->
    wasm_stack st = (u::v::stk) ->
  alloc_memory_table_lookup_read_cell
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    is_i32
    value
    enable ->
    (value (fun c : etable_cols => etable_values c i)) = v.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem stack_rel_read_1 : forall col i is_i32 enable v st stk,
    0 <= i ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->        
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    state_rel i st ->
    wasm_stack st = (v::stk) ->
  alloc_memory_table_lookup_read_cell_with_value
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 1)
    is_i32
    enable ->
  (etable_values (col AMTLRC_value_cell) i) = v.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem stack_rel_read_2 : forall col i is_i32 enable u v st stk,
    0 <= i ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->        
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    state_rel i st ->
    wasm_stack st = u::v::stk ->
  alloc_memory_table_lookup_read_cell_with_value
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell + 2)
    is_i32
    enable ->
  (etable_values (col AMTLRC_value_cell) i) = v.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem globals_rel_read : forall col i idx is_i32 value enable st,
    0 <= i ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->
    0 <= idx (fun c : etable_cols => etable_values c i) < common ->
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    state_rel i st ->
  alloc_memory_table_lookup_read_cell
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Global)
    idx
    is_i32
    value
    enable ->
  (exists v,
      glob_val (wasm_globals st) (Z.to_nat (idx (fun c => etable_values c i))) = Some v
      /\ value_rel (value (fun c => etable_values c i)) v).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem globals_rel_write : forall col i k is_i32 val enable eid x v gs,
    0 <= i ->
    eid > 0 ->
    mops_at eid MTableModel.LocationType_Global = 1 ->    
    enable (fun c : etable_cols => etable_values c i) = 1 ->
    etable_values op_global_set_idx_cell i = (Z.of_nat k) ->
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    val (fun c : etable_cols => etable_values c i) = x ->
    globals_rel (globals_map eid) gs ->
    value_rel x v ->
    etable_values eid_cell i = eid ->
  alloc_memory_table_lookup_write_cell
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Global)
    (fun get => get op_global_set_idx_cell)
    is_i32
    val
    enable ->
    Z.of_nat k <= domain MTableModel.LocationType_Global ->
    0 <= etable_values op_global_set_idx_cell i < common ->
  exists gs',
    (set_glob gs k v) = Some gs' /\ globals_rel (globals_map (eid+1)) gs'.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem write_cell_with_value_mops : forall col eid location_type offset is_i32 enable,
    alloc_memory_table_lookup_write_cell_with_value col eid location_type offset is_i32 enable ->
    forall i,
      0 <= i ->
      let get c := etable_values c i in
      0 <= eid get < common ->
      eid get > 0 ->
      (location_type get = MTableModel.LocationType_Stack \/
         location_type get = MTableModel.LocationType_Heap \/
         location_type get = MTableModel.LocationType_Global) ->
      (is_i32 get = 0 \/ is_i32 get = 1) ->
      0 <= offset get < 2 * common + 10 ->
      enable get = 1 ->
    mops_at (eid get) (location_type get) >= 1.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem write_cell_with_value_mops2 : forall col1 col2 eid location_type offset1 is_i32_1 enable1 offset2 is_i32_2 enable2,
    alloc_memory_table_lookup_write_cell_with_value col1 eid location_type offset1 is_i32_1 enable1 ->
    alloc_memory_table_lookup_write_cell_with_value col2 eid location_type offset2 is_i32_2 enable2 ->
    forall i,
      0 <= i ->
      let get c := etable_values c i in
      0 <= eid get < common ->
      eid get > 0 ->
      (location_type get = MTableModel.LocationType_Stack \/
         location_type get = MTableModel.LocationType_Heap \/
         location_type get = MTableModel.LocationType_Global) ->
      (is_i32_1 get = 0 \/ is_i32_1 get = 1) ->
      (is_i32_2 get = 0 \/ is_i32_2 get = 1) ->
      0 <= offset1 get < 2 * common + 10 ->
      0 <= offset2 get < 2 * common + 10 ->
      offset1 get <> offset2 get ->
      enable1 get = 1 ->
      enable2 get = 1 ->
    mops_at (eid get) (location_type get) >= 2.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem write_cell_mops : forall col eid location_type offset is_i32 value enable,
    alloc_memory_table_lookup_write_cell col eid location_type offset is_i32 value enable ->
    forall i,
      0 <= i ->
      let get c := etable_values c i in
      0 <= eid get < common ->
      eid get > 0 ->
      (location_type get = MTableModel.LocationType_Stack \/
         location_type get = MTableModel.LocationType_Heap \/
         location_type get = MTableModel.LocationType_Global) ->
      (is_i32 get = 0 \/ is_i32 get = 1) ->
      0 <= offset get < 2 * common + 10 ->
      enable get = 1 ->
    mops_at (eid get) (location_type get) >= 1.
Admitted. (* Proof omitted for release, present in original source. *)

Theorem stack_rel_drop : forall i n m eid sp stk1 stk2,
    0 <= i ->
    eid > 0 ->
    mops_at eid MTableModel.LocationType_Stack = 0 ->    
    stack_rel (stk_map eid) (sp+m+1) (stk1++stk2) ->
    etable_values eid_cell i = eid ->
    etable_values sp_cell i  = sp ->
    List.length stk1 = n ->
  stack_rel (stk_map (eid+1)) (sp + m + 1 + Z.of_nat n) (stk2).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem stack_rel_drop_1 : forall i u st stk,
    0 <= i ->
    (etable_values eid_cell i) > 0 ->
    (etable_values enabled_cell i) = 1 ->
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 0 -> 
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0 -> 
    mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0 ->
    state_rel i st ->
    wasm_stack st = (u::stk) ->
    (etable_values sp_cell (i+1))  = (etable_values sp_cell i) + 1 ->
    (etable_values mpages_cell (i+1))  = (etable_values mpages_cell i)  ->        
    (etable_values frame_id_cell (i+1)) = (etable_values frame_id_cell i) -> 
    (etable_values fid_cell (i+1)) = (etable_values fid_cell i) -> 
    wasm_pc (update_stack (incr_iid st) stk) =
    (etable_values fid_cell (i + 1), etable_values iid_cell (i + 1)) ->
    state_rel (i+1) (update_stack (incr_iid st) stk).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem stack_rel_write_without_value_large_drop : forall col i n m offset is_i32 value enable eid stk1 stk2,
    0 <= i ->
    eid > 0 ->
    mops_at eid MTableModel.LocationType_Stack = 1 ->
    0 <= m + Z.of_nat n < common + 10 ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->    
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    stack_rel (stk_map eid) (etable_values sp_cell i + m + 1) (stk1++stk2) ->
    etable_values eid_cell i = eid ->
    offset (fun c : etable_cols => etable_values c i) = (etable_values sp_cell i + m + Z.of_nat n) ->
    List.length stk1 = n ->
  alloc_memory_table_lookup_write_cell
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    offset
    is_i32
    value
    enable ->
  stack_rel (stk_map (eid+1)) (etable_values sp_cell i + m + Z.of_nat n) ((value (fun c : etable_cols => etable_values c i))::stk2).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem write_with_value_range : forall col i sp is_i32 enable loctyp,
    0 <= i ->
    0 <= sp (fun c : etable_cols => etable_values c i) < 2 * common + 10 ->
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
    is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->
    loctyp = MTableModel.LocationType_Stack \/
    loctyp = MTableModel.LocationType_Heap \/
    loctyp = MTableModel.LocationType_Global ->
    alloc_memory_table_lookup_write_cell_with_value
      col
      (fun get => get eid_cell)
      (fun get => loctyp)
      sp
      is_i32
      enable ->
    0 <= etable_values (col AMTLWC_value_cell) i < 
    2^(64 - (is_i32 (fun c : etable_cols => etable_values c i)) * 32).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem read_range : forall col i sp is_i32 value enable loctyp,
    0 <= i ->
    0 <= sp (fun c : etable_cols => etable_values c i) < 2 * common + 10 ->
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
    is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->
    loctyp = MTableModel.LocationType_Stack \/
    loctyp = MTableModel.LocationType_Heap \/
    loctyp = MTableModel.LocationType_Global ->
    alloc_memory_table_lookup_read_cell
      col
      (fun get => get eid_cell)
      (fun get => loctyp)
      sp
      is_i32
      value
      enable ->
    0 <= value (fun c : etable_cols => etable_values c i) < 
    2^(64 - (is_i32 (fun c : etable_cols => etable_values c i)) * 32).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem read_with_value_range : forall col i sp is_i32 enable loctyp,
    0 <= i ->
    0 <= sp (fun c : etable_cols => etable_values c i) < 2 * common + 10 ->
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
    is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    enable (fun c : etable_cols => etable_values c i) = 1 ->
    loctyp = MTableModel.LocationType_Stack \/
    loctyp = MTableModel.LocationType_Heap \/
    loctyp = MTableModel.LocationType_Global ->
    alloc_memory_table_lookup_read_cell_with_value
      col
      (fun get => get eid_cell)
      (fun get => loctyp)
      sp
      is_i32
      enable ->
    0 <= etable_values (col AMTLRC_value_cell) i < 
    2^(64 - (is_i32 (fun c : etable_cols => etable_values c i)) * 32).
Admitted. (* Proof omitted for release, present in original source. *)

