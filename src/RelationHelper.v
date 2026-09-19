(* Copyright (C) CertiK 2024-2026 *)

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
Proof. destruct st; reflexivity. Qed.

Lemma globals_update_callstack : forall st a,
    wasm_globals (update_callstack st a) = wasm_globals st.
Proof. destruct st; reflexivity. Qed.

Lemma stack_update_stack : forall st a,
    wasm_stack (update_stack st a) = a.
Proof. destruct st; reflexivity. Qed.

Lemma stack_update_callstack : forall st a,
    wasm_stack (update_callstack st a) = (wasm_stack st).
Proof. destruct st; reflexivity. Qed.

Lemma memory_update_stack : forall st a,
    wasm_memory (update_stack st a) = wasm_memory st.
Proof. destruct st; reflexivity. Qed.

Lemma memory_update_callstack : forall st a,
    wasm_memory (update_callstack st a) = wasm_memory st.
Proof. destruct st; reflexivity. Qed.

Lemma pc_update_stack : forall st a,
    wasm_pc (update_stack st a) = wasm_pc st.
Proof. destruct st; reflexivity. Qed.

Lemma pc_update_callstack : forall st a,
    wasm_pc (update_callstack st a) = wasm_pc st.
Proof. destruct st; reflexivity. Qed.

Lemma callstack_update_stack : forall st a,
    wasm_callstack (update_stack st a) = wasm_callstack st.
Proof. destruct st; reflexivity. Qed.

Lemma stack_update_globals : forall st a,
    wasm_stack (update_globals st a) = wasm_stack st.
Proof. destruct st; reflexivity. Qed.

Lemma globals_update_globals : forall st a,
    wasm_globals (update_globals st a) = a.
Proof. destruct st; reflexivity. Qed.

Lemma memory_update_globals : forall st a,
    wasm_memory (update_globals st a) = wasm_memory st.
Proof. destruct st; reflexivity. Qed.

Lemma pc_update_globals : forall st a,
    wasm_pc (update_globals st a) = wasm_pc st.
Proof. destruct st; reflexivity. Qed.

Lemma callstack_update_globals : forall st a,
    wasm_callstack (update_globals st a) = wasm_callstack st.
Proof. destruct st; reflexivity. Qed.

Lemma stack_update_memory : forall st a,
    wasm_stack (update_memory st a) = wasm_stack st.
Proof. destruct st; reflexivity. Qed.

Lemma globals_update_memory : forall st a,
    wasm_globals (update_memory st a) = wasm_globals st.
Proof. destruct st; reflexivity. Qed.

Lemma memory_update_memory : forall st a,
    wasm_memory (update_memory st a) = a.
Proof. destruct st; reflexivity. Qed.

Lemma pc_update_memory : forall st a,
    wasm_pc (update_memory st a) = wasm_pc st.
Proof. destruct st; reflexivity. Qed.

Lemma callstack_update_memory : forall st a,
    wasm_callstack (update_memory st a) = wasm_callstack st.
Proof. destruct st; reflexivity. Qed.

Lemma callstack_update_callstack : forall st a,
    wasm_callstack (update_callstack st a) = a.
Proof. destruct st; reflexivity. Qed.

Lemma pc_incr_iid : forall st,
    let (fid, iid) := wasm_pc st in
    wasm_pc (incr_iid st) = (fid, iid + 1).
Proof.
  destruct st.
  destruct wasm_pc; simpl; auto.
Qed.

Lemma globals_incr_iid : forall st,
    wasm_globals (incr_iid st) = wasm_globals st.
Proof.
  destruct st.
  destruct wasm_pc; simpl; auto.
Qed.

Lemma stack_incr_iid : forall st,
    wasm_stack (incr_iid st) = wasm_stack st.
Proof. 
  destruct st.
  destruct wasm_pc; simpl; auto.
Qed.

Lemma memory_incr_iid : forall st,
    wasm_memory (incr_iid st) = wasm_memory st.
Proof. 
  destruct st.
  destruct wasm_pc; simpl; auto.
Qed.

Lemma callstack_incr_iid : forall st,
    wasm_callstack (incr_iid st) = wasm_callstack st.
Proof. 
  destruct st.
  destruct wasm_pc; simpl; auto.
Qed.

Lemma incr_iid_update_stack : forall st a,
    wasm_pc (incr_iid (update_stack st a)) = wasm_pc (incr_iid st).
Proof.
  destruct st.
  destruct wasm_pc; simpl; reflexivity.
Qed.

Lemma move_iid_update_stack : forall st a niid,
    wasm_pc (move_to_iid (update_stack st a) niid) = wasm_pc (move_to_iid st niid).
Proof.
  destruct st.
  destruct wasm_pc; simpl; reflexivity.
Qed.

Lemma pc_move_iid : forall st niid,
    let (fid, iid) := wasm_pc st in
    wasm_pc (move_to_iid st niid) = (fid, niid).
Proof.
  destruct st.
  destruct wasm_pc; simpl; auto.
Qed.

Lemma globals_move_iid : forall st niid,
    wasm_globals (move_to_iid st niid) = wasm_globals st.
Proof.
  destruct st.
  destruct wasm_pc; simpl; auto.
Qed.

Lemma stack_move_iid : forall st niid,
    wasm_stack (move_to_iid st niid) = wasm_stack st.
Proof. 
  destruct st.
  destruct wasm_pc; simpl; auto.
Qed.

Lemma memory_move_iid : forall st niid,
    wasm_memory (move_to_iid st niid) = wasm_memory st.
Proof. 
  destruct st.
  destruct wasm_pc; simpl; auto.
Qed.

Lemma callstack_move_iid : forall st niid,
    wasm_callstack (move_to_iid st niid) = wasm_callstack st.
Proof. 
  destruct st.
  destruct wasm_pc; simpl; auto.
Qed.

Lemma pc_move_label : forall st l,
    wasm_pc (move_to_label st l) = l.
Proof.
  destruct st; simpl; auto.
Qed.

Lemma globals_move_label : forall st l,
    wasm_globals (move_to_label st l) = wasm_globals st.
Proof.
  destruct st; simpl; auto.
Qed.

Lemma stack_move_label : forall st l,
    wasm_stack (move_to_label st l) = wasm_stack st.
Proof. 
  destruct st; simpl; auto.
Qed.

Lemma memory_move_label : forall st l,
    wasm_memory (move_to_label st l) = wasm_memory st.
Proof. 
  destruct st; simpl; auto.
Qed.

Lemma callstack_move_label : forall st l,
    wasm_callstack (move_to_label st l) = wasm_callstack st.
Proof. 
  destruct st; simpl; auto.
Qed.

Lemma stack_update_stack_incr_iid : forall st a,
    wasm_stack (update_stack (incr_iid st) a) = wasm_stack (update_stack st a).
Proof. 
  destruct st. 
  destruct wasm_pc; simpl; auto.
Qed.

Lemma globals_update_stack_incr_iid : forall st a,
    wasm_globals (update_stack (incr_iid st) a) = wasm_globals (update_stack st a).
Proof. 
  destruct st. 
  destruct wasm_pc; simpl; auto.
Qed.

Lemma memory_update_stack_incr_iid : forall st a,
    wasm_memory (update_stack (incr_iid st) a) = wasm_memory (update_stack st a).
Proof. 
  destruct st. 
  destruct wasm_pc; simpl; auto.
Qed.

Lemma pc_update_stack_incr_iid : forall st a,
    wasm_pc (update_stack (incr_iid st) a) = wasm_pc (incr_iid st).
Proof. 
  destruct st. 
  destruct wasm_pc; simpl; auto.
Qed.

(*** The abstract stack/global map is unchanged if there are no writes to it. *)

Theorem globals_no_write : forall eid,
      eid > 0 ->
      MTable.mops_at eid MTableModel.LocationType_Global = 0 ->
      (globals_map (eid+1)) = (globals_map eid). 
Proof.
  intros eid mops.
  unfold globals_map.
  apply MTable.mtable_no_write; auto.
Qed.

Theorem stack_no_write : forall eid,
      eid > 0 ->
      MTable.mops_at eid MTableModel.LocationType_Stack = 0 ->
      (stk_map (eid+1)) = (stk_map eid). 
Proof.
  intros eid mops.
  unfold stk_map.
  apply MTable.mtable_no_write; auto.
Qed.

Theorem memory_no_write : forall eid,
      eid > 0 ->
      MTable.mops_at eid MTableModel.LocationType_Heap = 0 ->
      (heap_map (eid+1)) = (heap_map eid). 
Proof.
  intros eid mops.
  unfold heap_map.
  apply MTable.mtable_no_write; auto.
Qed.

Lemma alloc_memory_table_lookup_read_cell_correct: forall c eid location_type offset is_i32 value enabled,
    alloc_memory_table_lookup_read_cell c eid location_type offset is_i32 value enabled
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
      MTable.memory_table_lookup_read_cell (eid get) (location_type get) (offset get) (is_i32 get) (value get).
Proof.
  intros c eid location_type offset is_i32 value enabled AMTLRC i.
  simpl.
  intros Hrange read_eid_common read_location_type read_is_i32_bit read_offset_common Henabled.
  destruct AMTLRC.
  apply MTable.Build_memory_table_lookup_read_cell with
    (read_start_eid_cell :=  etable_values (c AMTLRC_start_eid_cell) i)
    (read_end_eid_cell   :=  etable_values (c AMTLRC_end_eid_cell) i)
    (read_start_eid_diff_cell :=  etable_values (c AMTLRC_start_eid_diff_cell) i)
    (read_end_eid_diff_cell   :=  etable_values (c AMTLRC_end_eid_diff_cell) i)
    (read_value_cell     :=  etable_values (c AMTLRC_value_cell) i)
    (read_encode_cell    :=  etable_values (c AMTLRC_encode_cell) i); simpl in *;
    specialize (read_gate i ltac:(lia));
    auto; try lia.
Qed.  

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
Proof.
  intros c eid location_type offset is_i32 enabled AMTLRC i.
  simpl.
  intros Hrange read_eid_common read_location_type read_is_i32_bit read_offset_common Henabled.
  destruct AMTLRC.
  apply MTable.Build_memory_table_lookup_read_cell with
    (read_start_eid_cell :=  etable_values (c AMTLRC_start_eid_cell) i)
    (read_end_eid_cell   :=  etable_values (c AMTLRC_end_eid_cell) i)
    (read_start_eid_diff_cell :=  etable_values (c AMTLRC_start_eid_diff_cell) i)
    (read_end_eid_diff_cell   :=  etable_values (c AMTLRC_end_eid_diff_cell) i)
    (read_value_cell     :=  etable_values (c AMTLRC_value_cell) i)
    (read_encode_cell    :=  etable_values (c AMTLRC_encode_cell) i); simpl in *;
    specialize (readv_gate i ltac:(lia));
    auto; lia.
Qed.

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
Proof.
  intros c eid location_type offset is_i32 value enabled AMTLWC i.
  simpl.
  intros Hrange read_eid_common read_location_type read_is_i32_bit read_offset_common Henabled.
  destruct AMTLWC.
  apply MTable.Build_memory_table_lookup_write_cell with
    (write_start_eid_cell      :=  etable_values (c AMTLWC_start_eid_cell) i)
    (write_end_eid_cell        :=  etable_values (c AMTLWC_end_eid_cell) i)
    (write_value_cell          :=  etable_values (c AMTLWC_value_cell) i)
    (write_encode_cell         :=  etable_values (c AMTLWC_encode_cell) i); simpl in *;
    specialize (write_gate i ltac:(lia));
    auto; lia.
Qed.

Lemma alloc_memory_table_lookup_write_cell_with_value_correct: forall c eid location_type offset is_i32 enabled,
    alloc_memory_table_lookup_write_cell_with_value c eid location_type offset is_i32 enabled
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
      MTable.memory_table_lookup_write_cell (eid get) (location_type get) (offset get) (is_i32 get) (etable_values (c AMTLWC_value_cell) i).
Proof.
  intros c eid location_type offset is_i32 enabled AMTLWC i.
  simpl.
  intros Hrange read_eid_common read_location_type read_is_i32_bit read_offset_common Henabled.
  destruct AMTLWC.
  apply MTable.Build_memory_table_lookup_write_cell with
    (write_start_eid_cell      :=  etable_values (c AMTLWC_start_eid_cell) i)
    (write_end_eid_cell        :=  etable_values (c AMTLWC_end_eid_cell) i)
    (write_value_cell          :=  etable_values (c AMTLWC_value_cell) i)
    (write_encode_cell         :=  etable_values (c AMTLWC_encode_cell) i); simpl in *;
    specialize (writev_gate i ltac:(lia));
    auto; lia.
Qed.

(**** Lemmas about reading/writing elements from the stack. *)

Require Import Lia.
Require Import MTable.

Lemma stack_rel_read' : forall n stk m sp v,
   stack_rel m sp stk ->
   nth_error stk n = Some v -> 
   get m (sp + Z.of_nat n) = Some v.
Proof.
  induction n; intros.
  - destruct stk; simpl in *.
    + congruence.
    + replace (sp+0) with sp by lia.
      destruct H. congruence.
  - destruct stk; simpl in *.
    + congruence.
    + destruct H as [_ H].
      replace (sp + Z.pos (Pos.of_succ_nat n)) with ((sp+1) + Z.of_nat n) by lia.
      eapply IHn; eauto.
Qed.

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
Proof.
  intros col i n is_i32 value enabled v st stk Hrange Hrangen Henable Hisbit Hrel Hstk Hnth Hread.
  simpl in Hread.
  apply alloc_memory_table_lookup_read_cell_correct 
    with (i := i)
    in Hread; auto; try lia.
   apply  mtable_read  with (init:=empty) in Hread.
    destruct Hrel.
    rewrite Hstk in *; clear Hstk.
    simpl in state_stack_rel.
    change  (gather_entries (etable_values eid_cell i) MTableModel.LocationType_Stack 0
                 MTableModel.mtable_numRow empty)
      with (stk_map (etable_values eid_cell i)) in Hread.
    remember (etable_values sp_cell i + 1) as sp.
    rewrite (stack_rel_read' n stk _ _ v) in Hread; auto.
    + congruence.
  - pose (eid_common i); lia.
  - pose (sp_common i); lia.
Qed.

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
Proof.
  intros col i n offset is_i32 value enabled v st stk Hrange Hrangen Henable Hisbit Hrel Hstk Hnth Hoffset Hread.
  simpl in Hread.
  apply alloc_memory_table_lookup_read_cell_correct 
    with (i := i)
    in Hread; auto; try lia.
   apply  mtable_read  with (init:=empty) in Hread.
    destruct Hrel.
    rewrite Hstk in *; clear Hstk.
    simpl in state_stack_rel.
    change  (gather_entries (etable_values eid_cell i) MTableModel.LocationType_Stack 0
                 MTableModel.mtable_numRow empty)
      with (stk_map (etable_values eid_cell i)) in Hread.
    rewrite Hoffset in Hread.
    remember (etable_values sp_cell i + 1) as sp.
    rewrite (stack_rel_read' n stk _ _ v) in Hread; auto.
    + congruence.
  - pose (eid_common i); lia.
  - pose (sp_common i); lia.
Qed.

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
Proof.
  intros col i n is_i32 enabled v st stk Hrange Hrangen Henable Hisbit Hrel Hstk Hnth Hread.
  simpl in Hread.
  apply alloc_memory_table_lookup_read_cell_with_value_correct 
    with (i := i)
    in Hread; auto; try lia.
  { apply  mtable_read  with (init:=empty) in Hread.
    destruct Hrel.
    rewrite Hstk in *; clear Hstk.
    simpl in state_stack_rel.
    change  (gather_entries (etable_values eid_cell i) MTableModel.LocationType_Stack 0
                 MTableModel.mtable_numRow empty)
      with (stk_map (etable_values eid_cell i)) in Hread.
    remember (etable_values sp_cell i + 1) as sp.
    rewrite (stack_rel_read' n stk _ _ v) in Hread; auto.
    + congruence. }      
  - pose (eid_common i); lia.
  - pose (sp_common i); lia.
Qed.

Lemma set_preserve_stack_rel : forall stk m k u sp,
    stack_rel m sp stk ->
    k < sp ->
    stack_rel (set m k u) sp stk.
Proof.
  induction stk; simpl; intros; auto.
  destruct H as [H1 H2].
  split.
  - rewrite gso by lia; auto.
    apply IHstk; auto; lia.
Qed.
  
Lemma stack_rel_write' : forall stk1 v stk2 u m n sp,
    stack_rel m sp (stk1 ++ v::stk2)  ->
    List.length stk1 = n ->
    stack_rel (set m (sp + Z.of_nat n) u) sp (stk1 ++ u::stk2).
Proof.
  induction stk1; simpl in *; subst; intros.
  - destruct H as [H1 H2].
    split.
    + replace (sp+Z.of_nat n) with sp by lia.
      rewrite gss. reflexivity.
    + apply set_preserve_stack_rel; auto; lia.
  - destruct H as [H1 H2].
    split.
    + rewrite gso; auto; lia.
    + destruct n as [|n']; try congruence.
      replace (sp + Z.of_nat (S n')) with (sp + 1 + Z.of_nat n') by lia.
      eapply IHstk1; eauto.
Qed.

Lemma stack_rel_write_negative' : forall m stk u sp,
    stack_rel m (sp+1) stk  ->
    stack_rel (set m sp u) sp (u::stk).
Proof.
  intros.
  simpl.
  split.
  - rewrite gss; reflexivity.
  - apply set_preserve_stack_rel; auto; lia.
Qed.

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
Proof.
  intros col i n is_i32 value enable eid sp stk1 v stk2.
  intros Hrange Heid_nonzero Hmops Hnrange Henable His32_bit Hrel Heid Hsp Hn Hwrite.
  apply alloc_memory_table_lookup_write_cell_correct 
    with (i := i)
    in Hwrite; auto; try lia.
  { apply mtable_write with (init:=empty) in Hwrite.
    - rewrite Heid in *.
      change (gather_entries (eid + 1) MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
        with (stk_map (eid+1)) in Hwrite.
      change (gather_entries eid MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
        with (stk_map eid) in Hwrite.
      rewrite Hwrite.
      rewrite Hsp in *.
      remember (value (fun c : etable_cols => etable_values c i)) as u.
      eapply stack_rel_write' with (sp:=sp+1); eauto.
    - rewrite Heid; lia.
    - rewrite Heid; lia.
  }
  - pose (eid_common i); lia.
  - pose (sp_common i); lia.
Qed. 

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
Proof.
  intros col i n offset is_i32 value enable eid stk1 v stk2.
  intros Hrange Heid_nonzero Hmops Hnrange Henable His32_bit Hrel Heid Hoffset Hn Hwrite.
  apply alloc_memory_table_lookup_write_cell_correct 
    with (i := i)
    in Hwrite; auto; try lia.
  { apply mtable_write with (init:=empty) in Hwrite.
    - rewrite Heid in *.
      change (gather_entries (eid + 1) MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
        with (stk_map (eid+1)) in Hwrite.
      change (gather_entries eid MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
        with (stk_map eid) in Hwrite.
      rewrite Hwrite.
      rewrite Hoffset in *.
      remember (value (fun c : etable_cols => etable_values c i)) as u.
      eapply stack_rel_write' with (sp:=etable_values sp_cell i +1); eauto.
    - rewrite Heid; lia.
    - rewrite Heid; lia.
  }
  - pose (eid_common i); lia.
  - pose (sp_common i); lia.
Qed.

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
Proof.
  intros col i n is_i32 enable eid sp stk1 v stk2.
  intros Hrange Heid_nonzero Hmops Hnrange Henable His32_bit Hrel Heid Hsp Hn Hwrite.
  apply alloc_memory_table_lookup_write_cell_with_value_correct 
    with (i := i)
    in Hwrite; auto; try lia.
  { apply mtable_write with (init:=empty) in Hwrite.
    - rewrite Heid in *.
      change (gather_entries (eid + 1) MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
        with (stk_map (eid+1)) in Hwrite.
      change (gather_entries eid MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
        with (stk_map eid) in Hwrite.
      rewrite Hwrite.
      rewrite Hsp in *.
      remember (etable_values (col AMTLWC_value_cell) i) as u.
      eapply stack_rel_write' with (sp:=sp+1); eauto.
    - rewrite Heid; lia.
    - rewrite Heid; lia.
  }
  - pose (eid_common i); lia.
  - pose (sp_common i); lia.
Qed.

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
Proof.
  intros col i is_i32 enable eid sp stk2.
  intros Hrange Heid_nonzero Hmops Henable His32_bit Hrel Heid Hsp Hwrite.
  apply alloc_memory_table_lookup_write_cell_with_value_correct 
    with (i := i)
    in Hwrite; auto; try lia.
  { apply mtable_write with (init:=empty) in Hwrite.
    - rewrite Heid in *.
      change (gather_entries (eid + 1) MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
        with (stk_map (eid+1)) in Hwrite.
      change (gather_entries eid MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
        with (stk_map eid) in Hwrite.
      rewrite Hwrite.
      rewrite Hsp in *.
      remember (etable_values (col AMTLWC_value_cell) i) as u.
      eapply stack_rel_write_negative'; eauto.
    - rewrite Heid; lia.
    - rewrite Heid; lia.
  }
  - pose (eid_common i); lia.
  - pose (sp_common i); lia.
Qed.

Lemma stack_rel_write_negative'' : forall col i is_i32 enable eid sp value stk2,
    0 <= i ->
    eid > 0 ->
    mops_at eid MTableModel.LocationType_Stack = 1 ->    
    enable (fun c : etable_cols => etable_values c i) = 1 ->    
    (is_i32 (fun c : etable_cols => etable_values c i) = 0 \/
       is_i32 (fun c : etable_cols => etable_values c i) = 1) ->
    stack_rel (stk_map eid) (sp+1) (stk2) ->
    etable_values eid_cell i = eid ->
    etable_values sp_cell i  = sp ->
  alloc_memory_table_lookup_write_cell
    col
    (fun get => get eid_cell)
    (fun get => MTableModel.LocationType_Stack)
    (fun get => get sp_cell)
    is_i32
    value
    enable ->
  stack_rel (stk_map (eid+1)) (sp) ((value (fun c => etable_values c i))::stk2).
Proof.
  intros col i is_i32 enable eid sp value stk2.
  intros Hrange Heid_nonzero Hmops Henable His32_bit Hrel Heid Hsp Hwrite.
  apply alloc_memory_table_lookup_write_cell_correct 
    with (i := i)
    in Hwrite; auto; try lia.
  { apply mtable_write with (init:=empty) in Hwrite.
    - rewrite Heid in *.
      change (gather_entries (eid + 1) MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
        with (stk_map (eid+1)) in Hwrite.
      change (gather_entries eid MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
        with (stk_map eid) in Hwrite.
      rewrite Hwrite.
      rewrite Hsp in *.
      remember (etable_values (col AMTLWC_value_cell) i) as u.
      eapply stack_rel_write_negative'; eauto.
    - rewrite Heid; lia.
    - rewrite Heid; lia.
  }
  - pose (eid_common i); lia.
  - pose (sp_common i); lia.
Qed.

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
Proof.
  intros col i is_i32 enable st value stk.
  intros Hrange Heid_nonzero Hrow_enabled Hmops Hmops' Hmops'' Henable His32_bit Hrel Hstk Hsp Hmpages  Hframe Hfid Hpc Hwrite.
  destruct Hrel.
  rewrite Hstk in *; clear Hstk.
  assert (Hrel' := stack_rel_write_negative'' _ i is_i32 enable _ _  value stk Hrange Heid_nonzero Hmops Henable His32_bit state_stack_rel eq_refl eq_refl Hwrite).
  constructor.
  - assumption.
  - simpl.
    rewrite stack_update_stack.
    rewrite Hsp.
    replace (etable_values sp_cell i - 1 + 1) with  (etable_values sp_cell i) by lia.
    rewrite eid_change by (auto;lia).
    apply Hrel'.
  - rewrite eid_change by (auto;lia).
    rewrite globals_update_stack_incr_iid.
    rewrite globals_no_write; auto.
    rewrite globals_update_stack; auto.
  - rewrite eid_change by (auto;lia).
    rewrite memory_update_stack_incr_iid.
    rewrite Hmpages.
    rewrite memory_no_write; auto.
    rewrite memory_update_stack; auto.
  - rewrite maximal_memory_pages_change; auto.
  - rewrite Hframe, Hfid, callstack_update_stack, callstack_incr_iid; auto.
Qed.

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
Proof.
  intros col i is_i32 value enable u st stk.
  intros Hrange Heid_nonzero Hrow_enabled Hmops Hmops' Hmops'' Henable His32_bit Hrel Hstk Hsp Hmpages Hframe_id Hfid Hpc Hwrite.
  destruct Hrel.
  rewrite Hstk in *; clear Hstk.
  replace (fun get => get sp_cell + 1)
    with (fun get => get sp_cell + 1 + 0) in Hwrite
      by (extensionality get; lia).
  assert (Hrel' := stack_rel_write_without_value _ _ (0%nat) is_i32 value enable _ _ (nil) u stk Hrange Heid_nonzero Hmops ltac:(lia) Henable His32_bit state_stack_rel eq_refl eq_refl eq_refl Hwrite).
  constructor.
  - assumption.
  - simpl in *.
    rewrite stack_update_stack_incr_iid.
    rewrite Hsp.
    rewrite eid_change by (auto;lia).
    destruct Hrel' as [Hrel1 Hrel2].
    destruct st. simpl.
    split; auto.
  - rewrite eid_change by (auto;lia).
    rewrite globals_update_stack_incr_iid.
    rewrite globals_no_write; auto.
    rewrite globals_update_stack; auto.
  - rewrite eid_change by (auto;lia).
    rewrite memory_update_stack_incr_iid.
    rewrite Hmpages.
    rewrite memory_no_write; auto.
    rewrite memory_update_stack; auto.
    rewrite maximal_memory_pages_change; auto.
  - rewrite Hframe_id, Hfid, callstack_update_stack, callstack_incr_iid; auto.
Qed.

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
Proof.
  intros col i is_i32 value enable u v w st stk.
  intros Hrange Heid_nonzero Hrow_enabled Hmops Hmops' Hmops'' Henable His32_bit Hrel Hstk Hsp Hmpages Hframe_id Hfid Hpc Hwrite.
  destruct Hrel.
  rewrite Hstk in *; clear Hstk.
  change (u :: v :: w :: stk) with (u::v::nil ++ w:: stk) in state_stack_rel.
  replace (fun get => get sp_cell + 3)
    with (fun get => get sp_cell + 1 + 2) in Hwrite
      by (extensionality get; lia).
  assert (Hrel' := stack_rel_write_without_value _ _ (2%nat) is_i32 value enable _ _ (u::v::nil) w stk Hrange Heid_nonzero Hmops ltac:(lia) Henable His32_bit state_stack_rel eq_refl eq_refl eq_refl Hwrite).
  constructor.
  - assumption.
  - simpl in *.
    rewrite stack_update_stack_incr_iid.
    rewrite Hsp.
    rewrite eid_change by (auto;lia).
    destruct Hrel' as [Hrel1 [Hrel2 [Hrel3 Hrel4]]].
    destruct st. simpl.
    replace(etable_values sp_cell i + 2 + 1) with (etable_values sp_cell i + 1 + 1 + 1) by lia.
    split; auto.
  - rewrite eid_change by (auto;lia).
    rewrite globals_update_stack_incr_iid.
    rewrite globals_no_write; auto.
    rewrite globals_update_stack; auto.
  - rewrite eid_change by (auto;lia).
    rewrite memory_update_stack_incr_iid.
    rewrite Hmpages.
    rewrite memory_no_write; auto.
    rewrite memory_update_stack; auto.
    rewrite maximal_memory_pages_change; auto.    
  - rewrite Hframe_id, Hfid, callstack_update_stack, callstack_incr_iid; auto.
Qed.

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
Proof.
  intros col i is_i32 enable u st stk.
  intros Hrange Heid_nonzero Hrow_enabled Hmops Hmops' Hmops'' Henable His32_bit Hrel Hstk Hsp Hmpages Hframe_id Hfid Hpc Hwrite.
  destruct Hrel.
  rewrite Hstk in *; clear Hstk.
  replace (fun get => get sp_cell + 1)
    with (fun get => get sp_cell + 1 + 0) in Hwrite
      by (extensionality get; lia).
  assert (Hrel' := stack_rel_write _ _ (0%nat) is_i32 enable _ _ (nil) u stk Hrange Heid_nonzero Hmops ltac:(lia) Henable His32_bit state_stack_rel eq_refl eq_refl eq_refl Hwrite).
  constructor.
  - assumption.
  - simpl in *.
    rewrite stack_update_stack_incr_iid.
    rewrite Hsp.
    rewrite eid_change by (auto;lia).
    destruct Hrel' as [Hrel1 Hrel2].
    destruct st. simpl.
    split; auto.
  - rewrite eid_change by (auto;lia).
    rewrite globals_update_stack_incr_iid.
    rewrite globals_no_write; auto.
    rewrite globals_update_stack; auto.
  - rewrite eid_change by (auto;lia).
    rewrite memory_update_stack_incr_iid.
    rewrite Hmpages.
    rewrite memory_no_write; auto.
    rewrite memory_update_stack; auto.
    rewrite maximal_memory_pages_change; auto.    
  - rewrite Hframe_id, Hfid, callstack_update_stack, callstack_incr_iid; auto.
Qed.

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
Proof.
  intros col i is_i32 enable u v st stk.
  intros Hrange Heid_nonzero Hrow_enabled Hmops Hmops' Hmops'' Henable His32_bit Hrel Hstk Hsp Hmpages Hframe_id Hfid Hpc Hwrite.
  destruct Hrel.
  rewrite Hstk in *; clear Hstk.
  change (u :: v :: stk) with (u::nil ++ v::stk) in state_stack_rel.
  replace (fun get => get sp_cell + 2)
    with (fun get => get sp_cell + 1 + 1) in Hwrite
      by (extensionality get; lia).
  assert (Hrel' := stack_rel_write _ _ (1%nat) is_i32 enable _ _ (u::nil) v stk Hrange Heid_nonzero Hmops ltac:(lia) Henable His32_bit state_stack_rel eq_refl eq_refl eq_refl Hwrite).
  constructor.
  - assumption.
  - simpl in *.
    rewrite stack_update_stack_incr_iid.
    rewrite Hsp.
    rewrite eid_change by (auto;lia).
    destruct Hrel' as [Hrel1 [Hrel2 Hrel3]].
    destruct st. simpl.
    split; auto.
  - rewrite eid_change by (auto;lia).
    rewrite globals_update_stack_incr_iid.
    rewrite globals_no_write; auto.
    rewrite globals_update_stack; auto.    
  - rewrite eid_change by (auto;lia).
    rewrite memory_update_stack_incr_iid.
    rewrite Hmpages.
    rewrite memory_no_write; auto.
    rewrite memory_update_stack; auto.    
    rewrite maximal_memory_pages_change; auto.    
  - rewrite Hframe_id, Hfid, callstack_update_stack, callstack_incr_iid; auto.
Qed.

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
Proof.
  intros.
  apply stack_rel_read_without_value with (col:=col) (v:=v) (n:=0%nat ) (st:=st) (stk:=v::stk) (is_i32:=is_i32) (value:=value) (enable:=enable); auto.
  - lia.
  - replace (fun get : etable_cols -> Z => get sp_cell + 1 + Z.of_nat 0)
      with  (fun get : etable_cols -> Z => get sp_cell + 1).
    auto.
    extensionality get. lia.
Qed.

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
Proof.
  intros.
  apply stack_rel_read_without_value with (col:=col) (v:=v) (n:=1%nat ) (st:=st) (stk:=u::v::stk) (is_i32:=is_i32) (value:=value) (enable:=enable); auto.
  - lia.
  - replace (fun get : etable_cols -> Z => get sp_cell + 1 + Z.of_nat 1)
      with  (fun get : etable_cols -> Z => get sp_cell + 2).
    auto.
    extensionality get. lia.
Qed.

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
Proof.
  intros.
  apply stack_rel_read with (v:=v) (n:=0%nat ) (st:=st) (stk:=v::stk) (is_i32:=is_i32) (enable:=enable); auto.
  - lia.
  - replace (fun get : etable_cols -> Z => get sp_cell + 1 + Z.of_nat 0)
      with  (fun get : etable_cols -> Z => get sp_cell + 1).
    auto.
    extensionality get. lia.
Qed.

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
Proof.
  intros.
  apply stack_rel_read with (v:=v) (n:=1%nat ) (st:=st) (stk:=u::v::stk) (is_i32:=is_i32) (enable:=enable); auto.
  - lia.
  - replace (fun get : etable_cols -> Z => get sp_cell + 1 + Z.of_nat 1)
      with  (fun get : etable_cols -> Z => get sp_cell + 2).
    auto.
    extensionality get. lia.
Qed.

Lemma globals_rel_read' : forall idx z m gs,
    globals_rel m gs ->
    get m (Z.of_nat idx) = Some z ->
    exists v, glob_val gs idx = Some v /\ value_rel z v.
Proof.
  destruct 1.
  firstorder.
Qed.

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
Proof.
  intros  col i idx is_i32 value enable st.
  intros  Hrange Henable Hidx_common Hisbit Hrel Hread.
  simpl in Hread.
  apply alloc_memory_table_lookup_read_cell_correct 
    with (i := i)
    in Hread; auto; try lia.
  { apply  mtable_read  with (init:=empty) in Hread.
    destruct Hrel.
    destruct state_globals_rel.
    change  (gather_entries (etable_values eid_cell i) MTableModel.LocationType_Global 0
                 MTableModel.mtable_numRow empty)
      with (globals_map (etable_values eid_cell i)) in Hread.
    specialize (globals_rel_lookup (Z.to_nat (idx (fun c : etable_cols => etable_values c i)))).
    rewrite Z2Nat.id in globals_rel_lookup by lia.
    apply (globals_rel_lookup _ Hread).  }      
  - pose (eid_common i); lia.
Qed.

Lemma set_nth_other : forall A (gs : seq.seq A) v i k,
    i <> k ->
    (k < List.length gs) %nat ->
    nth_error gs i = nth_error (seq.set_nth v gs k v) i.
Proof.
  induction gs; simpl.
  - intros; lia.
  - simpl in *.
    intros v i k Hneq Hlt.
    destruct k as [|k'].
    + simpl.
      destruct i as [|i]; [congruence|].
      reflexivity.
    + simpl.
      destruct i.
      * reflexivity.
      * simpl.
        apply IHgs; lia.
Qed.

Lemma set_nth_same : forall A (gs : seq.seq A) v k,
    (k < List.length gs) %nat ->
    nth_error (seq.set_nth v gs k v) k = Some v.
Proof.
  induction gs.
  - simpl; intros; lia.
  - simpl; intros.
    destruct k.
    + reflexivity.
    + simpl.
      apply IHgs; lia.
Qed.

Lemma set_nth_length : forall A (gs : seq.seq A) v k,
    (k < length gs) %nat ->
    length (seq.set_nth v gs k v) = length gs.
Proof.
  induction gs.
  - simpl; intros; lia.
  - simpl; intros.
    destruct k.
    + reflexivity.
    + simpl.
      f_equal.
      apply IHgs; lia.
Qed.

Lemma get_set_glob_other : forall gs gs' v i k,
    i <> k ->
    set_glob gs k v = Some gs' ->
    glob_val gs i = glob_val gs' i.
Proof.
  unfold set_glob, glob_val.
  intros.
  destruct (nth_error gs k) eqn:Hnth.
  - simpl in *.
    assert (k < length gs)%nat.
    {
      destruct (le_lt_dec (length gs) k) as [l|l].
      - rewrite <- nth_error_None in l.
        congruence.
      - assumption.
    }
    inversion H0.
    rewrite (set_nth_other _ _  {| datatypes.g_mut := datatypes.g_mut g; datatypes.g_val := v |} _ _ H H1).
    congruence.
  - simpl in *; congruence.
Qed.

Lemma get_set_glob_same : forall gs gs' v k,
    set_glob gs k v = Some gs' ->
    glob_val gs' k = Some v.
Proof.
  unfold set_glob, glob_val.
  intros.
  destruct (nth_error gs k) eqn:Hnth.
  - simpl in *.
    assert (k < length gs)%nat.
    {
      destruct (le_lt_dec (length gs) k) as [l|l].
      - rewrite <- nth_error_None in l.
        congruence.
      - assumption.
    }
    inversion H.
    rewrite (set_nth_same _ _ _ _ H0).
    reflexivity.
  - simpl in *; congruence.
Qed.

Lemma set_glob_defined : forall gs v k,
  (k < List.length gs) %nat ->
  exists gs',
    (set_glob gs k v) = Some gs' /\ length gs' = length gs.
Proof.
  intros gs v k Hlt.
  unfold set_glob.
  destruct (nth_error gs k) eqn:Hnth.
  - eexists.
    split.
    + reflexivity.
    + apply set_nth_length. auto.
  - rewrite nth_error_None in Hnth.
    lia.
Qed.

Lemma globals_rel_write'' : forall x v m gs k,
  globals_rel m gs ->
  value_rel x v ->
  (k < List.length gs)%nat ->
  exists gs',
    (set_glob gs k v) = Some gs' /\ globals_rel (set m (Z.of_nat k) x) gs'.
Proof.
  intros x v m gs k Hrel Hvalue_rel Hlen.
  destruct (set_glob_defined gs v k Hlen) as [gs' [Hgs' Hlen']].
  exists gs'. split; [assumption|].
  destruct Hrel as [rel_domain rel_lookup].
  constructor.
  - rewrite Hlen'. apply rel_domain.
  - intros j z Hget.
    destruct (Nat.eq_dec j  k) as [Heq| Hneq].
    + subst; simpl in *.
      rewrite gss in Hget. inversion Hget. subst.
      exists v; split; auto.
      apply get_set_glob_same with gs. auto.
    + replace (glob_val gs' j) with (glob_val gs j)
        by (apply get_set_glob_other with (v:=v) (k:=k); auto).
      apply rel_lookup.
      rewrite gso in Hget by lia.
      apply Hget.
Qed.

Lemma globals_rel_write' : forall m gs x v k,
  globals_rel m gs ->
  value_rel x v ->
  (Z.of_nat k <= MTable.domain MTableModel.LocationType_Global) ->
  exists gs',
    (set_glob gs k v) = Some gs' /\ globals_rel (set m (Z.of_nat k) x) gs'.
Proof.
  intros m gs x v k Hrel Hvalue_rel Hlen.
  apply globals_rel_write''; auto.
  destruct Hrel as [rel_domain rel_lookup].
  lia.
Qed.

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
Proof.         
  intros col i k is_i32 val enable eid x v gs.
  intros Hrange Heid_nonzero Hmops Henable Hidx His32_bit Hval Hrel Hvalue_rel Heid Hwrite Hdomain Hidxcommon.
  apply alloc_memory_table_lookup_write_cell_correct 
    with (i := i)
         (offset := (fun get => get op_global_set_idx_cell))
    in Hwrite; auto; try lia.
  { apply mtable_write with (init:=empty) in Hwrite.
    - rewrite Heid in *.
      change (gather_entries (eid + 1) MTableModel.LocationType_Global 0 MTableModel.mtable_numRow empty)
        with (globals_map (eid+1)) in Hwrite.
      change (gather_entries eid MTableModel.LocationType_Global 0 MTableModel.mtable_numRow empty)
        with (globals_map eid) in Hwrite.
      rewrite Hwrite.
      rewrite Hidx, Hval.
      apply globals_rel_write'; auto.
    - rewrite Heid; lia.
    - rewrite Heid; lia.
  }
  - pose (eid_common i); lia.
Qed.

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
Proof.
  intros col eid location_type offset is_i32 enable Hwrite i.
  simpl.
  intros Hrange Heid Heid_nonzero Hlocation_type His_i32 Hoffset_common Henable.
  apply alloc_memory_table_lookup_write_cell_with_value_correct
    with (i:=i)
    in Hwrite; auto.
  refine (mtable_write_mops _ _ _ _ _ _ Hwrite).
  auto.
Qed.

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
Proof.
  intros col1 col2 eid location_type offset1 is_i32_1 enable1 offset2 is_i32_2 enable2 Hwrite1 Hwrite2 i.
  simpl.
  intros Hrange Heid Heid_nonzero Hlocation_type His_i32_1 His_i32_2 Hoffset_common1 Hoffset_common2 Hoffset_diff Henable1 Henable2.
  apply alloc_memory_table_lookup_write_cell_with_value_correct
    with (i:=i)
    in Hwrite1; auto.
  apply alloc_memory_table_lookup_write_cell_with_value_correct
    with (i:=i)
    in Hwrite2; auto.
  refine (mtable_write_mops2 _ _ _ _ _ _ _ _ _ Hwrite1 Hwrite2 Hoffset_diff).
  auto.
Qed.

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
Proof.
  intros col eid location_type offset is_i32 value enable Hwrite i.
  simpl.
  intros Hrange Heid Heid_nonzero Hlocation_type His_i32 Hoffset_common Henable.
  apply alloc_memory_table_lookup_write_cell_correct
    with (i:=i)
    in Hwrite; auto.
  refine (mtable_write_mops _ _ _ _ _ _ Hwrite).
  auto.
Qed.

Lemma stack_rel_drop' : forall n stk1 stk2 m sp,
    stack_rel m sp (stk1 ++ stk2) ->
    List.length stk1 = n ->
    stack_rel m (sp + Z.of_nat n) (stk2).
Proof.
  induction n. intros.
  - destruct stk1.
    + simpl in *.
      replace(sp+0) with sp by lia.
      assumption.
    + unfold length in H0.
      lia.
  - assert (IHn1 : forall (stk1 stk2 : list Z) m (sp : Z),
      stack_rel m sp (stk1 ++ stk2) ->
      length stk1 = 1%nat -> stack_rel m (sp + 1) stk2).
    + intros.
      destruct stk1.
      - simpl in H0. lia.
      - simpl in H.
        pose(Hlength := app_length (z::nil) stk1).
        change (length (z::nil)) with 1%nat in Hlength.
        change((z::nil) ++ stk1) with (z::stk1) in Hlength.
        assert(length stk1 = 0%nat). lia.
        assert(stk1 = nil).
          + destruct stk1. reflexivity.
          + simpl in H1. lia.
        rewrite H2 in H.
        simpl in H.
        destruct H as [_ H]. assumption.
    intros. 
    destruct stk1.
    + simpl in H0. lia.
    + assert(Hlength : length (z::nil) = 1%nat). simpl. reflexivity.
      specialize (IHn1 (z::nil) (stk1 ++ stk2) m sp H Hlength).
      simpl in H0.
      assert(length stk1 = n). lia.
      specialize (IHn stk1 stk2 m (sp+1) IHn1 H1).
      replace (sp + 1 + Z.of_nat n) with (sp + Z.of_nat (S n)) in IHn by lia.
      assumption.
Qed.

Theorem stack_rel_drop : forall i n m eid sp stk1 stk2,
    0 <= i ->
    eid > 0 ->
    mops_at eid MTableModel.LocationType_Stack = 0 ->    
    stack_rel (stk_map eid) (sp+m+1) (stk1++stk2) ->
    etable_values eid_cell i = eid ->
    etable_values sp_cell i  = sp ->
    List.length stk1 = n ->
  stack_rel (stk_map (eid+1)) (sp + m + 1 + Z.of_nat n) (stk2).
Proof.
  intros i n m eid sp stk1 stk2.
  intros Hrange Heid_nonzero Hmops Hrel Heid Hsp Hn.
  pose(Hdrop := mtable_no_write eid MTableModel.LocationType_Stack empty Heid_nonzero Hmops).
  change (gather_entries (eid + 1) MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
    with (stk_map (eid + 1)) in Hdrop.
  change (gather_entries eid MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
    with (stk_map eid) in Hdrop.
  rewrite Hdrop.
  eapply(stack_rel_drop').
    - eapply Hrel.
    - apply Hn.
Qed.  

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
Proof.
  intros i u st stk.
  intros Hrange Heid_nonzero Hrow_enabled Hmop_stack Hmop_global Hmop_heap Hrel Hstk Hsp Hmpages Hframe_id Hfid Hpc.
  destruct Hrel.
  rewrite Hstk in *.
  constructor.
  - assumption.
  - simpl in *.
    rewrite Hsp.
    rewrite eid_change by (auto;lia).
    replace (etable_values sp_cell i + 1 + 1) with (etable_values sp_cell i + 0 + 1 + Z.of_nat 1) by lia.
    eapply stack_rel_drop with (stk1:=u::nil) (m:=0); auto; try lia.
    rewrite stack_update_stack_incr_iid.
    rewrite Z.add_0_r.
    destruct st; simpl; auto.
  - rewrite eid_change by (auto;lia).
    rewrite globals_no_write; auto.
    rewrite globals_update_stack_incr_iid.
    rewrite globals_update_stack; auto.    
  - rewrite eid_change by (auto;lia).
    rewrite Hmpages.
    rewrite memory_no_write; auto.
    rewrite memory_update_stack_incr_iid.
    rewrite memory_update_stack; auto.    
    rewrite maximal_memory_pages_change; auto.    
  - rewrite Hframe_id, Hfid, callstack_update_stack, callstack_incr_iid; auto.
Qed.

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
Proof.
  intros col i n m offset is_i32 value enable eid stk1 stk2.
  intros Hrange Heid_nonzero Hmops Hnrange Henable His32_bit Hrel Heid Hoffset Hn Hwrite.
  apply alloc_memory_table_lookup_write_cell_correct 
    with (i := i)
    in Hwrite; auto; try lia.
  assert(Hdrop : stack_rel (stk_map eid) (etable_values sp_cell i + m + 1 + Z.of_nat n) stk2).
  - apply stack_rel_drop' with (stk1:=stk1); auto.
  { apply mtable_write with (init:=empty) in Hwrite.
    - rewrite Heid in *.
      change (gather_entries (eid + 1) MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
        with (stk_map (eid+1)) in Hwrite.
      change (gather_entries eid MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty)
        with (stk_map eid) in Hwrite.
      rewrite Hwrite.
      rewrite Hoffset in *.
      remember (value (fun c : etable_cols => etable_values c i)) as u.
      replace(etable_values sp_cell i + m + 1 + Z.of_nat n) with 
        (etable_values sp_cell i + m + Z.of_nat n + 1) in Hdrop by lia.
      apply stack_rel_write_negative' with (u:=u); auto.
    - rewrite Heid; lia.
    - rewrite Heid; lia.
  }
  - pose (eid_common i); lia.
  - pose (sp_common i); lia.
Qed.

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
Proof.
  intros col i sp is_i32 enable loctyp Hrange Hsp Hi32 Henable Hlt Hm.
  pose(Hw := writev_lookup _ _ _ _ _ _ Hm i).
  pose(Hg := writev_gate _ _ _ _ _ _ Hm i Hrange); simpl in Hg.
  destruct Hw as [i0 [Hi0 Hw]].
  destruct Hw as [_ [_ [Hencode Hval]]].
  destruct Hg as [Hg _].
  rewrite <- Hval.
  pose(Hmc8 := MTableModel.gate_mc8 i0 Hi0).
  pose(Hmc9 := MTableModel.gate_mc9 i0 Hi0).
  pose(Hmc12 := MTableModel.gate_mc12 i0 Hi0).
  simpl in Hmc8, Hmc9, Hmc12.
  replace(i0+0) with i0 in * by lia.
  pose(H0 := MTableModel.value_u16_cells_le0_U16 i0).
  pose(H1 := MTableModel.value_u16_cells_le1_U16 i0).
  pose(H2 := MTableModel.value_u16_cells_le2_U16 i0).
  pose(H3 := MTableModel.value_u16_cells_le3_U16 i0).
  destruct Hi32 as [Hi320 | Hi321].
  - rewrite Hi320; lia.
  - assert (Hisi32 : MTableModel.mtable_values MTableModel.is_i32_cell i0 = 
           (is_i32 (fun c : etable_cols => etable_values c i))).
    - eapply lookup_encode with (offset := sp (fun c: etable_cols => etable_values c i))
                                (loc_typ := loctyp); auto.
      lia.
    rewrite Hisi32 in Hmc8.
    rewrite Hi321 in *.
    lia.
Qed.

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
Proof.
  intros col i sp is_i32 value enable loctyp Hrange Hsp Hi32 Henable Hlp Hm.
  pose(Hw := ETableModel.read_lookup _ _ _ _ _ _ _ Hm i).
  pose(Hg := ETableModel.read_gate _ _ _ _ _ _ _ Hm i Hrange); simpl in Hg.
  destruct Hw as [i0 [Hi0 Hw]].
  destruct Hw as [_ [_ [Hencode Hval]]].
  destruct Hg as [_ [_ [Hg Hv]]].
  rewrite <- Hval in Hv.
  replace (value (fun c : etable_cols => etable_values c i)) with
    (MTableModel.mtable_values MTableModel.value_u64_cell i0) by lia.
  pose(Hmc8 := MTableModel.gate_mc8 i0 Hi0).
  pose(Hmc9 := MTableModel.gate_mc9 i0 Hi0).
  pose(Hmc12 := MTableModel.gate_mc12 i0 Hi0).
  simpl in Hmc8, Hmc9, Hmc12.
  replace(i0+0) with i0 in * by lia.
  pose(H0 := MTableModel.value_u16_cells_le0_U16 i0).
  pose(H1 := MTableModel.value_u16_cells_le1_U16 i0).
  pose(H2 := MTableModel.value_u16_cells_le2_U16 i0).
  pose(H3 := MTableModel.value_u16_cells_le3_U16 i0).
  destruct Hi32 as [Hi320 | Hi321].
  - rewrite Hi320; lia.
  - assert (Hisi32 : MTableModel.mtable_values MTableModel.is_i32_cell i0 = 
           (is_i32 (fun c : etable_cols => etable_values c i))).
    - eapply lookup_encode with (offset := sp (fun c: etable_cols => etable_values c i))
                                (loc_typ := loctyp); auto.
      lia.
    rewrite Hisi32 in Hmc8.
    rewrite Hi321 in *.
    lia.
Qed.

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
Proof.
  intros col i sp is_i32 enable loctyp Hrange Hsp Hi32 Henable Hlt Hm.
  pose(Hw := ETableModel.readv_lookup _ _ _ _ _ _ Hm i).
  pose(Hg := ETableModel.readv_gate _ _ _ _ _ _ Hm i Hrange); simpl in Hg.
  destruct Hw as [i0 [Hi0 Hw]].
  destruct Hw as [_ [_ [Hencode Hval]]].
  destruct Hg as [_ [_ Hg]].
  replace (etable_values (col AMTLRC_value_cell) i) with
    (MTableModel.mtable_values MTableModel.value_u64_cell i0) by lia.
  pose(Hmc8 := MTableModel.gate_mc8 i0 Hi0).
  pose(Hmc9 := MTableModel.gate_mc9 i0 Hi0).
  pose(Hmc12 := MTableModel.gate_mc12 i0 Hi0).
  simpl in Hmc8, Hmc9, Hmc12.
  replace(i0+0) with i0 in * by lia.
  pose(H0 := MTableModel.value_u16_cells_le0_U16 i0).
  pose(H1 := MTableModel.value_u16_cells_le1_U16 i0).
  pose(H2 := MTableModel.value_u16_cells_le2_U16 i0).
  pose(H3 := MTableModel.value_u16_cells_le3_U16 i0).
  destruct Hi32 as [Hi320 | Hi321].
  - rewrite Hi320; lia.
  - assert (Hisi32 : MTableModel.mtable_values MTableModel.is_i32_cell i0 = 
           (is_i32 (fun c : etable_cols => etable_values c i))).
    - eapply lookup_encode with (offset := sp (fun c: etable_cols => etable_values c i))
                                (loc_typ := loctyp); auto.
      lia.
    rewrite Hisi32 in Hmc8.
    rewrite Hi321 in *.
    lia.
Qed.

