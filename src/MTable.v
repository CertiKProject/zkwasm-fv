(* Copyright (C) CertiK 2024-2026 *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import CommonModel.
Require Import ImageTableModel.
Require Import MTableModel.

Open Scope Z_scope.

Lemma enabled_lt_numRow : forall i,
    0 <= i -> 
    mtable_values enabled_cell i = 1 ->
    i < mtable_numRow.
Proof.
  intros.
  destruct (Z_lt_le_dec i mtable_numRow) as [Hl | Hl]; auto.
  apply mtable_end in Hl.
  congruence.
Qed.
       
Lemma circuit_if : forall x y,
    x <> 0 ->
    x*y = 0 ->
    y = 0.
Proof.
  intros; lia.
Qed.

Lemma circuit_eq : forall x y,
    x - y = 0 ->
    x = y.
Proof.
  lia.
Qed.

Lemma circuit_or : forall x y,
    x*y = 0 -> (x=0 \/ y=0).
Proof.
  lia.
Qed.

Lemma circuit_symm : forall x y,
    x*y = y*x.
Proof.
  lia.
Qed.
  
Lemma enabled_seq_mono : forall i,
    0 <= i ->
    mtable_values enabled_cell i = 0 ->
    forall j, i <= j -> mtable_values enabled_cell j = 0.
Proof.  
  intros i irange  Hi j Hj.
  replace j with (i + (j-i)) by lia.
  replace (j-i) with (Z.of_nat (Z.to_nat (j-i)))
                     by (apply Z2Nat.id; lia).
  remember (Z.to_nat (j - i)) as n.
  clear j Hj Heqn.
  induction n.
  - simpl. replace (i+0) with i by lia. auto.
  - rewrite Nat2Z.inj_succ.
    assert (H := gate_mc1 (i + Z.of_nat n) ltac:(lia)).
    destruct H as [H _].
    replace (i + Z.of_nat n + 0) with (i + Z.of_nat n) in H by lia.
    simpl in H.
    rewrite IHn in H.
    apply circuit_if in H; [|lia].
    replace (i + Z.succ (Z.of_nat n)) with (i + Z.of_nat n + 1) by lia.
    apply H.
Qed.    

Definition entry_type i : Z :=
       if Z.eqb (mtable_values is_stack_cell i) 1 then LocationType_Stack
  else if Z.eqb (mtable_values is_heap_cell  i) 1  then LocationType_Heap
  else LocationType_Global.

Lemma ltype_unique : forall i,
    0 <= i ->
    mtable_values enabled_cell i = 1 ->
      (entry_type i = LocationType_Global /\ mtable_values is_global_cell i = 1 /\ mtable_values is_heap_cell i = 0 /\ mtable_values is_stack_cell i = 0)
    \/ (entry_type i = LocationType_Heap /\ mtable_values is_global_cell i = 0 /\ mtable_values is_heap_cell i = 1 /\ mtable_values is_stack_cell i = 0)
      \/ (entry_type i = LocationType_Stack /\ mtable_values is_global_cell i = 0 /\ mtable_values is_heap_cell i = 0 /\ mtable_values is_stack_cell i = 1).
Proof.
  intros i Hrange Henabled.
  pose (Hmc2 := gate_mc2 i Hrange).
  simpl in Hmc2.
  replace (i+0) with i in * by lia.
  destruct Hmc2 as [Hmc2 _].
  unfold entry_type.
  destruct (is_global_bit i); 
  destruct (is_heap_bit i); 
  destruct (is_stack_bit i); 
  rewrite H, H0, H1; simpl; lia.
Qed.

Lemma entry_type_le : forall i,
    0 <= i ->
    mtable_values enabled_cell i = 1 ->
    mtable_values enabled_cell (i+1) = 1 ->
    entry_type i <= entry_type (i+1).
Proof.
  intros i Hrange Henabled Henabled'.
  destruct (ltype_unique i Hrange Henabled) as [[H1 [H2 [H3 H4]]] | [[H1 [H2 [H3 H4]]] | [H1 [H2 [H3 H4]]]]];
  destruct (ltype_unique (i+1) ltac:(lia) Henabled') as [[H1' [H2' [H3' H4']]] | [[H1' [H2' [H3' H4']]] | [H1' [H2' [H3' H4']]]]];
    rewrite H1, H1'; try lia;
  pose (Hmc3 := gate_mc3 i Hrange);
  simpl in Hmc3;
  destruct Hmc3 as [? [? _]];
  replace (i+0) with i in * by lia;
  try unfold LocationType_Stack; try unfold LocationType_Heap; try unfold LocationType_Global;
  try lia.
Qed.

Lemma is_next_same_ltype : forall i,
    0 <= i ->
    mtable_values enabled_cell i = 1 ->
    mtable_values enabled_cell (i+1) = 1 ->
    (mtable_values is_next_same_ltype_cell i = 1 
     <-> entry_type i = entry_type (i+1)).
Proof.
  intros i Hrange Henabled0 Henabled1.
  assert (Hmc4a := gate_mc4a i Hrange).
  destruct Hmc4a as [Hmc4a _].
  replace (i+0) with i in * by lia.
  simpl in Hmc4a.
  destruct (ltype_unique i Hrange Henabled0) as [[H1 [H2 [H3 H4]]] | [[H1 [H2 [H3 H4]]] | [H1 [H2 [H3 H4]]]]];
    destruct (ltype_unique (i+1) ltac:(lia) Henabled1) as [[H1' [H2' [H3' H4']]] | [[H1' [H2' [H3' H4']]] | [H1' [H2' [H3' H4']]]]];
  try unfold LocationType_Global in *; try unfold LocationType_Heap in *; try unfold LocationType_Stack in *;  
  split; intros; try lia.
Qed.

Lemma is_next_same_offset : forall i,
  0 <= i ->
  mtable_values enabled_cell i = 1 ->
  mtable_values enabled_cell (i+1) = 1 ->
  entry_type i = entry_type (i+1) ->
  (mtable_values is_next_same_offset_cell i = 1 
   <->  mtable_values offset_cell i = mtable_values offset_cell (i+1)).
Proof.
  intros i Hrange Henabled Henabled_next Hsame_entry.
  pose(Hcommon := CommonModel.common_lt_order).
  simpl Z.shiftl in Hcommon.
  pose(Hgate := gate_mc4b i Hrange); simpl in Hgate.
  pose(Hoffset_diff := gate_mc5 i Hrange); simpl in Hoffset_diff.
  replace(i+0) with i in * by lia.
  apply is_next_same_ltype in Hsame_entry; auto.
  destruct Hgate as [_ [Hod [Hinv [Hsame _]]]].
  split.
  - intros Hsame_offset.
    assert(mtable_values offset_diff_cell i = 0).
    - pose(offset_diff_common i).
      rewrite Z.mod_small in Hod; lia.
    lia.
  - intros Hsame_offset.
    assert(mtable_values offset_diff_cell i = 0) by lia.
    rewrite H in Hinv.
    rewrite Z.mul_0_l in Hinv.
    rewrite Z.sub_0_l in Hinv.
    pose(Hdiff_inv := Z_mod_zero_opp_full _ _ Hinv).
    rewrite Z.opp_involutive in Hdiff_inv.
    rewrite Hsame_entry in Hsame.
    destruct(is_next_same_offset_bit i); auto.
    rewrite H0 in Hsame.
    replace((0 - 1) * 1) with (-1) in Hsame by lia.
    replace(-1 * (mtable_values offset_diff_inv_helper_cell i - 1)) with
      (1 - mtable_values offset_diff_inv_helper_cell i) in Hsame by lia.
    rewrite Zminus_mod in Hsame.
    rewrite Hdiff_inv in Hsame.
    rewrite Z.sub_0_r in Hsame.
    rewrite Zmod_mod in Hsame.
    rewrite Z.mod_small in Hsame by lia.
    lia.
Qed.

Lemma offset_sort : forall i,
  0 <= i ->
  mtable_values enabled_cell i = 1 ->
  mtable_values enabled_cell (i+1) = 1 ->
  entry_type i = entry_type (i+1) ->
  mtable_values offset_cell i <= mtable_values offset_cell (i+1).
Proof.
  intros i Hrange Henabled0 Henabled1 Hsame_ltype.
  rewrite <- is_next_same_ltype in Hsame_ltype by auto.
  assert (Hmc5 := gate_mc5 i Hrange).
  destruct Hmc5 as [Hmc5 _].
  replace (i+0) with i in * by lia.
  simpl in Hmc5.
  rewrite circuit_symm in Hmc5.
  apply circuit_if in Hmc5; [|congruence].
  pose (offset_diff_common i).
  lia.
Qed.

Lemma eid_sort1 : forall i,
  0 <= i ->
  mtable_values enabled_cell i = 1 ->
  mtable_values enabled_cell (i+1) = 1 ->
  entry_type i = entry_type (i+1) ->
  mtable_values start_eid_cell i < mtable_values end_eid_cell i.
Proof.
  intros i Hrange Henabled0 Henabled1 Hsame_ltype.
  assert (Hmc6 := gate_mc6 i Hrange).
  destruct Hmc6 as [Hmc6 _].
  replace (i+0) with i in * by lia.
  simpl in Hmc6.
  rewrite <- is_next_same_ltype in Hsame_ltype by auto.  
  pose (eid_diff_common i).
  lia.
Qed.
  
Lemma eid_sort2 : forall i,
  0 <= i ->
  mtable_values enabled_cell i = 1 ->
  mtable_values enabled_cell (i+1) = 1 ->
  entry_type i = entry_type (i+1) ->
  mtable_values offset_cell i = mtable_values offset_cell (i+1) ->
  mtable_values end_eid_cell i = mtable_values start_eid_cell (i+1).
Proof.
  intros i Hrange Henabled0 Henabled1 Hsame_ltype Hsame_offset.
  assert (Hmc6 := gate_mc6 i Hrange).
  destruct Hmc6 as [_ [Hmc6 _]].
  replace (i+0) with i in * by lia.
  simpl in Hmc6.
  rewrite <- is_next_same_offset in Hsame_offset by auto.
  rewrite Hsame_offset in Hmc6.
  pose (eid_diff_common i).
  lia.
Qed.

Definition entry_lt i j : Prop :=
    mtable_values enabled_cell i > mtable_values enabled_cell j
    \/ (mtable_values enabled_cell i = mtable_values enabled_cell j
        /\  entry_type i < entry_type j)
    \/ (mtable_values enabled_cell i = mtable_values enabled_cell j
        /\ entry_type i = entry_type j
        /\ mtable_values offset_cell i < mtable_values offset_cell j)
    \/ (mtable_values enabled_cell i = mtable_values enabled_cell j
        /\ entry_type i = entry_type j
        /\ mtable_values offset_cell i = mtable_values offset_cell j
        /\ mtable_values start_eid_cell i < mtable_values end_eid_cell i <= mtable_values start_eid_cell j).

Lemma entry_lt_trans : forall i j k,
    entry_lt i j -> entry_lt j k -> entry_lt i k.
Proof.
  unfold entry_lt.
  intros i j k H1 H2.
  destruct H1 as [? | [? | ?]]; 
  destruct H2 as [? | [? | ?]]; lia.
Qed.

Lemma le_lt_or_eq : forall i j,
    i <= j -> (i < j \/ i = j).
Proof.
  intros. lia.
Qed.  

Theorem mtable_sorted : forall i,
    0 <= i ->
    mtable_values enabled_cell i = 1 ->
    entry_lt i (i+1).
Proof.  
  intros i Hrange Henabled.
  unfold entry_lt.
  destruct (enabled_bit (i+1)) as [Henabled1 | Henabled1].
  - left. lia.
  - right.    
    destruct (le_lt_or_eq _ _ (entry_type_le i Hrange Henabled Henabled1)) as [Hltype | Hltype].
    + left. split; try congruence; auto.
    + right.
      destruct (le_lt_or_eq _ _ (offset_sort i Hrange Henabled Henabled1 Hltype)) as [Hoffset | Hoffset].
      * left. split; try congruence; eauto.
      * right.
        split; try congruence.
        split; auto.
        split; auto.
        split.
        { auto using eid_sort1. }
        { pose (eid_sort2 i Hrange Henabled Henabled1 Hltype Hoffset).
          lia. }
Qed.

Lemma mtable_sorted_further' : forall n i,
    0 <= i  ->
    mtable_values enabled_cell i = 1 ->
    entry_lt i (i + 1 + Z.of_nat n).
Proof.
  induction n.
  - intros.
    replace (i + 1 + Z.of_nat 0) with (i+1) by lia.
    apply mtable_sorted; auto.
  - intros.
    destruct (enabled_bit (i+1)) as [Henabled|Henabled].
    + assert (Henabled' := enabled_seq_mono (i+1) ltac:(lia) Henabled(i + 1 + Z.of_nat (S n)) ltac:(lia)).
      left.
      lia.
    + apply entry_lt_trans with (j := i+1).
      apply mtable_sorted; auto.
      replace (i + 1 + Z.of_nat (S n)) with (i + 1 + 1 + Z.of_nat n) by lia.
      apply IHn; auto; lia.
Qed.      
      
Lemma mtable_sorted_further : forall i j,
    0 <= i < j ->
    mtable_values enabled_cell i = 1 ->
    entry_lt i j.
Proof.
  intros i j Hrange Henabled.
  replace j with (i + 1 + Z.of_nat (Z.to_nat (j - i - 1))) by lia.
  apply mtable_sorted_further'; lia.
Qed.

Lemma mtable_sorted_by_offset : forall i j,
    0 <= i ->
    0 <= j ->
    mtable_values enabled_cell i = 1 ->
    mtable_values enabled_cell j = 1 ->
    entry_type i = entry_type j ->
    mtable_values offset_cell i < mtable_values offset_cell j ->
    i < j.
Proof.
  intros i j Hirange Hjrange Hienabled Hjenabled Htype Hoffset.
  destruct (Z_lt_le_dec i j); [auto|].
  destruct (Z_lt_le_dec j i).
  - destruct (mtable_sorted_further j i ltac:(lia) Hjenabled) as
      [Hlt | [Hlt | [Hlt | Hlt]]]; lia.
  - replace j with i in * by lia.
    lia.
Qed.    
  
Lemma nonzero_eid_not_init : forall i,
    0 <= i ->
    mtable_values start_eid_cell i <> 0 ->
    mtable_values is_init_cell i = 0.
Proof.
  intros i Hrange Heid.
  pose (Hmc7 := gate_mc7 i Hrange).
  destruct Hmc7 as [Hmc7 _].
  replace (i+0) with i in * by lia.
  simpl in *.
  lia.
Qed.

Lemma ltype_formula : forall i,
    0 <= i ->
    mtable_values enabled_cell i = 1 ->
    entry_type i = 
    mtable_values is_stack_cell i * LocationType_Stack + mtable_values is_global_cell i * LocationType_Global + mtable_values is_heap_cell i * LocationType_Heap.
Proof.
  intros i Hrange Henabled.
  destruct (ltype_unique i Hrange Henabled) as [[? [? [? ?]]] | [[? [? [? ?]]] | [? [? [? ?]]]]];
    simpl;
    rewrite H, H0, H1, H2; lia.
Qed.

Lemma init_offsets : forall i,
    0 <= i ->
    mtable_values is_init_cell i = 1  ->
    mtable_values offset_align_left_cell i <= mtable_values offset_cell i <= mtable_values offset_align_right_cell i.
  Proof.
    intros i Hrange Hinit.
    destruct (gate_mc7 i Hrange) as [Hmc7_1 [Hmc7_2 [Hmc7_3 _]]].
    replace (i+0) with i in * by lia.
    simpl in *.
    rewrite Hinit in *.
    pose (offset_align_left_common i).
    pose (offset_align_right_common i).
    pose (offset_align_left_diff_common i).
    pose (offset_align_right_diff_common i).
    pose (offset_common i).
    lia.
  Qed.

  Lemma init_lookup_encoded : forall i,
      0 <= i ->
      mtable_values enabled_cell i = 1 ->
      mtable_values is_init_cell i = 1  ->
      exists j mut k1 k2,
        k1 <= mtable_values offset_cell i <= k2
        /\ image_table_values col j 
           = encode_init_memory_table_entry (entry_type i) mut k1 k2 (mtable_values value_u64_cell i).
  Proof.
    intros i Hrange Henabled Hinit.
    assert (Hlookup := init_memory_lookup i (mtable_values init_encode_cell i) eq_refl).
    destruct Hlookup as [j Hlookup].

    assert (Hmc7c := gate_mc7c i Hrange).
    destruct Hmc7c as [Hmc7c _].
    replace (i+0) with i in * by lia.
    simpl in *.
    replace (mtable_values is_stack_cell i * LocationType_Stack +
             mtable_values is_heap_cell i * LocationType_Heap +
               mtable_values is_global_cell i * LocationType_Global)
      with (entry_type i) in Hmc7c
        by (rewrite ltype_formula; auto; lia).
    exists j.
    exists (mtable_values is_mutable_cell i).
    exists (mtable_values offset_align_left_cell i).
    exists (mtable_values offset_align_right_cell i).
    split.
    - apply init_offsets; auto.
    - lia.
  Qed.
  
(* Translation of the constraints for alloc_memory_table_lookup_read_cell *)
Record memory_table_lookup_read_cell (eid location_type offset is_i32 value :Z) := {
    read_eid_common : 0 <= eid < common;
    read_location_type : location_type = LocationType_Stack \/
                         location_type = LocationType_Heap \/
                         location_type = LocationType_Global;
    read_is_i32_bit : is_i32 = 0 \/ is_i32 = 1;
    read_offset_common:  0 <= offset < 2 * common + 10;
    
    read_encode_cell : Z;
    read_start_eid_cell: Z;
    read_end_eid_cell: Z;
    read_value_cell: Z;
    read_start_eid_diff_cell : Z;
    read_start_eid_diff_common : 0 <= read_start_eid_diff_cell < common;
    read_end_eid_diff_cell : Z;

    read_lookup: exists i,
       0 <= i
    /\ mtable_values start_eid_cell i = read_start_eid_cell
    /\ mtable_values end_eid_cell i = read_end_eid_cell
    /\ mtable_values encode_cell i = read_encode_cell
    /\ mtable_values value_u64_cell i = read_value_cell;
                                       
    read_end_eid_diff_common : 0 <= read_end_eid_diff_cell < common;
    read_gate1: eid - read_start_eid_cell - read_start_eid_diff_cell - 1 = 0;
    read_gate2: eid + read_end_eid_diff_cell - read_end_eid_cell = 0;
    read_gate3: (encode_memory_table_entry offset location_type is_i32) - read_encode_cell = 0;
    read_gate4: read_value_cell - value = 0
  }.


(* Translation of the constraints for alloc_memory_table_lookup_write_cell *)
Record memory_table_lookup_write_cell (eid location_type offset is_i32 value :Z) := {
    write_eid_common : 0 <= eid < common;
    write_location_type : location_type = LocationType_Stack \/
                         location_type = LocationType_Heap \/
                         location_type = LocationType_Global;
    write_is_i32_bit : is_i32 = 0 \/ is_i32 = 1;
    write_offset_common:  0 <= offset < 2 * common + 10;

    write_start_eid_cell: Z;
    write_end_eid_cell: Z;
    write_encode_cell : Z;
    write_value_cell: Z;

    write_lookup: exists i,
       0 <= i
    /\ mtable_values start_eid_cell i = write_start_eid_cell
    /\ mtable_values end_eid_cell i = write_end_eid_cell
    /\ mtable_values encode_cell i = write_encode_cell
    /\ mtable_values value_u64_cell i = write_value_cell;

    write_gate1: (encode_memory_table_entry offset location_type is_i32) - write_encode_cell = 0;
    write_gate2: write_start_eid_cell - eid = 0;
    write_gate3: write_value_cell - value = 0
  }.

(* the "plus 10" is enough to look in the top items of the stack. *)
Lemma encode_memory_table_entry_inj : forall offset offset' loc_typ loc_typ' is_i32 is_i32' ,
    0 <= offset  < 2 * common + 10 ->
    0 <= offset' < 2 * common + 10 ->
    loc_typ = LocationType_Stack \/ loc_typ = LocationType_Heap \/ loc_typ = LocationType_Global ->
    loc_typ'= LocationType_Stack \/ loc_typ'= LocationType_Heap \/ loc_typ'= LocationType_Global ->
    is_i32 = 0 \/ is_i32 = 1 ->
    is_i32' = 0 \/ is_i32' = 1 ->        
    encode_memory_table_entry offset loc_typ is_i32 = encode_memory_table_entry offset' loc_typ' is_i32' ->
    (offset = offset' /\ loc_typ = loc_typ' /\ is_i32 = is_i32').
  Proof.
    intros.
    unfold encode_memory_table_entry in *.
    unfold COMMON_RANGE_OFFSET in *.
    simpl in *.
    assert (1 <= loc_typ < 4) by (compute in H1; lia).
    assert (1 <= loc_typ' < 4) by (compute in H2; lia).
    assert (0 <= is_i32 < 2) by lia.
    assert (0 <= is_i32' < 2) by lia.

    rewrite Zmod_small in H5.
    2: {
      assert (Hcommon := common_lt_order).
      simpl in Hcommon.
      lia.
    }
    rewrite Zmod_small in H5.
    2: {
      assert (Hcommon := common_lt_order).
      simpl in Hcommon.
      lia.
    }
    lia.
  Qed.

  (* So far, we have not needed to prove anything about initialization. *)
  (*
L\emma encode_init_memory_table_entry_inj : forall ltype ltype' is_mutable is_mutable' start_offset start_offset' end_offset end_offset' value value',
    ltype = LocationType_Stack \/ ltype= LocationType_Heap  \/ ltype = LocationType_Global ->
    ltype'= LocationType_Stack \/ ltype'= LocationType_Heap \/ ltype'= LocationType_Global ->
    is_mutable = 0 \/ is_mutable = 1 ->
    is_mutable' = 0 \/ is_mutable' = 1 ->
    0 <= start_offset < common ->
    0 <= start_offset' < common ->
    0 <= end_offset < common ->
    0 <= end_offset' < common ->
    (* value range *)
      encode_init_memory_table_entry ltype  is_mutable start_offset  end_offset  value
    = encode_init_memory_table_entry ltype' is_mutable start_offset' end_offset' value' ->
    (ltype = ltype' /\ is_mutable = is_mutable' /\ start_offset = start_offset' /\ end_offset=end_offset' /\ value=value').
Abort.
*)


Theorem lookup_encode : forall i offset loc_typ is_i32,
    0 <= i ->
    0 <= offset < 2 * common + 10 -> 
    loc_typ = LocationType_Stack \/ loc_typ = LocationType_Heap \/ loc_typ = LocationType_Global ->
    is_i32 = 0 \/ is_i32 = 1 ->
    mtable_values encode_cell i = encode_memory_table_entry offset loc_typ is_i32 ->
          mtable_values enabled_cell i = 1    
       /\ mtable_values offset_cell i = offset
       /\ entry_type i = loc_typ
       /\ mtable_values is_i32_cell i = is_i32.
Proof.
  intros i offset loc_typ is_i32 Hrange Hoffset_common Hloc_type His_i32_bit Hencode.
  assert (Hmc12 := gate_mc12 i Hrange).
  destruct Hmc12 as [Hmc12_1 [Hmc12_2 _]].
  replace (i+0) with i in * by lia.
  assert (Henabled : mtable_values enabled_cell i = 1).
  {
    destruct (enabled_bit i); auto.
    change LocationType_Stack with 1 in Hloc_type.
    change LocationType_Heap with 2 in Hloc_type.
    change LocationType_Global with 3 in Hloc_type.
    simpl value in *.
    rewrite H in Hmc12_1.
    replace(mtable_values encode_cell i) with 0 in Hencode by lia.
    unfold encode_memory_table_entry in Hencode.
    pose(Hlt := common_lt_order).
    simpl Z.shiftl in *.
    rewrite(Z.mod_small _ _) in Hencode by lia.
    lia.
  }
  clear Hmc12_1.
  replace (mtable_values encode_cell i) with
    (encode_memory_table_entry (value mtable offset_cell i)
              (value mtable is_stack_cell i * LocationType_Stack + value mtable is_global_cell i * LocationType_Global + value mtable is_heap_cell i * LocationType_Heap)
              (value mtable is_i32_cell i)) in Hencode
      by (simpl in *; lia).
  clear Hmc12_2.
  Opaque Z.add Z.sub Z.mul.
  simpl in Hencode.
  rewrite <- (ltype_formula i Hrange Henabled) in Hencode.
  apply encode_memory_table_entry_inj in Hencode; auto.
  - pose (offset_common i); lia.
  - destruct (ltype_unique i Hrange Henabled) as [[? [? [? ?]]] | [[? [? [? ?]]] | [? [? [? ?]]]]]; auto.
  - apply (is_i32_bit i).
Qed.

Theorem memory_table_lookup_read : forall eid loc_typ offset is_i32 value,
    memory_table_lookup_read_cell eid loc_typ offset is_i32 value ->
    exists i,
       0 <= i
    /\ mtable_values enabled_cell i = 1
    /\ mtable_values start_eid_cell i < eid <= mtable_values end_eid_cell i
    /\ mtable_values value_u64_cell i = value      
    /\ mtable_values offset_cell i = offset      
    /\ entry_type i = loc_typ
    /\ mtable_values is_i32_cell i = is_i32.
Proof.
  destruct 1.
  destruct read_lookup0 as [i [Hstart [Hend [Hencode Hvalue]]]].
  exists i.
  destruct (lookup_encode i offset loc_typ is_i32) as [? [? [? ?]]]; auto; try lia.
Qed.

Theorem memory_table_lookup_write: forall eid loc_typ offset is_i32 value,
    memory_table_lookup_write_cell eid loc_typ offset is_i32 value ->
    exists i,
       0 <= i
    /\ mtable_values enabled_cell i = 1
    /\ mtable_values start_eid_cell i = eid
    /\ mtable_values value_u64_cell i = value      
    /\ mtable_values offset_cell i = offset      
    /\ entry_type i = loc_typ
    /\ mtable_values is_i32_cell i = is_i32.
Proof.
  destruct 1.
  destruct write_lookup0 as [i [Hrange [Hstart [Hend [Hencode Hvalue]]]]].
  exists i.
  destruct (lookup_encode i offset loc_typ is_i32) as [? [? [? ?]]]; auto; try lia.
Qed.

Require Import Bool.

Section gather_mops. 
  
  Section gather.
  Variable min_eid max_eid :Z.
  Variable type : Z.
  
  Fixpoint gather_mops' (i : Z) (n:nat) :=
    match n with
    | O => 0
    | S n' =>
        if (mtable_values enabled_cell i =? 1) 
        then         
            (if
              (type =? (entry_type i))
              && ((mtable_values is_init_cell i) =? 0)
              && (min_eid <=? (mtable_values start_eid_cell i))
              && ((mtable_values start_eid_cell i) <? max_eid)
             then 1
             else 0) + gather_mops' (i+1) n'
        else
          0
    end.

  Definition gather_mops (from to : Z) :=
    gather_mops' from (Z.to_nat (to - from)).

  Lemma gather_mops_nonenabled : forall n i j,
      mtable_values enabled_cell i = 0 ->
      0 <= i <= j ->
       gather_mops' j n = 0.
  Proof.
    induction n.
    - intros; simpl; auto.
    - intros i j Henabled Hj.
      simpl.
      rewrite (enabled_seq_mono i ltac:(lia) Henabled j ltac:(lia)).
      reflexivity.
  Qed.

  Lemma gather_mops_nonnegative' : forall n i,
      0 <= gather_mops' i n.
  Proof.
    induction n.
    - simpl; lia.
    - intros; simpl.
      specialize (IHn (i+1)).
      destruct (mtable_values enabled_cell i =? 1);
      destruct ( (type =? entry_type i) && (mtable_values is_init_cell i =? 0) &&
                   (min_eid <=? mtable_values start_eid_cell i) && (mtable_values start_eid_cell i <? max_eid)); simpl;
        try lia.
  Qed.

  Lemma gather_mops_nonnegative : forall i j,
    0 <= gather_mops i j.
  Proof.
    intros. unfold gather_mops. auto using gather_mops_nonnegative'.
  Qed.

  Lemma gather_mops_append' : forall n m i,
      0 <= i ->
      gather_mops' i (n+m) =  (gather_mops' i n) + gather_mops' (i + Z.of_nat n) m.
  Proof.
    induction n.
    - intros.
      simpl.
      replace (i+0) with i by lia.
      lia.
    - rewrite Nat2Z.inj_succ.
      intros.
      simpl.
      destruct (enabled_bit i) as [Henabled|Henabled].
      + rewrite Henabled.
        simpl.
        rewrite gather_mops_nonenabled with (i:=i) (j:=i + Z.succ (Z.of_nat n)); auto.
        lia.
      + rewrite Henabled.
        rewrite Z.eqb_refl.
        rewrite IHn by lia.
        rewrite !Z.add_assoc.
        f_equal.
        f_equal.
        lia.
  Qed.                            

  Lemma gather_mops_append : forall i j k,
      0 <= i ->
      i <= j <= k ->
      gather_mops i k = (gather_mops i j) + gather_mops j k.
  Proof.
    intros.
    unfold gather_mops.    
    replace (k - i) with ((j - i) + (k - j)) by lia.
    rewrite Z2Nat.inj_add by lia.
    rewrite gather_mops_append' by lia.
    rewrite Z2Nat.id by lia.
    replace (i + (j - i)) with j by lia.
    auto.
  Qed.


  End gather.

  Lemma mops_split_range' : forall a b c type n i,
      a <= b <= c ->
      gather_mops' a c type i n =
        gather_mops' a b type i n + gather_mops' b c type i n.
  Proof.
    induction n; intros.
    - simpl. auto.
    - simpl.
      destruct (mtable_values enabled_cell i =? 1).
      2: now auto.
      destruct ((type =? entry_type i) && (mtable_values is_init_cell i =? 0)).
      2: { simpl.
           specialize (IHn (i+1) H).
           lia. }
      simpl.
      specialize (IHn (i+1) ltac:(lia)).
      destruct (a <=? mtable_values start_eid_cell i) eqn:Ha;
        destruct (mtable_values start_eid_cell i <? c) eqn:Hc;
        destruct (mtable_values start_eid_cell i <? b) eqn:Hb;
        destruct (b <=? mtable_values start_eid_cell i) eqn:Hbe;
        try rewrite Z.leb_le in *;
        try rewrite Z.leb_nle in *;
        try rewrite Z.ltb_lt in *;
        try rewrite Z.ltb_nlt in *; simpl; try lia.
  Qed.
        
  Lemma mops_split_range : forall a b c type i j,
      a <= b <= c ->
      gather_mops a c type i j =
      gather_mops a b type i j + gather_mops b c type i j.
  Proof.  
    unfold gather_mops.
    intros.
    eauto using mops_split_range'.
  Qed.    
    
  Lemma rest_mops_bound' : forall min_eid max_eid n i,
      0 <= i ->      
      gather_mops' min_eid max_eid LocationType_Stack    i n 
      + gather_mops' min_eid max_eid LocationType_Heap   i n
      + gather_mops' min_eid max_eid LocationType_Global i n
      <= mtable_values rest_mops_cell i.
  Proof.
    induction n; intros i Hrange.
    - simpl.
      pose (rest_mops_common i).
      lia.
    -
Opaque Z.eqb.
      simpl.
      destruct (mtable_values enabled_cell i =? 1) eqn:Henabled.
      2: { pose (rest_mops_common i). lia. }
      rewrite Z.eqb_eq in Henabled.

      destruct (is_init_bit i) as [Hinit|Hinit].
      + assert ( mtable_values rest_mops_cell i =  1+ mtable_values rest_mops_cell (i+1)).
        {
          pose (Hmc10b := gate_mc10b i Hrange).
          destruct Hmc10b as [_ [Hmc10b _]].
          replace (i + 0) with i in * by lia.
          simpl in Hmc10b.
          rewrite Hinit in Hmc10b.
          lia.
        }
        specialize (IHn (i+1) ltac:(lia)).
        destruct (ltype_unique i Hrange Henabled) as [[Htype _] | [[Htype _] | [Htype _]]].
        * rewrite Htype.
          replace (LocationType_Stack =? LocationType_Global) with false by reflexivity.
          replace (LocationType_Heap =? LocationType_Global) with false by reflexivity.
          replace (LocationType_Global =? LocationType_Global) with true by reflexivity.
          simpl.
          destruct ( (mtable_values is_init_cell i =? 0) && (min_eid <=? mtable_values start_eid_cell i) &&
                       (mtable_values start_eid_cell i <? max_eid)); simpl; lia.
       *  rewrite Htype.
          replace (LocationType_Stack =? LocationType_Heap) with false by reflexivity.
          replace (LocationType_Heap =? LocationType_Heap) with true by reflexivity.
          replace (LocationType_Global =? LocationType_Heap) with false by reflexivity.
          simpl.
          destruct ( (mtable_values is_init_cell i =? 0) && (min_eid <=? mtable_values start_eid_cell i) &&
                       (mtable_values start_eid_cell i <? max_eid)); simpl; lia.
       * rewrite Htype.
         replace (LocationType_Stack =? LocationType_Stack) with true by reflexivity.
         replace (LocationType_Heap =? LocationType_Stack) with false by reflexivity.
         replace (LocationType_Global =? LocationType_Stack) with false by reflexivity.
          simpl.
          destruct ( (mtable_values is_init_cell i =? 0) && (min_eid <=? mtable_values start_eid_cell i) &&
                       (mtable_values start_eid_cell i <? max_eid)); simpl; lia.
      + replace (mtable_values is_init_cell i =? 0) with false
          by (symmetry; rewrite Z.eqb_neq; lia).
        rewrite !andb_false_r, !andb_false_l.
        assert ( mtable_values rest_mops_cell i =  mtable_values rest_mops_cell (i+1)).
        {
          pose (Hmc10b := gate_mc10b i Hrange).
          destruct Hmc10b as [Hmc10b _].
          replace (i + 0) with i in * by lia.
          simpl in Hmc10b.
          rewrite Hinit in Hmc10b.
          lia.
        }
        specialize (IHn (i+1) ltac:(lia)).
        lia.
  Qed.

  Lemma rest_mops_bound : forall min_eid max_eid i j,
      0 <= i <= j ->      
        gather_mops min_eid max_eid LocationType_Stack i j
      + gather_mops min_eid max_eid LocationType_Heap i j
      + gather_mops min_eid max_eid LocationType_Global i j
      <= mtable_values rest_mops_cell i.
  Proof.
    unfold gather_mops.
    intros.
    apply rest_mops_bound' ; eauto; lia.
  Qed.  

  (* Number of memory operations that happen at a particular eid. *)
  Definition mops_at eid type := 
    gather_mops eid (eid+1) type 0 mtable_numRow.

  (* Number of memory operations that happen in a particular range of eids. *)
  Definition cum_mops from to :=
        gather_mops from to LocationType_Stack  0 mtable_numRow
      + gather_mops from to LocationType_Heap   0 mtable_numRow
      + gather_mops from to LocationType_Global 0 mtable_numRow.

  
  (* This lemma shows cum_mops is correctly defined. *)
  Theorem cum_mops_cons : forall eid to,
      0 <= eid < to ->
      cum_mops eid to =
        cum_mops (eid + 1) to
         + mops_at eid LocationType_Stack
         + mops_at eid LocationType_Heap
         + mops_at eid LocationType_Global.
  Proof.
    intros.
    unfold cum_mops, mops_at.
    rewrite !(mops_split_range eid (eid+1) to _ _); lia.
  Qed.
  
  (* This theorem proves that the rest_mops column is correct. *)
  Theorem rest_mops_correct : forall from to,
      cum_mops from to <= mtable_values rest_mops_cell 0.
  Proof.
    intros.
    unfold cum_mops.
    apply rest_mops_bound.
    pose mtable_numRow_nonneg; lia.
  Qed.

  Theorem cum_mops_nonnegative  : forall from to,
      0 <= cum_mops from to.
  Proof.
    intros.
    unfold cum_mops.
    pose (gather_mops_nonnegative from to LocationType_Stack 0 mtable_numRow).
    pose (gather_mops_nonnegative from to LocationType_Heap 0 mtable_numRow).
    pose (gather_mops_nonnegative from to LocationType_Global 0 mtable_numRow).
    lia.
  Qed.
  
  Theorem mops_at_nonnegative : forall eid typ,
    0 <= mops_at eid typ.
  Proof.
    intros. unfold mops_at.
    apply gather_mops_nonnegative.
  Qed.

  Lemma gather_mops'_empty_range : forall i typ n from,
      gather_mops' i i typ from n = 0.
  Proof.
    induction n; intros; simpl.
    - reflexivity.
    - destruct (mtable_values enabled_cell from =? 1); [|reflexivity].
      rewrite IHn. clear IHn.
      destruct (typ =? entry_type from); [|simpl; lia].
      destruct (mtable_values is_init_cell from =? 0); [|simpl; lia].
      destruct (i <=? mtable_values start_eid_cell from) eqn:e1; [|simpl;lia].
      destruct (mtable_values start_eid_cell from <? i) eqn:e2; [|simpl;lia].
      rewrite Z.leb_le in e1.
      rewrite Z.ltb_lt in e2.
      lia.
  Qed.
      
  Theorem cum_mops_empty_range : forall i,
      cum_mops i i = 0.
  Proof.
    intros i.
    unfold cum_mops, gather_mops.
    rewrite !gather_mops'_empty_range.
    lia.
  Qed.
  
End gather_mops.

(* There are three different types of semantic values: globals, memories, and stacks. 
   For each of them, we can update and query the value at a particular offset. 
*)

  Require Import Shared.

  Section gather.
  Variable eid_cutoff :Z.
  Variable type : Z.
  
  Fixpoint gather_entries' (i : Z) (n:nat) (s : map) :=
    match n with
    | O => s
    | S n' =>
        if (mtable_values enabled_cell i =? 1) 
        then         
          let s' := 
            if
              (type =? (entry_type i))
              && ((mtable_values start_eid_cell i) <? eid_cutoff)
             then Shared.set s (mtable_values offset_cell i) (mtable_values value_u64_cell i)
             else s in
          gather_entries' (i+1) n' s'
        else
          s
    end.

  Definition gather_entries (from to : Z) (init : map) :=
    gather_entries' from (Z.to_nat (to - from)) init.

  Lemma gather_entries_nonenabled : forall n i j s,
      mtable_values enabled_cell i = 0 ->
      0 <= i <= j ->
       gather_entries' j n s = s.
  Proof.
    induction n.
    - intros; simpl; auto.
    - intros i j s Henabled Hj.
      simpl.
      rewrite (enabled_seq_mono i ltac:(lia) Henabled j ltac:(lia)).
      reflexivity.
  Qed.
      
  Lemma gather_entries_append' : forall n m i s,
      0 <= i ->
      gather_entries' i (n+m) s = gather_entries' (i+ Z.of_nat n) m (gather_entries' i n s).
  Proof.
    induction n.
    - intros.
      simpl.
      replace (i+0) with i by lia.
      auto.
    - rewrite Nat2Z.inj_succ.
      intros.
      simpl.
      destruct (enabled_bit i) as [Henabled|Henabled].
      + rewrite Henabled.
        simpl.
        rewrite gather_entries_nonenabled with (i:=i); auto.
        lia.
      + rewrite Henabled.
        simpl.
        rewrite IHn by lia.
        f_equal.
        lia.
  Qed.
      
  Lemma gather_entries_append : forall i j k s,
      0 <= i ->
      i <= j <= k ->
      gather_entries i k s = gather_entries j k (gather_entries i j s).
  Proof.
    intros.
    unfold gather_entries.    
    replace (k - i) with ((j - i) + (k - j)) by lia.
    rewrite Z2Nat.inj_add by lia.
    rewrite gather_entries_append' by lia.
    rewrite Z2Nat.id by lia.
    replace (i + (j - i)) with j by lia.
    auto.
  Qed.

  Lemma gather_entries_cons_helper : forall i j s,
      0 <= i ->
      i <= j ->
      gather_entries i (j+1) s = gather_entries j (j+1) (gather_entries i j s).
  Proof.
    intros i j s Hrange Hj.
    rewrite (gather_entries_append i j (j+1));
      auto.
      lia.
  Qed.

  Lemma gather_entries_cons : forall i j s,
      0 <= i ->
      i <= j ->
      mtable_values enabled_cell j = 1 ->
      gather_entries i (j+1) s =
        if 
          (type =? (entry_type j))
          && ((mtable_values start_eid_cell j) <? eid_cutoff)
             then set (gather_entries i j s) (mtable_values offset_cell j) (mtable_values value_u64_cell j)
             else (gather_entries i j s).
  Proof.
    intros  i j s Hrange Hj Henabled.
    rewrite gather_entries_cons_helper; auto.
    remember (gather_entries i j s) as s'.
    clear Heqs'.
    unfold gather_entries.
    replace (j + 1 - j) with 1 by lia.
    simpl.
    rewrite Henabled; simpl.
    reflexivity.
  Qed.  

  Section gather_later_entries_get.
  (* We are interested in looking up a particular row i0, that was inserted a the current
     instruction. *)
  Variable i0 : Z.
  Variable i0_eid: mtable_values start_eid_cell i0 < eid_cutoff <= mtable_values end_eid_cell i0.
  Variable i0_type : (entry_type i0) = type. 
  
  Lemma gather_later_entries_get' : forall n i s,
      0 <= i ->
      entry_lt i0 i ->
      get (gather_entries' i n s) (mtable_values offset_cell i0)
      = get s (mtable_values offset_cell i0).
  Proof.
    induction n.
    - intros. simpl. reflexivity.
    - intros. simpl.
      destruct (enabled_bit i) as [Henabled | Henabled].
      + rewrite Henabled. simpl.
        reflexivity.
      + rewrite Henabled.
        simpl.
        rewrite IHn. simpl.
        { clear IHn.
          destruct H0 as [Hlt | [Hlt | [Hlt | Hlt]]].
          - destruct (enabled_bit i0); lia.
          - rewrite (proj2 (Z.eqb_neq type (entry_type i))) by lia.
            reflexivity.
          - destruct ((type =? entry_type i) && (mtable_values start_eid_cell i <? eid_cutoff)).
            + rewrite gso; auto.
              lia.
            + auto.
          - rewrite (Zaux.Zlt_bool_false) by lia.
            rewrite andb_false_r.
            reflexivity.
        }
        { lia. }        
        { apply entry_lt_trans with i; auto using mtable_sorted. }
  Qed.
           
  Lemma gather_later_entries_get : forall i j s,
      0 <= i ->
      entry_lt i0 i ->
      get (gather_entries i j s) (mtable_values offset_cell i0)
      = get s (mtable_values offset_cell i0).
  Proof.  
    unfold gather_entries.
    intros.
    rewrite gather_later_entries_get'; auto.
  Qed.

  End gather_later_entries_get.


  Section gather_later_entries_set.
  Variable i0 : Z.
  Variable i0_eid: mtable_values start_eid_cell i0 = eid_cutoff.
  Variable i0_type : (entry_type i0) = type. 
  
  Lemma gather_later_entries_set' : forall n i  v s,
      0 <= i ->
      entry_lt i0 i ->
      set (gather_entries' i n s) (mtable_values offset_cell i0) v
      = gather_entries' i n (set s (mtable_values offset_cell i0) v).
  Proof.
    induction n.
    - intros. simpl. reflexivity.
    - intros. simpl.
      destruct (enabled_bit i) as [Henabled | Henabled].
      + rewrite Henabled. simpl.
        reflexivity.
      + rewrite Henabled.
        simpl.
        rewrite IHn. simpl.
        { clear IHn.
          destruct H0 as [Hlt | [Hlt | [Hlt | Hlt]]].
          - destruct (enabled_bit i0); lia.
          - rewrite (proj2 (Z.eqb_neq type (entry_type i))) by lia.
            reflexivity.
          - destruct ((type =? entry_type i) && (mtable_values start_eid_cell i <? eid_cutoff)).
            + rewrite sso; auto.
              lia.
            + reflexivity.
          - rewrite (Zaux.Zlt_bool_false) by lia.
            rewrite andb_false_r.
            reflexivity.
        }
        { lia. }        
        { apply entry_lt_trans with i; auto using mtable_sorted. }
  Qed.
           
  Lemma gather_later_entries_set : forall i j s v,
      0 <= i ->
      entry_lt i0 i ->
      set (gather_entries i j s) (mtable_values offset_cell i0) v
      = gather_entries i j (set s (mtable_values offset_cell i0) v).
  Proof.  
    unfold gather_entries.
    intros.
    rewrite gather_later_entries_set'; auto.
  Qed.
  
  End gather_later_entries_set.

  End gather.

  (* This is the theorem that shows reads are correct. *)
  Theorem mtable_read : forall eid type offset is_i32 value init,
    memory_table_lookup_read_cell eid type offset is_i32 value ->
    get (gather_entries eid type 0 mtable_numRow init) offset = Some value.
  Proof.
    intros eid type offset is_i32 value init Hlookup.
    apply memory_table_lookup_read in Hlookup.
    destruct Hlookup as [i [Hrange [Henabled [Het [Hvalue [Hoffset [Htype Hi32]]]]]]].
    
    rewrite (gather_entries_append _ _  0 (i+1) mtable_numRow).
    2: { lia. }
    2: { apply enabled_lt_numRow  in Henabled; auto.
         lia. }
    rewrite <- Hoffset.
    rewrite gather_later_entries_get.
    - rewrite gather_entries_cons; auto; try lia.
      rewrite Htype, Z.eqb_refl.
      simpl.
      rewrite Zaux.Zlt_bool_true by lia.
      rewrite gss.
      f_equal.
      apply Hvalue.
    - auto.
    - auto.
    - lia.
    - apply mtable_sorted; auto.
  Qed.

  Lemma no_mops_no_ops' :   forall n (eid type i : Z) (init : map),
      0 <= i ->
      eid > 0 ->
      gather_mops' eid (eid + 1) type i n = 0 ->
        gather_entries' (eid+1) type i n init 
      = gather_entries' eid type i n init.
  Proof.
    induction n; intros eid type i init Hrange Heid.
    - simpl. auto.
    - simpl.
      destruct (mtable_values enabled_cell i =? 1) eqn:Henabled; [|auto].
      destruct (type =? entry_type i); simpl.
      2: { rewrite Z.add_0_l.
           assert (0 <= i+1) by lia; eauto. }
      intros H.
      assert ( (mtable_values is_init_cell i =? 0) && (eid <=? mtable_values start_eid_cell i) &&
                 (mtable_values start_eid_cell i <? eid + 1) = false
               /\  gather_mops' eid (eid + 1) type (i + 1) n = 0).
      { pose (gather_mops_nonnegative' eid (eid + 1) type  n (i + 1)).
        destruct ((mtable_values is_init_cell i =? 0) && (eid <=? mtable_values start_eid_cell i) &&
                    (mtable_values start_eid_cell i <? eid + 1)); simpl in *; try lia.
      }
      clear H.
      destruct H0 as [H1 H2].

      destruct (Z_le_dec (mtable_values start_eid_cell i) 0) as [Hl | Hl].
      + replace ( mtable_values start_eid_cell i <? eid + 1) with true. 
        2: { symmetry. apply Z.ltb_lt. lia. }
        replace ( mtable_values start_eid_cell i <? eid) with true. 
        2: { symmetry. apply Z.ltb_lt. lia. }
        apply IHn; try lia.
      + replace (mtable_values is_init_cell i =? 0) with true in H1.
        2: {
          symmetry.
          rewrite nonzero_eid_not_init; simpl; auto; lia.
        }
        simpl in H1.
        rewrite andb_false_iff, Z.leb_nle, Z.ltb_nlt in H1.
        assert ( mtable_values start_eid_cell i <> eid) by lia.
        destruct (Z_lt_dec (mtable_values start_eid_cell i) eid) as [Hll | Hll].
        * rewrite (Zaux.Zlt_bool_true _ eid) by lia.
          rewrite (Zaux.Zlt_bool_true _ (eid+1)) by lia.
          apply IHn; try lia.
        * rewrite (Zaux.Zlt_bool_false _ eid) by lia.
          rewrite (Zaux.Zlt_bool_false _ (eid+1)) by lia.
          apply IHn; try lia.
  Qed.

  Lemma no_mops_no_ops : forall eid type i j init,
      0 <= i ->
      eid > 0 ->      
      gather_mops eid (eid+1) type i j = 0 ->
      gather_entries (eid+1) type i j init = gather_entries eid type i j init.
  Proof.
    unfold gather_mops, gather_entries.
    intros.
    apply no_mops_no_ops'; auto.
  Qed.

  (* This is needed for all instructions that do not do writes. *)
  Theorem mtable_no_write : forall eid type init,
      eid > 0 ->
      mops_at eid type = 0 ->
      gather_entries (eid+1) type 0 mtable_numRow init = gather_entries eid type 0 mtable_numRow init.
  Proof.
    unfold gather_mops, gather_entries.
    intros.
    apply no_mops_no_ops'; auto; lia.
  Qed.

  (* This is the theorem that shows every write is counted. *)
  Theorem mtable_write_mops : forall eid type offset is_i32 value,
    eid > 0 ->
    memory_table_lookup_write_cell eid type offset is_i32 value ->
    mops_at eid type >= 1.
  Proof.
    unfold mops_at.
    intros eid type offset is_i32 value Heid Hlookup.
    apply memory_table_lookup_write in Hlookup.
    destruct Hlookup as [i [Hrange [Henabled [Het [Hvalue [Hoffset [Htype Hi32]]]]]]].    
    rewrite (gather_mops_append _ _ type 0 (i+1) mtable_numRow).
    2: { lia.  }
    2: { apply enabled_lt_numRow  in Henabled; auto. lia. }
    
    rewrite (gather_mops_append _ _ type 0 i (i+1)).
    2: { lia.  }
    2: { apply enabled_lt_numRow  in Henabled; auto. lia. }
    
    cut ( gather_mops eid (eid + 1) type i (i + 1) >= 1).
    {
      pose (gather_mops_nonnegative eid (eid + 1) type 0 i).
      pose (gather_mops_nonnegative  eid (eid + 1) type (i + 1) mtable_numRow).
      lia.
    }

    unfold gather_mops.
    replace (Z.to_nat (i + 1 - i)) with 1%nat by lia.
    simpl.
    rewrite Henabled.  rewrite Z.eqb_refl.
    rewrite Htype.   rewrite Z.eqb_refl.
    rewrite nonzero_eid_not_init by lia. rewrite Z.eqb_refl.
    rewrite Het. rewrite Z.leb_refl.
    rewrite Zaux.Zlt_bool_true by lia.
    simpl.
    lia.
  Qed.

  Theorem mtable_write_mops2 : forall eid type offset1 is_i32_1 value1 offset2 is_i32_2 value2,
    eid > 0 ->
    memory_table_lookup_write_cell eid type offset1 is_i32_1 value1 ->
    memory_table_lookup_write_cell eid type offset2 is_i32_2 value2 ->
    offset1 <> offset2 ->
    mops_at eid type >= 2.
  Proof.
    unfold mops_at.
    intros eid type offset1 is_i32_1 value1 offset2 is_i32_2 value2 Heid Hlookup1 Hlookup2 Hoffset_diff.
    apply memory_table_lookup_write in Hlookup1.
    apply memory_table_lookup_write in Hlookup2.
    destruct Hlookup1 as [i [Hrange [Henabled [Het [Hvalue [Hoffset [Htype Hi32]]]]]]].    
    destruct Hlookup2 as [i2 [Hrange2 [Henabled2 [Het2 [Hvalue2 [Hoffset2 [Htype2 Hi32_2]]]]]]].
    
    assert(H: i < i2 \/ i2 < i \/ i = i2) by lia.
    destruct H as [H1 | [H2 | Hc]].
    
    - rewrite (gather_mops_append _ _ type 0 (i + 1) mtable_numRow).
      2: { lia.  }
      2: { apply enabled_lt_numRow  in Henabled; auto; lia. }
      
      rewrite (gather_mops_append _ _ type 0 i (i + 1)); try lia.
      rewrite (gather_mops_append _ _ type (i+1) (i2+1) mtable_numRow); try lia.
      2: { apply enabled_lt_numRow in Henabled2; auto; lia. }
      rewrite (gather_mops_append _ _ type (i+1) i2 (i2 + 1)); try lia.

      cut ( gather_mops eid (eid + 1) type i (i + 1) >= 1 /\  gather_mops eid (eid + 1) type i2 (i2 + 1) >= 1).
      {
        pose (gather_mops_nonnegative eid (eid + 1) type 0 i).
        pose (gather_mops_nonnegative  eid (eid + 1) type (i + 1) i2).
        pose (gather_mops_nonnegative  eid (eid + 1) type (i2 + 1) mtable_numRow).
        lia.
      }

      unfold gather_mops.
      replace (Z.to_nat (i + 1 - i)) with 1%nat by lia.
      replace (Z.to_nat (i2 + 1 - i2)) with 1%nat by lia.
      simpl.
      rewrite Henabled, Henabled2.  rewrite Z.eqb_refl.
      rewrite Htype, Htype2.   rewrite Z.eqb_refl.
      repeat rewrite nonzero_eid_not_init by lia. rewrite Z.eqb_refl.
      rewrite Het, Het2. rewrite Z.leb_refl.
      rewrite Zaux.Zlt_bool_true by lia.
      simpl.
      lia.

      - rewrite (gather_mops_append _ _ type 0 (i2 + 1) mtable_numRow).
      2: { lia.  }
      2: { apply enabled_lt_numRow  in Henabled2; auto; lia. }
      
      rewrite (gather_mops_append _ _ type 0 i2 (i2 + 1)); try lia.
      rewrite (gather_mops_append _ _ type (i2+1) (i+1) mtable_numRow); try lia.
      2: { apply enabled_lt_numRow in Henabled; auto; lia. }
      rewrite (gather_mops_append _ _ type (i2+1) i (i + 1)); try lia.

      cut ( gather_mops eid (eid + 1) type i2 (i2 + 1) >= 1 /\  gather_mops eid (eid + 1) type i (i + 1) >= 1).
      {
        pose (gather_mops_nonnegative eid (eid + 1) type 0 i2).
        pose (gather_mops_nonnegative  eid (eid + 1) type (i2 + 1) i).
        pose (gather_mops_nonnegative  eid (eid + 1) type (i + 1) mtable_numRow).
        lia.
      }

      unfold gather_mops.
      replace (Z.to_nat (i + 1 - i)) with 1%nat by lia.
      replace (Z.to_nat (i2 + 1 - i2)) with 1%nat by lia.
      simpl.
      rewrite Henabled, Henabled2.  rewrite Z.eqb_refl.
      rewrite Htype, Htype2.   rewrite Z.eqb_refl.
      repeat rewrite nonzero_eid_not_init by lia. rewrite Z.eqb_refl.
      rewrite Het, Het2. rewrite Z.leb_refl.
      rewrite Zaux.Zlt_bool_true by lia.
      simpl.
      lia.

    - rewrite Hc in Hoffset. 
      lia.
  Qed.
  
(* This is the theorem that shows writes are correct. *)
  Theorem mtable_write : forall eid type offset is_i32 value init,
    eid > 0 ->
    memory_table_lookup_write_cell eid type offset is_i32 value ->
    mops_at eid type = 1 ->      
    (gather_entries (eid+1) type 0 mtable_numRow init)
    = set (gather_entries eid type 0 mtable_numRow init) offset value.
  Proof.
    intros eid type offset is_i32 value init Heid Hlookup Hops.
    apply memory_table_lookup_write in Hlookup.
    destruct Hlookup as [i [Hrange [Henabled [Het [Hvalue [Hoffset [Htype Hi32]]]]]]].

    rewrite (gather_entries_append (eid+1) _  0 (i+1) mtable_numRow).
    2: { lia. }
    2: { apply enabled_lt_numRow  in Henabled; auto.
         lia. }

    rewrite (gather_entries_append (eid) _  0 (i+1) mtable_numRow).
    2: { lia. }
    2: { apply enabled_lt_numRow  in Henabled; auto.
         lia. }    

    unfold mops_at in Hops.
    rewrite (gather_mops_append _ _ type 0 (i+1) mtable_numRow) in Hops.
    2: { lia.  }
    2: { apply enabled_lt_numRow  in Henabled; auto. lia. }
    
    rewrite (gather_mops_append _ _ type 0 i (i+1)) in Hops.
    2: { lia.  }
    2: { apply enabled_lt_numRow  in Henabled; auto. lia. }
    
    replace  (gather_mops eid (eid + 1) type i (i + 1)) with 1 in Hops.
    2: {
      unfold gather_mops.
      replace (Z.to_nat (i + 1 - i)) with 1%nat by lia.
      simpl.
      rewrite Henabled.  rewrite Z.eqb_refl.
      rewrite Htype.   rewrite Z.eqb_refl.
      rewrite nonzero_eid_not_init by lia. rewrite Z.eqb_refl.
      rewrite Het. rewrite Z.leb_refl.
      rewrite Zaux.Zlt_bool_true by lia.
      simpl.
      lia.
    }
    assert (Hmops_before : gather_mops eid (eid + 1) type 0 i = 0).
    {
      pose (gather_mops_nonnegative eid (eid + 1) type 0 i).
      pose (gather_mops_nonnegative  eid (eid + 1) type (i + 1) mtable_numRow).
      lia.
    }
    assert (Hmops_after : gather_mops eid (eid + 1) type (i + 1) mtable_numRow = 0).
    {
      pose (gather_mops_nonnegative eid (eid + 1) type 0 i).
      pose (gather_mops_nonnegative  eid (eid + 1) type (i + 1) mtable_numRow).
      lia.
    }

    rewrite (no_mops_no_ops eid type (i+1) mtable_numRow) by (auto; lia).

    rewrite <- Hoffset.
    rewrite (gather_later_entries_set).
    2,3,4: auto; lia.
    2: { apply mtable_sorted; auto. }

    f_equal.

    rewrite gather_entries_cons by (auto; lia).
    rewrite Htype, Z.eqb_refl.
    rewrite Het. rewrite Zaux.Zlt_bool_true by lia.
    simpl.
    rewrite (no_mops_no_ops eid type 0 i) by (auto; lia).
    rewrite Hvalue.

    rewrite gather_entries_cons by (auto; lia).
    rewrite Htype, Z.eqb_refl.
    rewrite Het. rewrite Z.ltb_irrefl.
    simpl.
    
    reflexivity.
  Qed.  
    
  (* Similar to previous, but with two writes. *)
  Theorem mtable_write_two : forall eid type offset1 offset2 is_i32_1 is_i32_2 value1 value2 init,
      eid > 0 ->
      offset1 < offset2 ->
    memory_table_lookup_write_cell eid type offset1 is_i32_1 value1 ->
    memory_table_lookup_write_cell eid type offset2 is_i32_2 value2 ->
    mops_at eid type = 2 ->      
    (gather_entries (eid+1) type 0 mtable_numRow init)
    = set (set (gather_entries eid type 0 mtable_numRow init) offset1 value1) offset2 value2.
  Proof.
    intros eid type offset1 offset2 is_i32_1 is_i32_2 value1 value2 init Heid Hlt Hlookup1 Hlookup2 Hops.
    apply memory_table_lookup_write in Hlookup1.
    apply memory_table_lookup_write in Hlookup2.
    destruct Hlookup1 as [i [Hrange1 [Henabled1 [Het1 [Hvalue1 [Hoffset1 [Htype1 Hi321]]]]]]].
    destruct Hlookup2 as [j [Hrange2 [Henabled2 [Het2 [Hvalue2 [Hoffset2 [Htype2 Hi322]]]]]]].
    assert (i < j).
    {
      apply mtable_sorted_by_offset; auto; lia.
    }
    
    rewrite (gather_entries_append (eid+1) _  0 (i+1) mtable_numRow).
    2: { lia. }
    2: { apply enabled_lt_numRow  in Henabled1; auto.
         lia. }

    rewrite (gather_entries_append (eid) _  0 (i+1) mtable_numRow).
    2: { lia. }
    2: { apply enabled_lt_numRow  in Henabled1; auto.
         lia. }

    unfold mops_at in Hops.
    rewrite (gather_mops_append _ _ type 0 (i+1) mtable_numRow) in Hops.
    2: { lia.  }
    2: { apply enabled_lt_numRow  in Henabled1; auto. lia. }
    
    rewrite (gather_mops_append _ _ type 0 i (i+1)) in Hops.
    2: { lia.  }
    2: { apply enabled_lt_numRow  in Henabled1; auto. lia. }
    
    replace  (gather_mops eid (eid + 1) type i (i + 1)) with 1 in Hops.
    2: {
      unfold gather_mops.
      replace (Z.to_nat (i + 1 - i)) with 1%nat by lia.
      simpl.
      rewrite Henabled1.  rewrite Z.eqb_refl.
      rewrite Htype1.   rewrite Z.eqb_refl.
      rewrite nonzero_eid_not_init by lia. rewrite Z.eqb_refl.
      rewrite Het1. rewrite Z.leb_refl.
      rewrite Zaux.Zlt_bool_true by lia.
      simpl.
      lia.
    }


    rewrite (gather_entries_append (eid+1) _  (i+1) (j+1) mtable_numRow).
    2: { lia. }
    2: { apply enabled_lt_numRow  in Henabled2; auto.
         lia. }

    rewrite (gather_entries_append (eid) _  (i+1) (j+1) mtable_numRow).
    2: { lia. }
    2: { apply enabled_lt_numRow  in Henabled2; auto.
         lia. }

    rewrite (gather_mops_append _ _ type (i+1) (j+1) mtable_numRow) in Hops.
    2: { lia.  }
    2: { apply enabled_lt_numRow  in Henabled2; auto. lia. }
    
    rewrite (gather_mops_append _ _ type (i+1) j (j+1)) in Hops.
    2: { lia.  }
    2: { apply enabled_lt_numRow  in Henabled2; auto. lia. }
    
    replace  (gather_mops eid (eid + 1) type j (j + 1)) with 1 in Hops.
    2: {
      unfold gather_mops.
      replace (Z.to_nat (j + 1 - j)) with 1%nat by lia.
      simpl.
      rewrite Henabled2.  rewrite Z.eqb_refl.
      rewrite Htype2.   rewrite Z.eqb_refl.
      rewrite nonzero_eid_not_init by lia. rewrite Z.eqb_refl.
      rewrite Het2. rewrite Z.leb_refl.
      rewrite Zaux.Zlt_bool_true by lia.
      simpl.
      lia.
    }
    
    assert (Hmops_before : gather_mops eid (eid + 1) type 0 i = 0).
    {
      pose (gather_mops_nonnegative eid (eid + 1) type 0 i).
      pose (gather_mops_nonnegative  eid (eid + 1) type (i + 1) j).
      pose (gather_mops_nonnegative  eid (eid + 1) type (j + 1) mtable_numRow).
      lia.
    }
    assert (Hmops_middle : (gather_mops eid (eid + 1) type (i + 1) j = 0)).
    {
      pose (gather_mops_nonnegative eid (eid + 1) type 0 i).
      pose (gather_mops_nonnegative  eid (eid + 1) type (i + 1) j).
      pose (gather_mops_nonnegative  eid (eid + 1) type (j + 1) mtable_numRow).
      lia.
    }
    assert (Hmops_after : gather_mops eid (eid + 1) type (j + 1) mtable_numRow = 0).
    {
      pose (gather_mops_nonnegative eid (eid + 1) type 0 i).
      pose (gather_mops_nonnegative  eid (eid + 1) type (i + 1) j).
      pose (gather_mops_nonnegative  eid (eid + 1) type (j + 1) mtable_numRow).
      lia.
    }

    rewrite (no_mops_no_ops eid type (j+1) mtable_numRow) by (auto; lia).

    rewrite <- Hoffset1.
    rewrite (gather_later_entries_set).
    2,3,4: auto; lia.
    2: {
      apply mtable_sorted_further; auto; lia.
    }

    rewrite <- Hoffset2.
    rewrite (gather_later_entries_set).
    2,3,4: auto; lia.
    2: {
      apply mtable_sorted; auto.
    }

    f_equal.

    rewrite gather_entries_cons by (auto; lia).
    rewrite Htype2, Z.eqb_refl.
    rewrite Het2. rewrite Zaux.Zlt_bool_true by lia.
    simpl.
    rewrite Hvalue2.

    rewrite gather_entries_cons by (auto; lia).
    rewrite Htype1, Z.eqb_refl.
    rewrite Het1. rewrite Zaux.Zlt_bool_true by lia.
    simpl.
    rewrite Hvalue1.    

    rewrite (no_mops_no_ops eid type 0 i) by (auto; lia).
    rewrite (no_mops_no_ops eid type (i+1) j) by (auto; lia).
    
    rewrite gather_entries_cons by (auto; lia).
    rewrite Htype2, Z.eqb_refl.
    rewrite Het2. rewrite Z.ltb_irrefl.
    simpl.

    rewrite gather_entries_cons by (auto; lia).
    rewrite Htype1, Z.eqb_refl.
    rewrite Het1. rewrite Z.ltb_irrefl.
    simpl.

    rewrite <- gather_later_entries_set.
    2,3,4: auto; lia.
    2: {
      apply mtable_sorted; auto.
    }
    
    reflexivity.
  Qed.
  
  Definition initial_value typ k v :=
           exists j mut k1 k2,
             k1 <= k <= k2 /\
             image_table_values col j = encode_init_memory_table_entry typ mut k1 k2 v.

  Definition initial_map typ s := forall k v, get s k = Some v -> initial_value typ k v.

  Lemma initial_map_empty : forall typ,  initial_map typ empty.
  Proof.
    intros typ k v Hget.
    rewrite gempty in Hget.
    congruence.
  Qed.

  Lemma initial_map_update : forall typ s k v,
      initial_map typ s ->
      initial_value typ k v ->
      initial_map typ (set s k v).
  Proof.
    intros.
    unfold initial_map.
    intros k0 v0.
    destruct (Z.eq_dec k k0) as [e|e].
    - subst.
      rewrite gss.
      injection 1; intros; subst.
      auto.
    - rewrite gso by auto.
      intros Hget.
      apply H.
      auto.
  Qed.

  Lemma no_mops_init : forall eid typ n i s,
      0 <= i ->
      gather_mops' 0 eid typ i n = 0 ->
      initial_map typ s ->
      initial_map typ (gather_entries' eid typ i n s).
  Proof.
    induction n; intros i s Hrange Hops Hs.
    - simpl in *. auto.
    - simpl in *.
      destruct (mtable_values enabled_cell i =? 1) eqn:Henabled.
      2: { auto. }

      destruct (Z.eq_dec typ (entry_type i)) as [Htyp | Htyp].
      2: { rewrite <- Z.eqb_neq in Htyp. rewrite Htyp in *.
            assert (0 <= i+1) by lia; eauto. }

      replace (typ =? entry_type i) with true in * by (rewrite <- Z.eqb_eq in Htyp; congruence).
      simpl in *.

      assert ( (mtable_values is_init_cell i =? 0) && (0 <=? mtable_values start_eid_cell i) &&
                 (mtable_values start_eid_cell i <? eid) = false
               /\  gather_mops' 0 eid typ (i + 1) n = 0).
      { pose (gather_mops_nonnegative' 0 eid typ  n (i + 1)).
        destruct ((mtable_values is_init_cell i =? 0) && (0 <=? mtable_values start_eid_cell i) &&
                    (mtable_values start_eid_cell i <? eid)); simpl in *; try lia.
      }
      destruct H as [H1 H2].
      clear Hops.

      rewrite <- andb_assoc in H1.
      rewrite andb_false_iff in H1.
      destruct H1.
      + destruct (is_init_bit i) as [Hinit | Hinit]; [rewrite Hinit in H; simpl in H; congruence |].
        clear H.
        apply IHn.
        * lia.
        * auto.
          destruct ( mtable_values start_eid_cell i <? eid).
          ** apply initial_map_update; auto.
             rewrite Htyp.
             rewrite Z.eqb_eq in Henabled.
             eapply init_lookup_encoded; auto.
          ** auto.
       + apply IHn.
         lia.
         auto.
         replace (0 <=? mtable_values start_eid_cell i) with true in H.
         2: { pose (start_eid_common i).
              symmetry. rewrite Z.leb_le. lia. }
         simpl in H. rewrite H.
         assumption.
  Qed.

  (* This theorem justifies the initial value at the beginning of program execution. *)
  Theorem initial_state: forall eid typ,
      gather_mops 0 eid typ 0 mtable_numRow = 0 ->
      forall k v,
        get (gather_entries eid typ 0 mtable_numRow empty) k = Some v ->
        initial_value typ k v.
  Proof.
    intros eid typ Hmops k v Hget.
    unfold gather_mops in Hmops.
    refine (no_mops_init eid typ _ _ empty _ Hmops _ k v Hget).
    - lia.
    - apply initial_map_empty.
  Qed.

  (* List all the addresses with writes. This is used to define the globals relation. *)
  Section domain.

   Variable (type : Z).

  Fixpoint gather_offsets' (i : Z) (n:nat) :=
    match n with
    | O => 0
    | S n' =>
        if (   (mtable_values enabled_cell i =? 1)
            && (type =? (entry_type i)))
        then
          (Z.max (mtable_values offset_cell i)
                 (gather_offsets' (i+1) n'))
        else
          gather_offsets' (i+1) n'
    end.

  Lemma gather_offsets'_correct : forall (n k : nat) i,
      (k < n) % nat->
      mtable_values enabled_cell (i + Z.of_nat k) = 1 ->
      entry_type (i + Z.of_nat k) = type ->
      mtable_values offset_cell (i + Z.of_nat k) <= gather_offsets' i n.
  Proof.
    induction n.
    - intros. lia.
    - destruct k.
      + intros i Hlt Henabled Htype.
        replace (i + Z.of_nat 0) with i in * by lia.
        simpl.
        rewrite Henabled, Z.eqb_refl, Htype, Z.eqb_refl.
        simpl.
        lia.
      + intros i Hlt Henabled Htype.
        simpl.
        replace (i + Z.of_nat (S k)) with (i+1 + Z.of_nat k) in * by lia.
        replace (i + Z.pos (Pos.of_succ_nat k))  with (i+1 + Z.of_nat k) in * by lia.
        specialize (IHn k (i+1) ltac:(lia) Henabled Htype).
        destruct ((mtable_values enabled_cell i =? 1) && (type =? entry_type i)); lia.
  Qed.

  Definition gather_offsets (from to : Z) :=
    gather_offsets' from (Z.to_nat (to - from)).

  Definition domain := gather_offsets 0 mtable_numRow.

  Theorem domain_correct : forall eid offset is_i32 value,
      memory_table_lookup_write_cell eid type offset is_i32 value ->
      0 <= offset <= domain.
  Proof.
    destruct 1.
    destruct write_lookup0 as [i [Hrange [Hstart [_ [Hencode _]]]]].
    destruct (lookup_encode i offset type is_i32 Hrange write_offset_common0 write_location_type0 write_is_i32_bit0)
     as [Henabled [Hoffset [Htype _]]].
    { lia. }
    split; [lia|].
    unfold domain, gather_offsets.
    rewrite <- Hoffset.
    replace i with (0 + Z.of_nat (Z.to_nat i)) by lia.
    apply gather_offsets'_correct.
    - replace (mtable_numRow - 0) with mtable_numRow by lia.
      enough (i < mtable_numRow); [pose mtable_numRow_nonneg; lia|].
      apply enabled_lt_numRow; auto.
    - replace (0 + Z.of_nat (Z.to_nat i)) with i by lia; assumption.
    - replace (0 + Z.of_nat (Z.to_nat i)) with i by lia; assumption.
  Qed.  
  End domain.
