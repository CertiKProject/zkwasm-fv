(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import CommonModel.
Require Import ImageTableModel.
Require Import MTableModel.

Open Scope Z_scope.

Lemma enabled_seq_mono : forall i,
    0 <= i ->
    mtable_values enabled_cell i = 0 ->
    forall j, i <= j -> mtable_values enabled_cell j = 0.
Admitted. (* Proof omitted for release, present in original source. *)

Definition entry_type i : Z :=
       if Z.eqb (mtable_values is_stack_cell i) 1 then LocationType_Stack
  else if Z.eqb (mtable_values is_heap_cell  i) 1  then LocationType_Heap
  else LocationType_Global.

Lemma is_next_same_ltype : forall i,
    0 <= i ->
    mtable_values enabled_cell i = 1 ->
    mtable_values enabled_cell (i+1) = 1 ->
    (mtable_values is_next_same_ltype_cell i = 1 
     <-> entry_type i = entry_type (i+1)).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma is_next_same_offset : forall i,
  0 <= i ->
  mtable_values enabled_cell i = 1 ->
  mtable_values enabled_cell (i+1) = 1 ->
  entry_type i = entry_type (i+1) ->
  (mtable_values is_next_same_offset_cell i = 1 
   <->  mtable_values offset_cell i = mtable_values offset_cell (i+1)).
Admitted. (* Proof omitted for release, present in original source. *)

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

Theorem mtable_sorted : forall i,
    0 <= i ->
    mtable_values enabled_cell i = 1 ->
    entry_lt i (i+1).
Admitted. (* Proof omitted for release, present in original source. *)

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
Admitted. (* Proof omitted for release, present in original source. *)

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
Admitted. (* Proof omitted for release, present in original source. *)

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
Admitted. (* Proof omitted for release, present in original source. *)

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

  End gather.

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
Admitted. (* Proof omitted for release, present in original source. *)
  
  (* This theorem proves that the rest_mops column is correct. *)
  Theorem rest_mops_correct : forall from to,
      cum_mops from to <= mtable_values rest_mops_cell 0.
Admitted. (* Proof omitted for release, present in original source. *)

  Theorem cum_mops_nonnegative  : forall from to,
      0 <= cum_mops from to.
Admitted. (* Proof omitted for release, present in original source. *)
  
  Theorem mops_at_nonnegative : forall eid typ,
    0 <= mops_at eid typ.
Admitted. (* Proof omitted for release, present in original source. *)

  Theorem cum_mops_empty_range : forall i,
      cum_mops i i = 0.
Admitted. (* Proof omitted for release, present in original source. *)
  
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

  Section gather_later_entries_get.
  (* We are interested in looking up a particular row i0, that was inserted a the current
     instruction. *)
  Variable i0 : Z.
  Variable i0_eid: mtable_values start_eid_cell i0 < eid_cutoff <= mtable_values end_eid_cell i0.
  Variable i0_type : (entry_type i0) = type. 
  
  End gather_later_entries_get.

  Section gather_later_entries_set.
  Variable i0 : Z.
  Variable i0_eid: mtable_values start_eid_cell i0 = eid_cutoff.
  Variable i0_type : (entry_type i0) = type. 
  
  End gather_later_entries_set.

  End gather.

  (* This is the theorem that shows reads are correct. *)
  Theorem mtable_read : forall eid type offset is_i32 value init,
    memory_table_lookup_read_cell eid type offset is_i32 value ->
    get (gather_entries eid type 0 mtable_numRow init) offset = Some value.
Admitted. (* Proof omitted for release, present in original source. *)

  (* This is needed for all instructions that do not do writes. *)
  Theorem mtable_no_write : forall eid type init,
      eid > 0 ->
      mops_at eid type = 0 ->
      gather_entries (eid+1) type 0 mtable_numRow init = gather_entries eid type 0 mtable_numRow init.
Admitted. (* Proof omitted for release, present in original source. *)

  (* This is the theorem that shows every write is counted. *)
  Theorem mtable_write_mops : forall eid type offset is_i32 value,
    eid > 0 ->
    memory_table_lookup_write_cell eid type offset is_i32 value ->
    mops_at eid type >= 1.
Admitted. (* Proof omitted for release, present in original source. *)

  Theorem mtable_write_mops2 : forall eid type offset1 is_i32_1 value1 offset2 is_i32_2 value2,
    eid > 0 ->
    memory_table_lookup_write_cell eid type offset1 is_i32_1 value1 ->
    memory_table_lookup_write_cell eid type offset2 is_i32_2 value2 ->
    offset1 <> offset2 ->
    mops_at eid type >= 2.
Admitted. (* Proof omitted for release, present in original source. *)
  
(* This is the theorem that shows writes are correct. *)
  Theorem mtable_write : forall eid type offset is_i32 value init,
    eid > 0 ->
    memory_table_lookup_write_cell eid type offset is_i32 value ->
    mops_at eid type = 1 ->      
    (gather_entries (eid+1) type 0 mtable_numRow init)
    = set (gather_entries eid type 0 mtable_numRow init) offset value.
Admitted. (* Proof omitted for release, present in original source. *)
    
  (* Similar to previous, but with two writes. *)
  Theorem mtable_write_two : forall eid type offset1 offset2 is_i32_1 is_i32_2 value1 value2 init,
      eid > 0 ->
      offset1 < offset2 ->
    memory_table_lookup_write_cell eid type offset1 is_i32_1 value1 ->
    memory_table_lookup_write_cell eid type offset2 is_i32_2 value2 ->
    mops_at eid type = 2 ->      
    (gather_entries (eid+1) type 0 mtable_numRow init)
    = set (set (gather_entries eid type 0 mtable_numRow init) offset1 value1) offset2 value2.
Admitted. (* Proof omitted for release, present in original source. *)
  
  Definition initial_value typ k v :=
           exists j mut k1 k2,
             k1 <= k <= k2 /\
             image_table_values col j = encode_init_memory_table_entry typ mut k1 k2 v.


  (* This theorem justifies the initial value at the beginning of program execution. *)
  Theorem initial_state: forall eid typ,
      gather_mops 0 eid typ 0 mtable_numRow = 0 ->
      forall k v,
        get (gather_entries eid typ 0 mtable_numRow empty) k = Some v ->
        initial_value typ k v.
Admitted. (* Proof omitted for release, present in original source. *)

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

  Definition gather_offsets (from to : Z) :=
    gather_offsets' from (Z.to_nat (to - from)).

  Definition domain := gather_offsets 0 mtable_numRow.

  Theorem domain_correct : forall eid offset is_i32 value,
      memory_table_lookup_write_cell eid type offset is_i32 value ->
      0 <= offset <= domain.
Admitted. (* Proof omitted for release, present in original source. *)
  End domain.
