(* Copyright (C) CertiK 2024-2026 *)

Require Import Wasm.numerics.
Require Import Wasm.operations.
Require Wasm.memory_list.

Require Import ZArith.
Require Import List.
Require Import FunctionalExtensionality.
Require Import Lia.


Require Import Shared.
Require Import OpMemoryGrowModel.
Require Import ETable.
Require Import MTable.
Require MTable.
Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_memory_grow : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct MemoryGrow i.
Proof.
  unfold opcode_mops_correct. 
  intros i Hrange Heid Hops.
  change (config_mops (opcode_config MemoryGrow i)) with 1.
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).
  pose(mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).

  assert(mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  - apply MTable.mtable_write_mops with
      (offset := etable_values sp_cell i + 1)
      (is_i32 := 1)
      (value := etable_values result i); auto.
    apply (alloc_memory_table_lookup_write_cell_correct _ _ _ _ _ _ _ 
      stack_write i Hrange); auto.
    - apply eid_common.
    - pose(sp_common i); lia.
  lia.
Qed.


Require Import ImageTableModel.
Require Import InjectivityHelper.

Lemma MemoryGrow_decode : forall i st,
  0 <= i ->
  state_rel i st ->
  etable_values enabled_cell i = 1 ->    
  etable_values (ops_cell MemoryGrow) i = 1 ->
  program (wasm_pc st) = IMemoryGrow.
Proof.
  intros i st Hrange Hrel Henabled Hops.
  destruct Hrel as [state_pc_rel _ _ _ _].
  rewrite state_pc_rel.
  destruct (image_table_encoding _ (itable_lookup_in_itable i Hrange Henabled))
             as [fid [iid [Hfid_range [Hiid_range Hencode]]]].
  rewrite (itable_lookup_encode i MemoryGrow Hrange Henabled Hops) in Hencode.
  apply encode_instruction_table_entry_inj in Hencode ; (eauto using fid_common, iid_common, config_opcode_range, opcode_of_instruction_range).
  destruct Hencode as [Hfid [Hid Hopcode]].
  subst.
  apply opcode_of_instruction_inj.
  rewrite <- Hopcode.
  reflexivity.
Qed.

Lemma nth_grow : forall A n (xs ys : list A) b,
  nth_error xs n = Some b ->
  nth_error (seq.cat xs ys) n = Some b.
Proof.
  induction n.
  - simpl.
    destruct xs; simpl; intros; congruence.
  - simpl.  
    destruct xs; [intros; congruence|].
    simpl.
    auto.
Qed.

Lemma lookup_mem_grow : forall memd i b delta,
  memory_list.mem_lookup i memd = Some b ->
  memory_list.mem_lookup i (memory_list.mem_grow delta memd) = Some b.
Proof.
  intros m i b delta Hlookup.
  unfold memory_list.mem_lookup, memory_list.mem_grow in *.
  destruct m; simpl in *.
  apply nth_grow; auto.
Qed.

Lemma read_bytes_grow' : forall  memd memd',
  (forall i b, memory_list.mem_lookup i memd = Some b ->
               memory_list.mem_lookup i memd' = Some b) ->
  
  forall n k a bs,
    those (List.map (fun off  => memory_list.mem_lookup (a + N.of_nat off)%N memd)  (seq.iota k n)) = Some bs ->
    those (List.map (fun off  => memory_list.mem_lookup (a + N.of_nat off)%N memd') (seq.iota k n)) = Some bs.
Proof.
  intros memd memd' Hlookup.
  induction n.
  - intros.
    simpl in *.
    cbv in H. inversion H. reflexivity.
  - simpl.
    intros k a bs H.
    rewrite <- those_those0 in *.
    simpl in *.
    destruct ( memory_list.mem_lookup (a + N.of_nat k)%N memd ) as [b|] eqn:Hb; [|congruence].
    apply Hlookup in Hb.
    rewrite Hb.
    rewrite those_those0 in *.

    destruct (those (List.map (fun off : nat => memory_list.mem_lookup (a + N.of_nat off)%N memd) (seq.iota (S k) n))) as [bs0|] eqn:Hbs0; [| simpl in *; congruence].
    apply IHn in Hbs0.
    rewrite Hbs0.
    assumption.
Qed.    
    
Lemma read_bytes_grow : forall mem delta len a n bs,
    read_bytes mem a n = Some bs ->
    read_bytes {| mem_data := memory_list.mem_grow delta (mem_data mem); mem_max_opt := len |} a n = Some bs.
Proof.
  intros mem delta len a n bs Hread.
  unfold read_bytes in *.
  rewrite <- Hread.
  unfold read_bytes in *.
  simpl.
  rewrite read_bytes_grow'
    with (memd := mem_data mem) (memd' := (memory_list.mem_grow delta (mem_data mem))) (bs := bs).
  - auto.
  - intros.
    apply lookup_mem_grow.
    auto.
  - auto.
Qed.

Lemma length_cat : forall A (xs ys : list A),
    (length (seq.cat xs ys) = length xs + length ys)%nat.
Proof.
  induction xs.
  - reflexivity.
  - simpl. intros. rewrite IHxs. reflexivity.
Qed.

Lemma memory_list_length_grow : forall del md,
      memory_list.mem_length (memory_list.mem_grow (del)%N md)
      = (memory_list.mem_length md + del)%N.
Proof.
  unfold memory_list.mem_grow, memory_list.mem_length.
  destruct md.
  simpl.
  replace  (N.of_nat (length ml_data) + del)%N with  (N.of_nat ((length ml_data) + (N.to_nat del)))%nat by lia.
  f_equal.
  rewrite length_cat.
  rewrite repeat_length.
  reflexivity.
Qed.

Lemma mem_grow_rel : forall  (h: map) (sz delta mp : Z) (mem mem' : memory),
    mem_grow mem (Z.to_N delta) = Some mem' ->
    0 <= delta ->
    heap_rel h sz mp mem ->
    heap_rel h (sz + delta) mp mem'.
Proof.
  intros h sz delta mp mem mem' Hgrow Hdeltarange Hrel.
  unfold mem_grow in Hgrow.
  destruct (mem_size mem + Z.to_N delta <=? page_limit)%N; [|simpl in*; congruence].
  replace (mem_max_opt mem) with (Some (Z.to_N mp)) in Hgrow
    by (destruct Hrel; rewrite heap_limit; reflexivity).
  destruct  (mem_size mem + Z.to_N delta <=? Z.to_N mp)%N ; [|congruence].
  constructor.
    + intros block z Hlen Hget.
      destruct Hrel.
      apply heap_rel_lookup in Hget.
      destruct Hget as [bs [Hread Hdecode]].
      exists bs.
      split; [|assumption].
      inversion Hgrow.
      apply read_bytes_grow; auto.
      rewrite heap_size in heap_bounded.
      specialize (heap_bounded _ _ Hget).
      unfold mem_size in heap_bounded.
      unfold ml_valid in heap_valid.      
      rewrite  (proj2 (N.Div0.div_exact (mem_length mem) page_size)) by (apply heap_valid).
      lia.
    + inversion Hgrow.
      destruct Hrel.
      (* replace  (Z.of_N (sz + delta)) with (Z.of_N sz + Z.of_N delta) by lia. *)
      destruct mem.
      unfold mem_size, mem_length in *.
      simpl.
      rewrite memory_list_length_grow.
      simpl in heap_valid.
      unfold ml_valid in heap_valid.
      replace  (Z.of_N ((memory_list.mem_length mem_data + Z.to_N delta * page_size) / page_size))
        with  ((Z.of_N  (memory_list.mem_length mem_data) + Z.of_N (Z.to_N delta) * (Z.of_N page_size)) / (Z.of_N page_size)) by lia.
      rewrite Z_div_plus_full by (cbv; lia).
      simpl in heap_size.
      lia.
    + inversion Hgrow.
      destruct Hrel as [_ _ Hvalid _].
      unfold ml_valid in *.
      destruct mem. simpl in *.
      rewrite memory_list_length_grow in *.
      rewrite N.Div0.mod_add.
      assumption.
    + inversion Hgrow.
      destruct Hrel as [_ Hsize Hvalid Hbounded].
      rewrite Hsize in Hbounded.
      intros.
      specialize (Hbounded _ _ H).
      Opaque Z.mul page_size.
      unfold ml_valid in *.
      destruct mem; unfold mem_size, mem_length in *; simpl in *.
      lia.
    + inversion Hgrow.
      reflexivity.
    + destruct Hrel; auto.
Qed.

Lemma mem_grow_defined : forall  (h: map) (sz  mp delta :Z) (mem: memory) ,
    0 <= delta ->
    heap_rel h sz mp mem ->
    sz + delta <= mp ->
    exists mem',
      mem_grow mem (Z.to_N delta) = Some mem'.
Proof.
  intros h sz mp delta mem Hdeltarange Hrel Hle.
  destruct Hrel.
  eexists.
  unfold mem_grow.
  replace (mem_size mem + Z.to_N delta <=? page_limit)%N with true.
  2: {
    symmetry.
    rewrite N.leb_le.
    lia.
  }
  rewrite heap_limit.
  replace (mem_size mem + Z.to_N delta <=? Z.to_N mp)%N with true.
  2: {
    symmetry.
    rewrite N.leb_le.
    lia.
  }
  reflexivity.
Qed.

Lemma result_minus_one_when_no_success : forall i,
    0 <= i ->
    etable_values (ops_cell MemoryGrow) i = 1 ->
    etable_values success i = 0 ->
    etable_values result i = 0xFFFFFFFF.
Proof.
  intros i Hrange Hops Hsuccess.
  pose(H := memory_grow_return_value i Hrange).
  simpl value in H.
  unfold ForallP in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.

Lemma result_old_memory_when_success : forall i,
    0 <= i ->
    etable_values (ops_cell MemoryGrow) i = 1 ->
    etable_values success i = 1 ->
    etable_values result i = etable_values mpages_cell i.
Proof.
  intros i Hrange Hops Hsuccess.
  pose(H := memory_grow_return_value i Hrange).
  simpl value in H.
  unfold ForallP in H.
  replace(i+0) with i in * by lia.
  lia.
Qed.
    
Lemma new_memory_does_not_exceed_maximum : forall i,
    0 <= i ->
    etable_values (ops_cell MemoryGrow) i = 1 ->
    etable_values success i = 1 ->
    etable_values current_memory_size i + etable_values grow_size i <=
    etable_values maximal_memory_pages i.
Proof.
  intros i Hrange Hops Hsuccess.
  pose(H := memory_grow_updated_memory_size i Hrange).
  simpl in H.
  replace(i+0) with i in * by lia.
  pose(current_maximal_diff_common i).
  lia.
Qed.

Lemma MemoryGrowop_mops : forall i,
    0 <= i ->
    etable_values eid_cell i > 0 ->
    etable_values enabled_cell i = 1 ->
    etable_values (ops_cell MemoryGrow) i = 1 ->
    mops_at_correct i ->
        mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack = 1
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Global = 0
    /\  mops_at (etable_values eid_cell i) MTableModel.LocationType_Heap = 0.
Proof.
  intros i Hrange Heid_nonzero Hrow_enabled Hop_class Hops.
  unfold mops_at_correct in Hops.
  replace (class_of_row i) with MemoryGrow in Hops.
  2: {
    symmetry.
    rewrite (proj1 (class_of_row_op i MemoryGrow Hrow_enabled)); auto.
  }
  simpl in Hops.
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Heap).
  pose (mops_at_nonnegative (etable_values eid_cell i) MTableModel.LocationType_Global).

  assert ( mops_at (etable_values eid_cell i) MTableModel.LocationType_Stack >= 1).
  {
    apply (write_cell_mops _ _ _ _ _ _ _ stack_write i Hrange); auto.
    - apply (eid_common i).
    - pose (sp_common i); lia.
  }
  lia.
Qed.
    
Definition memory_grow success current : Z :=
  match success with
  | 1 => current
  | _ => 0xFFFFFFFF
  end.

(* The zkWasm constraints are less deterministic than WasmCert, it may refuse to grow
   a memory even if it is within the limit, and then let a later grow operation 
   succeed. (This probably is allowed by the English-language Wasm specification, even if 
   it would not be done by Wasmi.) So we have two cases, one when the operation succeeds
   and one it doesn't.
   Becuase we cover both possible values of (success i) this handles all possible traces. 
 *)
Theorem MemoryGrowOp_correct_nosuccess : forall i st x1 xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell MemoryGrow) i = 1 ->
  etable_values success i = 0   ->
  state_rel i st ->
  wasm_stack st = x1:: xs ->
  state_rel (i+1) (update_stack (incr_iid st) (0xFFFFFFFF :: xs)).
Proof.
  intros i st x1 xs Hrange Hrow_enabled Hmops Hop Hsuccess Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (MemoryGrowop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hread: etable_values grow_size i = x1).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => 1)
                                 (enable := fun get => get (ops_cell MemoryGrow))
                                 (value := fun get => get grow_size).
    - apply Hrange.
    - apply Hop.
    - auto.
    - eauto.
    - eauto.
    - apply stack_read.
  }
  assert (Hres: etable_values result i =  0xFFFFFFFF).
  {
    apply (result_minus_one_when_no_success i Hrange Hop Hsuccess).
  }
  rewrite <-Hread in Hstk.  rewrite <-Hres. clear Hread Hres.

  assert (wasm_pc (update_stack (incr_iid st) (etable_values result i :: xs))
    = (etable_values fid_cell (i+1), etable_values iid_cell (i+1))).
  - rewrite fid_change with (idx := MemoryGrow); auto.
    rewrite iid_change with (idx := MemoryGrow); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values result i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    destruct Hrel.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.

  eapply stack_rel_write_1_without_value with (col:=memory_table_lookup_stack_write)
                                (is_i32 := fun get => 1)
                                (value := fun get => get result)
                                (enable := fun get => get (ops_cell MemoryGrow)); auto; try lia.
    + apply Hstk.
    + pose(Hsp := sp_change i MemoryGrow Hrange Hrow_enabled Hop).
      replace(config_sp_diff (opcode_config MemoryGrow i)) with 0 in Hsp by constructor.
      lia .
    + rewrite (mpages_change i _ Hrange Hrow_enabled Hop).
      simpl.
      lia.
    + rewrite (frame_id_change i MemoryGrow); auto; reflexivity.
    + rewrite (fid_change i MemoryGrow); auto.
    + apply stack_write.
Qed.

Theorem MemoryGrowOp_correct_success : forall i st x1 xs,
  0 <= i ->
  etable_values enabled_cell i = 1 ->
  mops_at_correct i ->
  etable_values (ops_cell MemoryGrow) i = 1 ->
  etable_values success i = 1   ->
  state_rel i st ->
  wasm_stack st = x1:: xs ->
  exists mem',
    mem_grow (wasm_memory st) (Z.to_N x1) = Some mem' /\
    state_rel (i+1) (update_memory (update_stack (incr_iid st) (Z.of_N (mem_size (wasm_memory st)) :: xs)) mem').
Proof.
  intros i st x1 xs Hrange Hrow_enabled Hmops Hop Hsuccess Hrel Hstk.
  assert (Heid_nonzero := eid_nonzero i Hrange Hrow_enabled).
  apply (MemoryGrowop_mops) in Hmops; auto. destruct Hmops as [Hmops [Hmops' Hmops'']].
  assert (Hread: etable_values grow_size i = x1).
  {
    eapply stack_rel_read_1_without_value with (is_i32 := fun get => 1)
                                 (enable := fun get => get (ops_cell MemoryGrow))
                                 (value := fun get => get grow_size).
    - apply Hrange.
    - apply Hop.
    - auto.
    - eauto.
    - eauto.
    - apply stack_read.
  }
  assert (Hres: etable_values result i =   Z.of_N (mem_size (wasm_memory st))).
  {
    destruct Hrel.
    destruct state_heap_rel.
    rewrite <- heap_size.
    apply(result_old_memory_when_success i Hrange Hop Hsuccess).
  }
  rewrite <-Hread in *. rewrite <-Hres. clear Hread Hres.
  destruct Hrel.
  assert (grow_size_U64_i := grow_size_U64 i).
  destruct (mem_grow_defined _
                             (etable_values current_memory_size i)
                             (etable_values maximal_memory_pages i)
                             (etable_values grow_size i)
                             (wasm_memory st)
                             ltac:(lia)
                             state_heap_rel)
    as [mem' Hgrow].
    { apply new_memory_does_not_exceed_maximum; auto. }
  exists mem'.
  split; [ assumption | ].
  
  constructor.
  - rewrite fid_change with (idx := MemoryGrow); auto.
    rewrite iid_change with (idx := MemoryGrow); auto.
    simpl.
    pose(H := pc_incr_iid (update_stack st (etable_values result i :: xs))).
    rewrite pc_update_stack in H.
    rewrite incr_iid_update_stack in *.
    rewrite pc_update_memory.
    rewrite pc_update_stack_incr_iid.
    rewrite state_pc_rel in H; auto.    
  - Opaque stack_rel.
    rewrite stack_update_memory, stack_update_stack.
    rewrite eid_change in *; auto.
    eapply stack_rel_write_without_value
      with
      (col:=memory_table_lookup_stack_write)
      (i := i)
      (n := (0%nat))
      (is_i32 := fun get => 1)
      (value := fun get => get result)
      (enable := fun get => get (ops_cell MemoryGrow))
      (stk1 := nil); auto.
    + lia.
    + rewrite Hstk in state_stack_rel.
      rewrite (sp_change i MemoryGrow Hrange Hrow_enabled Hop).
      replace(config_sp_diff (opcode_config MemoryGrow i)) with 0 by constructor.
      replace  (etable_values sp_cell i + 0 + 1) with  (etable_values sp_cell i + 1) by lia.
      apply state_stack_rel.
    + rewrite (sp_change i MemoryGrow Hrange Hrow_enabled Hop).
      replace(config_sp_diff (opcode_config MemoryGrow i)) with 0 by constructor.
      lia.
    + replace (fun get : etable_cols -> Z => get sp_cell + 1 + Z.of_nat 0)
        with  (fun get : etable_cols -> Z => get sp_cell + 1)
        by (extensionality get; lia).
      apply stack_write.
  - rewrite globals_update_memory, globals_update_stack.
    rewrite eid_change by auto.
    rewrite globals_no_write by auto.
    rewrite globals_incr_iid.
    auto.
  - rewrite memory_update_memory.
    rewrite eid_change by auto.
    rewrite memory_no_write by auto.
    rewrite (mpages_change i _ Hrange Hrow_enabled Hop); simpl.
    rewrite (maximal_memory_pages_change i) by auto.
    replace (etable_values current_memory_size i + etable_values success i * etable_values grow_size i) with (etable_values current_memory_size i +  etable_values grow_size i) by lia.
    apply (mem_grow_rel _ _ _ _ _ _ Hgrow).
    + lia.
    + apply state_heap_rel.
  - rewrite callstack_update_memory, callstack_update_stack, callstack_incr_iid.
    rewrite (frame_id_change i MemoryGrow); simpl; auto.
    rewrite (fid_change i MemoryGrow); simpl; auto.
Qed.
