Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import IntegerFunctions.
Require Import RTableModel.
Require Import RTable.
Require Import BitTableModel.
Require Import InjectivityHelper.

Open Scope Z_scope.
    
  Lemma stupid_add x y z : x+y=z -> forall w, w+x+y = w+z.
  Proof.  intros. lia. Qed.

  #[export] Hint Rewrite (stupid_add 0 0 0 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 0 1 1 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 0 2 2 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 0 3 3 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 0 4 4 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 0 5 5 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 0 6 6 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 0 7 7 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 0 8 8 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 0 9 9 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 0 10 10 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 1 0 1 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 1 1 2 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 1 2 3 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 1 3 4 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 1 4 5 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 1 5 6 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 1 6 7 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 1 7 8 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 1 8 9 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 1 9 10 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 1 10 11 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 2 0 2 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 2 1 3 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 2 2 4 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 2 3 5 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 2 4 6 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 2 5 7 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 2 6 8 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 2 7 9 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 2 8 10 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 2 9 11 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 2 10 12 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 3 0 3 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 3 1 4 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 3 2 5 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 3 3 6 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 3 4 7 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 3 5 8 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 3 6 9 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 3 7 10 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 3 8 11 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 3 9 12 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 3 10 13 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 4 0 4 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 4 1 5 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 4 2 6 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 4 3 7 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 4 4 8 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 4 5 9 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 4 6 10 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 4 7 11 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 4 8 12 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 4 9 13 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 4 10 14 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 5 0 5 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 5 1 6 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 5 2 7 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 5 3 8 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 5 4 9 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 5 5 10 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 5 6 11 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 5 7 12 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 5 8 13 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 5 9 14 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 5 10 15 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 6 0 6 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 6 1 7 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 6 2 8 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 6 3 9 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 6 4 10 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 6 5 11 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 6 6 12 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 6 7 13 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 6 8 14 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 6 9 15 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 6 10 16 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 7 0 7 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 7 1 8 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 7 2 9 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 7 3 10 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 7 4 11 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 7 5 12 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 7 6 13 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 7 7 14 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 7 8 15 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 7 9 16 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 7 10 17 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 8 0 8 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 8 1 9 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 8 2 10 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 8 3 11 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 8 4 12 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 8 5 13 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 8 6 14 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 8 7 15 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 8 8 16 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 8 9 17 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 8 10 18 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 9 0 9 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 9 1 10 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 9 2 11 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 9 3 12 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 9 4 13 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 9 5 14 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 9 6 15 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 9 7 16 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 9 8 17 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 9 9 18 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 9 10 19 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 10 0 10 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 10 1 11 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 10 2 12 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 10 3 13 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 10 4 14 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 10 5 15 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 10 6 16 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 10 7 17 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 10 8 18 eq_refl) : bit_table. #[export] Hint Rewrite (stupid_add 10 9 19 eq_refl) : bit_table.
  #[export] Hint Rewrite (stupid_add 10 10 20 eq_refl) : bit_table.



Lemma add_modulo : forall a b k N,
  N <> 0 ->
  a mod N = b mod N  ->
      (a+k) mod N =  (b+k) mod N.
Proof.
  intros.
  rewrite (Z.add_mod a) by auto.
  rewrite (Z.add_mod b) by auto. 
  rewrite H0.  
  reflexivity.
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

Import BitTableModel.
Export BitTableModel.

Lemma bit_table_lookup_op : forall i,
    bit_table_values lookup_sel i = 1 ->
    in_op_table (bit_table_values op i)
                (bit_table_values val_l i)
                (bit_table_values val_r i)
                (bit_table_values val_res i).
Proof.
  intros.
  replace (bit_table_values op i) with (1 * bit_table_values op i) by lia.
  replace (bit_table_values val_l i) with (1 * bit_table_values val_l i) by lia.
  replace (bit_table_values val_r i) with (1 * bit_table_values val_r i) by lia.
  replace (bit_table_values val_res i) with (1 * bit_table_values val_res i) by lia.
  rewrite <- H.
  apply (bit_table_configure_in_op_table i); auto.
Qed.

Lemma op_preserved : forall i,
    0 <= i ->
    (bit_table_values u32_sel i + bit_table_values lookup_sel i <> 0) ->
    bit_table_values op i = bit_table_values op (i-1).
Proof.
  intros i Hi Hnonzero.
  assert (H:=bit_table_gate_1 i ltac:(lia)).
  simpl in H.
  destruct H as [H _].
  replace (i+0) with i in * by lia.
  (* replace (i mod bit_table_numRows) with i in * by (symmetry; eauto using Z.mod_small).*)
  apply circuit_if in H; [|lia].
  replace (i + -1) with (i-1) in * by lia.
  lia.
Qed.  
 
Section blockwise.
  Variable i : Z.
  Hypothesis i_range : 0 <= i.
  
  Hypothesis is_block_1 : bit_table_values block_sel (i+1) = 1.

  Lemma i_val : Zmod (i-bit_table_start) STEP_SIZE = 0.
  Proof.
    rewrite block_sel_spec in is_block_1.
    destruct (Z.eq_dec ((i + 1 - bit_table_start) mod STEP_SIZE) BLOCK_SEL_OFFSET); [|congruence].
    change (BLOCK_SEL_OFFSET) with (1 mod STEP_SIZE) in e.
    apply add_modulo with (k:=-1) in e; [|unfold STEP_SIZE; lia].    
    replace (i + 1 - bit_table_start + -1) with ((i - bit_table_start)) in * by lia.
    change ((1 + -1) mod STEP_SIZE) with 0 in *.
    auto.
  Qed.

  Lemma i_val_plus: forall k,
      0 <= k < STEP_SIZE ->
      Zmod (i+k-bit_table_start) STEP_SIZE = k.
  Proof.
    intros.
    replace (i+k-bit_table_start) with ((i-bit_table_start)+k) by lia.
    rewrite <- Zplus_mod_idemp_l.
    rewrite i_val.
    rewrite Z.mod_small; lia.
  Qed.
    
  (* We can first specify all the values for block_sel, u32_sel, lookup_sel explicitly. *)
  Lemma is_block_0 : bit_table_values block_sel i = 0.
  Proof. rewrite block_sel_spec, i_val; reflexivity. Qed.
  Lemma is_block_2 : bit_table_values block_sel (i+2) = 0.
  Proof. rewrite block_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_block_3 : bit_table_values block_sel (i+3) = 0.
  Proof. rewrite block_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_block_4 : bit_table_values block_sel (i+4) = 0.
  Proof. rewrite block_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_block_5 : bit_table_values block_sel (i+5) = 0.
  Proof. rewrite block_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_block_6 : bit_table_values block_sel (i+6) = 0.
  Proof. rewrite block_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_block_7 : bit_table_values block_sel (i+7) = 0.
  Proof. rewrite block_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_block_8 : bit_table_values block_sel (i+8) = 0.
  Proof. rewrite block_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_block_9 : bit_table_values block_sel (i+9) = 0.
  Proof. rewrite block_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_block_10 : bit_table_values block_sel (i+10) = 0.
  Proof. rewrite block_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.

  Hint Rewrite is_block_0 is_block_1 is_block_2 is_block_3 is_block_4 is_block_5 is_block_6 is_block_7 is_block_8 is_block_9 is_block_10 : bit_table.
  
  Lemma is_u32_0 : bit_table_values u32_sel i = 0.
  Proof. rewrite u32_sel_spec. rewrite i_val. reflexivity. Qed.
  Lemma is_u32_1 : bit_table_values u32_sel (i+1) = 1.
  Proof. rewrite u32_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_u32_2 : bit_table_values u32_sel (i+2) = 0.
  Proof. rewrite u32_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_u32_3 : bit_table_values u32_sel (i+3) = 0.
  Proof. rewrite u32_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_u32_4 : bit_table_values u32_sel (i+4) = 0.
  Proof. rewrite u32_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_u32_5 : bit_table_values u32_sel (i+5) = 0.
  Proof. rewrite u32_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_u32_6 : bit_table_values u32_sel (i+6) = 1.
  Proof. rewrite u32_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_u32_7 : bit_table_values u32_sel (i+7) = 0.
  Proof. rewrite u32_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_u32_8 : bit_table_values u32_sel (i+8) = 0.
  Proof. rewrite u32_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_u32_9 : bit_table_values u32_sel (i+9) = 0.
  Proof. rewrite u32_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_u32_10 : bit_table_values u32_sel (i+10) = 0.
  Proof. rewrite u32_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.

  Hint Rewrite is_u32_0 is_u32_1 is_u32_2 is_u32_3 is_u32_4 is_u32_5 is_u32_6 is_u32_7 is_u32_8 is_u32_9 is_u32_10 : bit_table.
  
  Lemma is_lookup_0 : bit_table_values lookup_sel i = 0.
  Proof. rewrite lookup_sel_spec. rewrite i_val. reflexivity. Qed.
  Lemma is_lookup_1 : bit_table_values lookup_sel (i+1) = 0.
  Proof. rewrite lookup_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_lookup_2 : bit_table_values lookup_sel (i+2) = 1.
  Proof. rewrite lookup_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_lookup_3 : bit_table_values lookup_sel (i+3) = 1.
  Proof. rewrite lookup_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_lookup_4 : bit_table_values lookup_sel (i+4) = 1.
  Proof. rewrite lookup_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_lookup_5 : bit_table_values lookup_sel (i+5) = 1.
  Proof. rewrite lookup_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_lookup_6 : bit_table_values lookup_sel (i+6) = 0.
  Proof. rewrite lookup_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_lookup_7 : bit_table_values lookup_sel (i+7) = 1.
  Proof. rewrite lookup_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_lookup_8 : bit_table_values lookup_sel (i+8) = 1.
  Proof. rewrite lookup_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_lookup_9 : bit_table_values lookup_sel (i+9) = 1.
  Proof. rewrite lookup_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.
  Lemma is_lookup_10 : bit_table_values lookup_sel (i+10) = 1.
  Proof. rewrite lookup_sel_spec. rewrite i_val_plus by (unfold STEP_SIZE; lia). reflexivity. Qed.

  Hint Rewrite is_lookup_0 is_lookup_1 is_lookup_2 is_lookup_3 is_lookup_4 is_lookup_5 is_lookup_6 is_lookup_7 is_lookup_8 is_lookup_9 is_lookup_10 : bit_table.
  
  Definition OP := bit_table_values op i.
  Lemma is_op_0 : bit_table_values op i = OP.
  Proof. reflexivity. Qed.
  
  Lemma is_op_1 : bit_table_values op (i+1) = OP.
  Proof. unfold OP; rewrite op_preserved; [| lia | autorewrite with bit_table; lia].
    - replace (i + 1 - 1) with i by lia. reflexivity.
  Qed.
  Lemma is_op_2 : bit_table_values op (i+2) = OP.
  Proof. unfold OP; rewrite op_preserved; [| lia | autorewrite with bit_table; lia].
    - replace (i + 2 - 1) with (i+1) by lia. apply is_op_1.
  Qed.
  Lemma is_op_3 : bit_table_values op (i+3) = OP.
  Proof. unfold OP; rewrite op_preserved; [| lia | autorewrite with bit_table; lia].
    - replace (i + 3 - 1) with (i+2) by lia. apply is_op_2.
  Qed.
  Lemma is_op_4 : bit_table_values op (i+4) = OP.
  Proof. unfold OP; rewrite op_preserved; [| lia | autorewrite with bit_table; lia].
    - replace (i + 4 - 1) with (i+3) by lia. apply is_op_3.
  Qed.
  Lemma is_op_5 : bit_table_values op (i+5) = OP.
  Proof. unfold OP; rewrite op_preserved; [| lia | autorewrite with bit_table; lia].
    - replace (i + 5 - 1) with (i+4) by lia. apply is_op_4.
  Qed.
  Lemma is_op_6 : bit_table_values op (i+6) = OP.
  Proof. unfold OP; rewrite op_preserved; [| lia | autorewrite with bit_table; lia].
    - replace (i + 6 - 1) with (i+5) by lia. apply is_op_5.
  Qed.
  Lemma is_op_7 : bit_table_values op (i+7) = OP.
  Proof. unfold OP; rewrite op_preserved; [| lia | autorewrite with bit_table; lia].
    - replace (i + 7 - 1) with (i+6) by lia. apply is_op_6.
  Qed.
  Lemma is_op_8 : bit_table_values op (i+8) = OP.
  Proof. unfold OP; rewrite op_preserved; [| lia | autorewrite with bit_table; lia].
    - replace (i + 8 - 1) with (i+7) by lia. apply is_op_7.
  Qed.
  Lemma is_op_9 : bit_table_values op (i+9) = OP.
  Proof. unfold OP; rewrite op_preserved; [| lia | autorewrite with bit_table; lia].
    - replace (i + 9 - 1) with (i+8) by lia. apply is_op_8.
  Qed.
  Lemma is_op_10 : bit_table_values op (i+10) = OP.
  Proof. unfold OP; rewrite op_preserved; [| lia | autorewrite with bit_table; lia].
    - replace (i + 10 - 1) with (i+9) by lia. apply is_op_9.
  Qed.

  Hint Rewrite is_op_0 is_op_1 is_op_2 is_op_3 is_op_4 is_op_5 is_op_6 is_op_7 is_op_8 is_op_9 is_op_10 : bit_table.

  Lemma OP_cases :
    OP = BitOp_And \/ OP = BitOp_Or \/ OP = BitOp_Xor \/ OP = Popcnt_index.
  Proof.
    assert (H:=bit_table_gate_1 (i+1) ltac:(lia)).
    destruct H as [_ [_ [H _]]].
    simpl in H.
    rewrite <- !Z.mul_assoc in H.
    apply circuit_if in H ; [|autorewrite with bit_table; congruence].
    autorewrite with bit_table in H.
    apply circuit_or in H; destruct H.
    {
      apply circuit_eq in H.
      destruct (bit_table_gate_1 (i+1) ltac:(lia)) as [_ [H2 _]].
      simpl in H2.
      autorewrite with bit_table in H2.
      rewrite <- !Z.mul_assoc in H2.
      apply circuit_if in H2; [|congruence].
      apply circuit_if in H2; [|congruence].
      apply circuit_eq in H2.
      right. right. right. congruence.
    }
    {
      apply circuit_or in H; destruct H; [apply circuit_eq in H; left; congruence | right ].
      apply circuit_or in H; destruct H; [apply circuit_eq in H; left; congruence | right ].
      apply circuit_eq in H; left; congruence.
    }
  Qed.
  
  Lemma compose_l_1 : bit_table_values val_l (i+1) =
                        bit_table_values val_l (i+2) 
                      + bit_table_values val_l (i+3) * (Z.shiftl 1 8)
                      + bit_table_values val_l (i+4) * (Z.shiftl 1 16)
                        + bit_table_values val_l (i+5) * (Z.shiftl 1 24).
  Proof.
    assert (H:=bit_table_gate_2 (i+1) ltac:(lia)).
    destruct H as [H _].
    simpl in H.
    unfold compose_u32, compose_u32_helper in H. simpl in H.
    apply circuit_if in H.
    {
      apply circuit_eq in H. symmetry in H.
      autorewrite with bit_table in *.
      simpl.
      lia.
    }
    {
      autorewrite with bit_table.
      lia.
    }
  Qed.

  Lemma compose_l_6 : bit_table_values val_l (i+6) =
                        bit_table_values val_l (i+7) 
                      + bit_table_values val_l (i+8) * (Z.shiftl 1 8)
                      + bit_table_values val_l (i+9) * (Z.shiftl 1 16)
                        + bit_table_values val_l (i+10) * (Z.shiftl 1 24).
  Proof.
    assert (H:=bit_table_gate_2 (i+6) ltac:(lia)).
    destruct H as [H _].
    simpl in H.
    unfold compose_u32, compose_u32_helper in H. simpl in H.
    apply circuit_if in H.
    {
      apply circuit_eq in H. symmetry in H.
      autorewrite with bit_table in *.
      simpl.
      lia.
    }
    {
      autorewrite with bit_table.
      lia.
    }
  Qed.

  Lemma compose_l_0 :
    bit_table_values val_l i
    = bit_table_values val_l (i+1) + bit_table_values val_l (i+6) * (Z.shiftl 1 32).
  Proof.
    assert (H:=bit_table_gate_3 (i+1) ltac:(lia)).
    destruct H as [H _].
    unfold compose_u64 in H.
    simpl in H.
    replace (i+1+ -1) with (i) in * by lia.
    autorewrite with bit_table in *.
    simpl.
    lia.
  Qed.

  Lemma shiftl_add : forall a b n,
      0 <= n ->
      Z.shiftl (a+b) n = (Z.shiftl a n) + (Z.shiftl b n).
  Proof.
    intros.
    rewrite !Z.shiftl_mul_pow2 by lia.
    lia.
  Qed.

  Lemma l_0_spec :
          bit_table_values val_l i
          =  bit_table_values val_l (i+2) 
             + Z.shiftl (bit_table_values val_l (i+3)
             + Z.shiftl (bit_table_values val_l (i+4) 
             + Z.shiftl (bit_table_values val_l (i+5)
             + Z.shiftl (bit_table_values val_l (i+7)
             + Z.shiftl (bit_table_values val_l (i+8)
             + Z.shiftl (bit_table_values val_l (i+9)
             + Z.shiftl (bit_table_values val_l (i+10)) 8) 8) 8) 8) 8) 8) 8.
  Proof.
    rewrite compose_l_0.
    rewrite compose_l_1.
    rewrite compose_l_6.
    rewrite !Z.shiftl_1_l.
    rewrite <- !Z.shiftl_mul_pow2 by lia.
    rewrite !shiftl_add by lia.
    rewrite !Z.shiftl_shiftl by lia.
    rewrite !Z.add_assoc.
    reflexivity.
  Qed.
    
  Lemma compose_r_0 :
    bit_table_values val_r i
    = bit_table_values val_r (i+1) + bit_table_values val_r (i+6) * (Z.shiftl 1 32).
  Proof.
    assert (H:=bit_table_gate_3 (i+1) ltac:(lia)).
    destruct H as [_ [H _]].
    unfold compose_u64 in H.
    simpl in H.
    replace (i+1+ -1) with (i) in * by lia.
    autorewrite with bit_table in *.
    simpl.
    lia.
  Qed.
  
  Lemma compose_r_1 : bit_table_values val_r (i+1) =
                        bit_table_values val_r (i+2) 
                      + bit_table_values val_r (i+3) * (Z.shiftl 1 8)
                      + bit_table_values val_r (i+4) * (Z.shiftl 1 16)
                        + bit_table_values val_r (i+5) * (Z.shiftl 1 24).
  Proof.
    assert (H:=bit_table_gate_2 (i+1) ltac:(lia)).
    destruct H as [_ [H _]].
    simpl in H.
    unfold compose_u32, compose_u32_helper in H. simpl in H.
    apply circuit_if in H.
    {
      apply circuit_eq in H. symmetry in H.
      autorewrite with bit_table in *.
      simpl.
      lia.
    }
    {
      autorewrite with bit_table in *.
      lia.
    }
  Qed.

  Lemma compose_r_6 : bit_table_values val_r (i+6) =
                        bit_table_values val_r (i+7) 
                      + bit_table_values val_r (i+8) * (Z.shiftl 1 8)
                      + bit_table_values val_r (i+9) * (Z.shiftl 1 16)
                        + bit_table_values val_r (i+10) * (Z.shiftl 1 24).
  Proof.
    assert (H:=bit_table_gate_2 (i+6) ltac:(lia)).
    destruct H as [_ [H _]].
    simpl in H.
    unfold compose_u32, compose_u32_helper in H. simpl in H.
    apply circuit_if in H.
    {
      apply circuit_eq in H. symmetry in H.
      autorewrite with bit_table in *.
      simpl.
      lia.
    }
    {
      autorewrite with bit_table in *.
      lia.
    }
  Qed.

  Lemma r_0_spec :
          bit_table_values val_r i
          =  bit_table_values val_r (i+2) 
             + Z.shiftl (bit_table_values val_r (i+3)
             + Z.shiftl (bit_table_values val_r (i+4) 
             + Z.shiftl (bit_table_values val_r (i+5)
             + Z.shiftl (bit_table_values val_r (i+7)
             + Z.shiftl (bit_table_values val_r (i+8)
             + Z.shiftl (bit_table_values val_r (i+9)
             + Z.shiftl (bit_table_values val_r (i+10)) 8) 8) 8) 8) 8) 8) 8.
  Proof.
    rewrite compose_r_0.
    rewrite compose_r_1.
    rewrite compose_r_6.
    rewrite !Z.shiftl_1_l.
    rewrite <- !Z.shiftl_mul_pow2 by lia.
    rewrite !shiftl_add by lia.
    rewrite !Z.shiftl_shiftl by lia.
    rewrite !Z.add_assoc.
    reflexivity.
  Qed.
  
  Section blockwise_bitop.
    Hypothesis op_isnt_popcnt : OP <> Popcnt_index.

    Lemma is_popcnt_false : forall k,
        0 <= k ->
        bit_table_values u32_sel k = 1 ->
        bit_table_values op k <> Popcnt_index ->
        bit_table_values helper k = 0.
    Proof.
      intros k Hrange Hu32 Hop.
      assert (H:=bit_table_gate_1 k ltac:(lia)).
      destruct H as [_ [H _]].
      replace (k+0) with k in * by lia.
      rewrite <- Z.mul_assoc in H. (* Need a circuit_mul_assoc lemma. *)
      apply circuit_if in H ; [|simpl; congruence].
      {
        apply circuit_or in H; destruct H.
        - auto.
        - apply circuit_eq in H.
          simpl in H.
          congruence.
      }
    Qed.
    
    Lemma is_bit_1 : bit_table_values helper (i+1) = 0.
    Proof.
      apply is_popcnt_false; [lia| |]; autorewrite with bit_table; auto.
    Qed.
    Lemma is_bit_6 : bit_table_values helper (i+6) = 0.
      apply is_popcnt_false; [lia| |]; autorewrite with bit_table; auto.
    Qed.
    
    Lemma compose_res_1 : bit_table_values val_res (i+1) =
                          bit_table_values val_res (i+2) 
                          + bit_table_values val_res (i+3) * (Z.shiftl 1 8)
                          + bit_table_values val_res (i+4) * (Z.shiftl 1 16)
                          + bit_table_values val_res (i+5) * (Z.shiftl 1 24).
    Proof.
      assert (H:=bit_table_gate_2 (i+1) ltac:(lia)).
      destruct H as [_ [_ [H _]]].
      simpl in H.
      unfold compose_u32_if_bit, compose_u32, compose_u32_helper in H.
      simpl in H.
      rewrite Z.mul_comm in H.
      apply circuit_if in H.
      2: {
        unfold is_bit, is_popcnt.
        pose is_bit_1.
        autorewrite with bit_table in *.
        lia.
      }
      {
        apply circuit_if in H.
        2: {
          autorewrite with bit_table.
          lia.
        }
        {
          apply circuit_eq in H. symmetry in H.
          autorewrite with bit_table in *.
          simpl.
          lia.
        }
      }
    Qed.

    Lemma compose_res_6 : bit_table_values val_res (i+6) =
                         bit_table_values val_res (i+7) 
                          + bit_table_values val_res (i+8) * (Z.shiftl 1 8)
                          + bit_table_values val_res (i+9) * (Z.shiftl 1 16)
                          + bit_table_values val_res (i+10) * (Z.shiftl 1 24).
    Proof.
      assert (H:=bit_table_gate_2 (i+6) ltac:(lia)).
      destruct H as [_ [_ [H _]]].
      simpl in H.
      unfold compose_u32_if_bit, compose_u32, compose_u32_helper in H.
      simpl in H.
      rewrite Z.mul_comm in H.
      apply circuit_if in H.
      2: {
        unfold is_bit, is_popcnt.
        replace (i+6+0) with (i+6) by lia.
        pose is_bit_6.
        lia.
      }
      {
        apply circuit_if in H.
        2: {
          autorewrite with bit_table.
          lia.
        }
        {
          apply circuit_eq in H. symmetry in H.
          autorewrite with bit_table in *.
          simpl.
          lia.
        }
      }
    Qed.
    
    Lemma compose_res_0 :
      bit_table_values val_res i
      = bit_table_values val_res (i+1) + bit_table_values val_res (i+6) * (Z.shiftl 1 32).
    Proof.
      pose is_bit_1.
      assert (H:=bit_table_gate_3 (i+1) ltac:(lia)).
      destruct H as [_ [_ [H _]]].
      unfold compose_u64_if_bit, compose_u64 in H.
      simpl in H.
      replace (i+1+ -1) with (i) in * by lia.
      unfold is_bit, is_popcnt in H.
      autorewrite with bit_table in *.
      simpl.
      lia.
    Qed.

    Lemma res_0_spec :
          bit_table_values val_res i
          =  bit_table_values val_res (i+2) 
             + Z.shiftl (bit_table_values val_res (i+3)
             + Z.shiftl (bit_table_values val_res (i+4) 
             + Z.shiftl (bit_table_values val_res (i+5)
             + Z.shiftl (bit_table_values val_res (i+7)
             + Z.shiftl (bit_table_values val_res (i+8)
             + Z.shiftl (bit_table_values val_res (i+9)
             + Z.shiftl (bit_table_values val_res (i+10)) 8) 8) 8) 8) 8) 8) 8.
    Proof.
      rewrite compose_res_0.
      rewrite compose_res_1.
      rewrite compose_res_6.
      rewrite !Z.shiftl_1_l.
      rewrite <- !Z.shiftl_mul_pow2 by lia.
      rewrite !shiftl_add by lia.
      rewrite !Z.shiftl_shiftl by lia.
      rewrite !Z.add_assoc.
      reflexivity.
    Qed.      
  End blockwise_bitop.

  Section blockwise_bitop_and.
    Hypothesis op_is_And : OP = BitOp_And.
    
    Lemma bitop_and : forall k,
        bit_table_values op k = OP ->
        bit_table_values lookup_sel k = 1 ->
            (0 <= (bit_table_values val_l k) < 256)
         /\ (0 <= (bit_table_values val_r k) < 256)
         /\ bit_table_values val_res k = Z.land (bit_table_values val_l k)
                                                (bit_table_values val_r k).
    Proof.
      intros k is_op is_lookup.
      eapply in_op_table_and. 
      rewrite <- op_is_And.
      rewrite <- is_op.
      apply bit_table_lookup_op.
      rewrite is_lookup.
      auto.
    Qed.
    
    Lemma bitop_and_spec :
      bit_table_values val_res i = Z.land (bit_table_values val_l i)
                                          (bit_table_values val_r i).
    Proof.
      rewrite l_0_spec.
      rewrite r_0_spec.
      rewrite res_0_spec by (rewrite op_is_And; unfold BitOp_And, Popcnt_index; lia).

      destruct (bitop_and (i+2) is_op_2 is_lookup_2) as [H2_l [H2_r H2_res]].
      rewrite (plus_lor _ _ H2_l).
      rewrite (plus_lor _ _ H2_r).
      rewrite H2_res.
      rewrite (plus_lor _ _ (land_bound H2_l H2_r)).
      rewrite land_compose by auto.
      f_equal. f_equal.

      destruct (bitop_and (i+3) is_op_3 is_lookup_3) as [H3_l [H3_r H3_res]].
      rewrite (plus_lor _ _ H3_l).
      rewrite (plus_lor _ _ H3_r).
      rewrite H3_res.
      rewrite (plus_lor _ _ (land_bound H3_l H3_r)).
      rewrite land_compose by auto.
      f_equal. f_equal.

      destruct (bitop_and (i+4) is_op_4 is_lookup_4) as [H4_l [H4_r H4_res]].
      rewrite (plus_lor _ _ H4_l).
      rewrite (plus_lor _ _ H4_r).
      rewrite H4_res.
      rewrite (plus_lor _ _ (land_bound H4_l H4_r)).
      rewrite land_compose by auto.
      f_equal. f_equal.

      destruct (bitop_and (i+5) is_op_5 is_lookup_5) as [H5_l [H5_r H5_res]].
      rewrite (plus_lor _ _ H5_l).
      rewrite (plus_lor _ _ H5_r).
      rewrite H5_res.
      rewrite (plus_lor _ _ (land_bound H5_l H5_r)).
      rewrite land_compose by auto.
      f_equal. f_equal.
      
      destruct (bitop_and (i+7) is_op_7 is_lookup_7) as [H7_l [H7_r H7_res]].
      rewrite (plus_lor _ _ H7_l).
      rewrite (plus_lor _ _ H7_r).
      rewrite H7_res.
      rewrite (plus_lor _ _ (land_bound H7_l H7_r)).
      rewrite land_compose by auto.
      f_equal. f_equal.

      destruct (bitop_and (i+8) is_op_8 is_lookup_8) as [H8_l [H8_r H8_res]].
      rewrite (plus_lor _ _ H8_l).
      rewrite (plus_lor _ _ H8_r).
      rewrite H8_res.
      rewrite (plus_lor _ _ (land_bound H8_l H8_r)).
      rewrite land_compose  by auto.
      f_equal. f_equal.
      
      destruct (bitop_and (i+9) is_op_9 is_lookup_9) as [H9_l [H9_r H9_res]].
      rewrite (plus_lor _ _ H9_l).
      rewrite (plus_lor _ _ H9_r).
      rewrite H9_res.
      rewrite (plus_lor _ _ (land_bound H9_l H9_r)).
      rewrite land_compose  by auto.
      f_equal. f_equal.

      destruct (bitop_and (i+10) is_op_10 is_lookup_10) as [H10_l [H10_r H10_res]].
      congruence.
    Qed.     
        
  End blockwise_bitop_and.

  Section blockwise_bitop_xor.
    Hypothesis op_is_Xor : OP = BitOp_Xor.
    
    Lemma bitop_xor : forall k,
        bit_table_values op k = OP ->
        bit_table_values lookup_sel k = 1 ->
            (0 <= (bit_table_values val_l k) < 256)
         /\ (0 <= (bit_table_values val_r k) < 256)
         /\ bit_table_values val_res k = Z.lxor (bit_table_values val_l k)
                                                (bit_table_values val_r k).
    Proof.
      intros k is_op is_lookup.
      eapply in_op_table_xor. 
      rewrite <- op_is_Xor.
      rewrite <- is_op.
      apply bit_table_lookup_op.
      rewrite is_lookup.
      auto.
    Qed.
    
    Lemma bitop_xor_spec :
      bit_table_values val_res i = Z.lxor (bit_table_values val_l i)
                                          (bit_table_values val_r i).
    Proof.
      rewrite l_0_spec.
      rewrite r_0_spec.
      rewrite res_0_spec by (rewrite op_is_Xor; unfold BitOp_Xor, Popcnt_index; lia).

      destruct (bitop_xor (i+2) is_op_2 is_lookup_2) as [H2_l [H2_r H2_res]].
      rewrite (plus_lor _ _ H2_l).
      rewrite (plus_lor _ _ H2_r).
      rewrite H2_res.
      rewrite (plus_lor _ _ (lxor_bound H2_l H2_r)).
      rewrite lxor_compose by auto.
      f_equal. f_equal.

      destruct (bitop_xor (i+3) is_op_3 is_lookup_3) as [H3_l [H3_r H3_res]].
      rewrite (plus_lor _ _ H3_l).
      rewrite (plus_lor _ _ H3_r).
      rewrite H3_res.
      rewrite (plus_lor _ _ (lxor_bound H3_l H3_r)).
      rewrite lxor_compose by auto.
      f_equal. f_equal.

      destruct (bitop_xor (i+4) is_op_4 is_lookup_4) as [H4_l [H4_r H4_res]].
      rewrite (plus_lor _ _ H4_l).
      rewrite (plus_lor _ _ H4_r).
      rewrite H4_res.
      rewrite (plus_lor _ _ (lxor_bound H4_l H4_r)).
      rewrite lxor_compose by auto.
      f_equal. f_equal.

      destruct (bitop_xor (i+5) is_op_5 is_lookup_5) as [H5_l [H5_r H5_res]].
      rewrite (plus_lor _ _ H5_l).
      rewrite (plus_lor _ _ H5_r).
      rewrite H5_res.
      rewrite (plus_lor _ _ (lxor_bound H5_l H5_r)).
      rewrite lxor_compose by auto.
      f_equal. f_equal.
      
      destruct (bitop_xor (i+7) is_op_7 is_lookup_7) as [H7_l [H7_r H7_res]].
      rewrite (plus_lor _ _ H7_l).
      rewrite (plus_lor _ _ H7_r).
      rewrite H7_res.
      rewrite (plus_lor _ _ (lxor_bound H7_l H7_r)).
      rewrite lxor_compose by auto.
      f_equal. f_equal.

      destruct (bitop_xor (i+8) is_op_8 is_lookup_8) as [H8_l [H8_r H8_res]].
      rewrite (plus_lor _ _ H8_l).
      rewrite (plus_lor _ _ H8_r).
      rewrite H8_res.
      rewrite (plus_lor _ _ (lxor_bound H8_l H8_r)).
      rewrite lxor_compose  by auto.
      f_equal. f_equal.
      
      destruct (bitop_xor (i+9) is_op_9 is_lookup_9) as [H9_l [H9_r H9_res]].
      rewrite (plus_lor _ _ H9_l).
      rewrite (plus_lor _ _ H9_r).
      rewrite H9_res.
      rewrite (plus_lor _ _ (lxor_bound H9_l H9_r)).
      rewrite lxor_compose  by auto.
      f_equal. f_equal.

      destruct (bitop_xor (i+10) is_op_10 is_lookup_10) as [H10_l [H10_r H10_res]].
      congruence.
    Qed.     
        
  End blockwise_bitop_xor.

  Section blockwise_bitop_or.
    Hypothesis op_is_Or : OP = BitOp_Or.
    
    Lemma bitop_or : forall k,
        bit_table_values op k = OP ->
        bit_table_values lookup_sel k = 1 ->
            (0 <= (bit_table_values val_l k) < 256)
         /\ (0 <= (bit_table_values val_r k) < 256)
         /\ bit_table_values val_res k = Z.lor (bit_table_values val_l k)
                                                (bit_table_values val_r k).
    Proof.
      intros k is_op is_lookup.
      eapply in_op_table_or. 
      rewrite <- op_is_Or.
      rewrite <- is_op.
      apply bit_table_lookup_op.
      rewrite is_lookup.
      auto.
    Qed.
    
    Lemma bitop_or_spec :
      bit_table_values val_res i = Z.lor (bit_table_values val_l i)
                                          (bit_table_values val_r i).
    Proof.
      rewrite l_0_spec.
      rewrite r_0_spec.
      rewrite res_0_spec by (rewrite op_is_Or; unfold BitOp_Or, Popcnt_index; lia).

      destruct (bitop_or (i+2) is_op_2 is_lookup_2) as [H2_l [H2_r H2_res]].
      rewrite (plus_lor _ _ H2_l).
      rewrite (plus_lor _ _ H2_r).
      rewrite H2_res.
      rewrite (plus_lor _ _ (lor_bound H2_l H2_r)).
      rewrite lor_compose by auto.
      f_equal. f_equal.

      destruct (bitop_or (i+3) is_op_3 is_lookup_3) as [H3_l [H3_r H3_res]].
      rewrite (plus_lor _ _ H3_l).
      rewrite (plus_lor _ _ H3_r).
      rewrite H3_res.
      rewrite (plus_lor _ _ (lor_bound H3_l H3_r)).
      rewrite lor_compose by auto.
      f_equal. f_equal.

      destruct (bitop_or (i+4) is_op_4 is_lookup_4) as [H4_l [H4_r H4_res]].
      rewrite (plus_lor _ _ H4_l).
      rewrite (plus_lor _ _ H4_r).
      rewrite H4_res.
      rewrite (plus_lor _ _ (lor_bound H4_l H4_r)).
      rewrite lor_compose by auto.
      f_equal. f_equal.

      destruct (bitop_or (i+5) is_op_5 is_lookup_5) as [H5_l [H5_r H5_res]].
      rewrite (plus_lor _ _ H5_l).
      rewrite (plus_lor _ _ H5_r).
      rewrite H5_res.
      rewrite (plus_lor _ _ (lor_bound H5_l H5_r)).
      rewrite lor_compose by auto.
      f_equal. f_equal.
      
      destruct (bitop_or (i+7) is_op_7 is_lookup_7) as [H7_l [H7_r H7_res]].
      rewrite (plus_lor _ _ H7_l).
      rewrite (plus_lor _ _ H7_r).
      rewrite H7_res.
      rewrite (plus_lor _ _ (lor_bound H7_l H7_r)).
      rewrite lor_compose by auto.
      f_equal. f_equal.

      destruct (bitop_or (i+8) is_op_8 is_lookup_8) as [H8_l [H8_r H8_res]].
      rewrite (plus_lor _ _ H8_l).
      rewrite (plus_lor _ _ H8_r).
      rewrite H8_res.
      rewrite (plus_lor _ _ (lor_bound H8_l H8_r)).
      rewrite lor_compose  by auto.
      f_equal. f_equal.
      
      destruct (bitop_or (i+9) is_op_9 is_lookup_9) as [H9_l [H9_r H9_res]].
      rewrite (plus_lor _ _ H9_l).
      rewrite (plus_lor _ _ H9_r).
      rewrite H9_res.
      rewrite (plus_lor _ _ (lor_bound H9_l H9_r)).
      rewrite lor_compose  by auto.
      f_equal. f_equal.

      destruct (bitop_or (i+10) is_op_10 is_lookup_10) as [H10_l [H10_r H10_res]].
      congruence.
    Qed.     
        
  End blockwise_bitop_or.
  
  Section blockwise_popcnt.

    Hypothesis op_is_popcnt : OP = Popcnt_index.

    Lemma is_popcnt_true : forall k,
        0 <= k ->
        bit_table_values u32_sel k = 1 ->
        bit_table_values op k = Popcnt_index ->
        bit_table_values helper k = 1.
    Proof.
      intros k Hrange Hop.
      assert (H:=bit_table_gate_1 k ltac:(lia)).
      destruct H as [_ [_ [H _]]].
      replace (k+0) with k in * by lia.
      rewrite <- !Z.mul_assoc in H. (* Need a circuit_mul_assoc lemma. *)
      apply circuit_if in H ; [ | simpl in *; lia].
      apply circuit_or in H; destruct H as [H|H].
      - intros.
        apply circuit_eq in H.
        auto.
      -  apply circuit_or in H; destruct H as [H|H].
         apply circuit_eq in H.
         intros.
         unfold BitOp_And, Popcnt_index in *. simpl in *; congruence.

         apply circuit_or in H; destruct H as [H|H].
         apply circuit_eq in H.
         intros.
         unfold BitOp_Or, Popcnt_index in *. simpl in *; congruence.

         apply circuit_eq in H.
         intros.
         unfold BitOp_Xor, Popcnt_index in *. simpl in *; congruence.
    Qed.         
        
    Lemma is_bit_1' : bit_table_values helper (i+1) = 1.
    Proof.
      apply is_popcnt_true; [lia| |]; autorewrite with bit_table; auto.
    Qed.
      
    Lemma is_bit_6' : bit_table_values helper (i+6) = 1.
    Proof.
      apply is_popcnt_true; [lia| |]; autorewrite with bit_table; auto.
    Qed.

    Lemma acc_res_0 :
      bit_table_values val_res i
      = bit_table_values val_res (i+1) + bit_table_values val_res (i+6).
    Proof.
      assert (H:=bit_table_gate_3 (i+1) ltac:(lia)).
      destruct H as [_ [_ [_ [H _]]]].
      unfold acc_u64_if_popcnt, is_popcnt in H.
      simpl in H.
      replace (i+1+ -1) with (i) in * by lia.
      autorewrite with bit_table in H.
      rewrite is_bit_1' in H.
      apply circuit_if in H; [|lia].
      lia.
    Qed.

    Lemma acc_res_1 : bit_table_values val_res (i+1) =
                          bit_table_values val_res (i+2) 
                          + bit_table_values val_res (i+3)
                          + bit_table_values val_res (i+4)
                          + bit_table_values val_res (i+5).
    Proof.
      intros.
      assert (H:= bit_table_gate_2 (i+1) ltac:(lia)).
      destruct H as [_ [_ [_ [H _]]]].
      unfold acc_u32_if_popcnt, acc_u32_helper, is_popcnt in H.
      simpl in H.
      autorewrite with bit_table in H.
      rewrite is_bit_1' in H.
      lia.  
    Qed.
      
    Lemma acc_res_6 : bit_table_values val_res (i+6) =
                         bit_table_values val_res (i+7) 
                          + bit_table_values val_res (i+8)
                          + bit_table_values val_res (i+9)
                          + bit_table_values val_res (i+10).
    Proof.
      intros.
      assert (H:= bit_table_gate_2 (i+6) ltac:(lia)).
      destruct H as [_ [_ [_ [H _]]]].
      unfold acc_u32_if_popcnt, acc_u32_helper, is_popcnt in H.
      simpl in H.
      autorewrite with bit_table in H.
      rewrite is_bit_6' in H.
      lia.
    Qed.

    Lemma bitop_popcnt : forall k,
        bit_table_values op k = OP ->
        bit_table_values lookup_sel k = 1 ->
        (0 <= (bit_table_values val_l k) < 256)
        /\  (bit_table_values val_r k) = 0          
        /\ bit_table_values val_res k = popcnt (bit_table_values val_l k).
    Proof.
      intros k is_op is_lookup.
      eapply in_op_table_popcnt.
      rewrite <- op_is_popcnt.
      rewrite <- is_op.
      apply bit_table_lookup_op.
      rewrite is_lookup.
      auto.
    Qed.

    Lemma shift_bound : forall a b n,
        0 <= a < 256 ->
        0 <= b < 2^n ->
        0 <= a + Z.shiftl b 8 < 2^(n+8).
    Proof.
      intros.
      rewrite Z.add_comm.
      replace (n+8) with (8+n) by lia.
      apply InjectivityHelper.shift_plus_bound.
      - assumption.
      - change (2^8) with 256.
        assumption.
    Qed.
      
    Lemma bitop_popcnt_spec :
      bit_table_values val_res i = popcnt (bit_table_values val_l i).
    Proof.
      rewrite l_0_spec.

      rewrite acc_res_0, acc_res_1, acc_res_6.
      rewrite <- !Z.add_assoc.
      
      destruct (bitop_popcnt (i+2) is_op_2 is_lookup_2) as [H2_l [_ H2_res]].
      destruct (bitop_popcnt (i+3) is_op_3 is_lookup_3) as [H3_l [_ H3_res]].
      destruct (bitop_popcnt (i+4) is_op_4 is_lookup_4) as [H4_l [_ H4_res]].
      destruct (bitop_popcnt (i+5) is_op_5 is_lookup_5) as [H5_l [_ H5_res]].
      destruct (bitop_popcnt (i+7) is_op_7 is_lookup_7) as [H7_l [_ H7_res]].
      destruct (bitop_popcnt (i+8) is_op_8 is_lookup_8) as [H8_l [_ H8_res]].
      destruct (bitop_popcnt (i+9) is_op_9 is_lookup_9) as [H9_l [_ H9_res]].
      destruct (bitop_popcnt (i+10) is_op_10 is_lookup_10) as [H10_l [_ H10_res]].

      assert (bound6 :  0 <= bit_table_values val_l (i + 9) + Z.shiftl (bit_table_values val_l (i + 10)) 8 < 2 ^ (8+8)).
      {
        apply shift_bound; auto.
      }
      
      assert (bound5 :  0 <=
  bit_table_values val_l (i + 8) +
  Z.shiftl (bit_table_values val_l (i + 9) + Z.shiftl (bit_table_values val_l (i + 10)) 8) 8 < 
                          2 ^ (16+8)).
      {
        apply shift_bound; [auto | exact bound6].
      }
      
      assert (bound4 :   0 <=
  bit_table_values val_l (i + 7) +
  Z.shiftl
    (bit_table_values val_l (i + 8) +
     Z.shiftl (bit_table_values val_l (i + 9) + Z.shiftl (bit_table_values val_l (i + 10)) 8) 8) 8 <
  2 ^ (24 + 8)).
      { apply shift_bound; [auto | exact bound5]. }
      
      assert (bound3 :   0 <=
  bit_table_values val_l (i + 5) +
  Z.shiftl
    (bit_table_values val_l (i + 7) +
     Z.shiftl
       (bit_table_values val_l (i + 8) +
        Z.shiftl (bit_table_values val_l (i + 9) + Z.shiftl (bit_table_values val_l (i + 10)) 8) 8) 8)
    8 < 2 ^ (32+8)).
      { apply shift_bound; [auto | exact bound4]. }
      
      assert (bound2 :   0 <=
  bit_table_values val_l (i + 4) +
  Z.shiftl
    (bit_table_values val_l (i + 5) +
     Z.shiftl
       (bit_table_values val_l (i + 7) +
        Z.shiftl
          (bit_table_values val_l (i + 8) +
           Z.shiftl (bit_table_values val_l (i + 9) + Z.shiftl (bit_table_values val_l (i + 10)) 8) 8)
          8) 8) 8 < 2 ^ (40+8)).
      { apply shift_bound ; [auto | exact bound3]. }
      
      assert (bound1 :
                0 <=
 bit_table_values val_l (i + 3) +
 Z.shiftl
   (bit_table_values val_l (i + 4) +
    Z.shiftl
      (bit_table_values val_l (i + 5) +
       Z.shiftl
         (bit_table_values val_l (i + 7) +
          Z.shiftl
            (bit_table_values val_l (i + 8) +
             Z.shiftl (bit_table_values val_l (i + 9) + Z.shiftl (bit_table_values val_l (i + 10)) 8)
               8) 8) 8) 8) 8 < 2 ^ (48+8)).
      { apply shift_bound; [auto| exact bound2]. }

      
      rewrite (plus_lor _ _ H2_l).
      rewrite H2_res.
      rewrite popcnt_compose by auto.
      f_equal.

      rewrite (plus_lor _ _ H3_l).
      rewrite H3_res.
      rewrite popcnt_compose by (auto; lia).
      f_equal.

      rewrite (plus_lor _ _ H4_l).
      rewrite H4_res.
      rewrite popcnt_compose by (auto; lia).
      f_equal.
      
      rewrite (plus_lor _ _ H5_l).
      rewrite H5_res.
      rewrite popcnt_compose by (auto; lia).
      f_equal.

      rewrite (plus_lor _ _ H7_l).
      rewrite H7_res.
      rewrite popcnt_compose by (auto; lia).
      f_equal.

      rewrite (plus_lor _ _ H8_l).
      rewrite H8_res.
      rewrite popcnt_compose by (auto; lia).
      f_equal.

      rewrite (plus_lor _ _ H9_l).
      rewrite H9_res.
      rewrite popcnt_compose by (auto; lia).
      f_equal.

      auto.
    Qed.     
  End blockwise_popcnt.

End blockwise.

Require Import Wasm.numerics.

(** The bit_table is correct for the And operation. *)
Theorem in_bit_table_and : 
 forall (i : Z) w_l w_r,
       0 <= i ->
       value bit_table block_sel (i + 1) = 1 ->
       value bit_table op i = BitOp_And ->
       value bit_table val_l i   = Wasm_int.Z_of_uint i64m w_l ->
       value bit_table val_r i   = Wasm_int.Z_of_uint i64m w_r ->
       value bit_table val_res i = Wasm_int.Z_of_uint i64m (Wasm_int.int_and i64m w_l w_r).
Proof.
  simpl.
  intros i w_l w_r i_bound Hsel Hop Hl Hr.
  destruct w_l as [l_val l_range].
  destruct w_r as [r_val r_range].
  unfold  Wasm_int.Int64.iand, Wasm_int.Int64.and.  
  simpl in *.
  
  rewrite bitop_and_spec by auto.
  rewrite Hl, Hr in *. clear Hsel Hop Hl Hr i i_bound.
  rewrite Wasm_int.Int64.Z_mod_modulus_id.
  - congruence.
  - eapply land_bound64; auto.
Qed.

(** The bit_table is correct for the Xor operation. *)
Theorem in_bit_table_xor : 
 forall (i : Z) w_l w_r,
       0 <= i ->
       value bit_table block_sel (i + 1) = 1 ->
       value bit_table op i = BitOp_Xor ->
       value bit_table val_l i   = Wasm_int.Z_of_uint i64m w_l ->
       value bit_table val_r i   = Wasm_int.Z_of_uint i64m w_r ->
       value bit_table val_res i = Wasm_int.Z_of_uint i64m (Wasm_int.int_xor i64m w_l w_r).
Proof.
  simpl.
  intros i w_l w_r i_bound Hsel Hop Hl Hr.
  destruct w_l as [l_val l_range].
  destruct w_r as [r_val r_range].
  unfold  Wasm_int.Int64.ixor, Wasm_int.Int64.xor.
  simpl in *.
  
  rewrite bitop_xor_spec by auto.
  rewrite Hl, Hr in *. clear Hsel Hop Hl Hr i i_bound.
  rewrite Wasm_int.Int64.Z_mod_modulus_id.
  - congruence.
  - eapply lxor_bound64; auto.
Qed.

(** The bit_table is correct for the Or operation. *)
Theorem in_bit_table_or : 
 forall (i : Z) w_l w_r,
       0 <= i ->
       value bit_table block_sel (i + 1) = 1 ->
       value bit_table op i = BitOp_Or ->
       value bit_table val_l i   = Wasm_int.Z_of_uint i64m w_l ->
       value bit_table val_r i   = Wasm_int.Z_of_uint i64m w_r ->
       value bit_table val_res i = Wasm_int.Z_of_uint i64m (Wasm_int.int_or i64m w_l w_r).
Proof.
  simpl.
  intros i w_l w_r i_bound Hsel Hop Hl Hr.
  destruct w_l as [l_val l_range].
  destruct w_r as [r_val r_range].
  unfold  Wasm_int.Int64.ior, Wasm_int.Int64.or.
  simpl in *.
  
  rewrite bitop_or_spec by auto.
  rewrite Hl, Hr in *. clear Hsel Hop Hl Hr i i_bound.
  rewrite Wasm_int.Int64.Z_mod_modulus_id.
  - congruence.
  - eapply lor_bound64; auto.
Qed.
  
(** The bit_table is correct for the Popcnt operation. *)
Theorem in_bit_table_popcnt : 
    forall (i : Z) w_l,
        0 <= i ->
        value bit_table block_sel (i + 1) = 1 ->
        value bit_table op i = Popcnt_index ->
        value bit_table val_l i   = Wasm_int.Z_of_uint i64m w_l ->
        value bit_table val_r i = 0 ->
        value bit_table val_res i = Wasm_int.Z_of_uint i64m (Wasm_int.int_popcnt i64m w_l).
Proof.
Opaque  Wasm_int.Int64.wordsize Wasm_int.Z_of_uint. 
  simpl.
  intros i w_l i_bound Hsel Hop Hl Hr.
  rewrite bitop_popcnt_spec by auto.
  rewrite Hl.
  clear Hsel Hop Hl Hr i i_bound.
  apply popcnt_commutes_with_uint.
Qed.
