(* Copyright (C) CertiK 2024-2026 *)

Require Import List.
Require Import ZArith.
Require Import Wasm.numerics.


Require Import ETableModel.
Require Import Relation.


Open Scope Z_scope.

  

Inductive steps : WasmState -> WasmState -> Prop :=
| steps_refl : forall st,  steps st st
| steps_step : forall st1 st2 st3, 
    steps st1 st2 ->
    step  st2 st3 ->
    steps st1 st3.

Inductive steps_list : WasmState -> list WasmState -> WasmState -> Prop :=
| steps_list_refl : forall st,  steps_list st (nil) st
| steps_list_step : forall sts st1 st2 st3, 
    step st1 st2 ->
    steps_list st2 sts st3 ->
    steps_list st1 (st1::sts) st3.

Lemma steps_cons : forall st1 st2 st3,
    step st1 st2 ->
    steps st2 st3 ->
    steps st1 st3.
Proof.
  induction 2.
  -  eauto using steps_step, steps_refl.
  - specialize (IHsteps H).
    eauto using steps_step.
Qed.

Lemma steps_list_steps : forall st1 sts st2,
    steps_list st1 sts st2 -> steps st1 st2.
Proof.
  induction 1.
  - apply steps_refl.
  - eauto using steps_cons.
Qed.

Definition valid_state (st : WasmState) : Prop :=
  match (program (wasm_pc st)) with
  | IBinShift _ _ => exists xr xl xs,
      wasm_stack st = xr::xl::xs
  | IBin _ _ => exists xr xl xs,
      wasm_stack st = xr::xl::xs
  | IBrIf false drop dst_pc => exists xcond xd xs,
      wasm_stack st = xcond :: xd ++ xs
      /\ length xd = Z.to_nat (Wasm_int.Int32.unsigned drop)
  | IBrIf true drop dst_pc => exists xcond xv xd xs,
      wasm_stack st = xcond :: xv :: xd ++ xs
      /\ length xd = Z.to_nat (Wasm_int.Int32.unsigned drop)
  | IBrIfEqz false drop dst_pc => exists xcond xd xs,
      wasm_stack st = xcond :: xd ++ xs
      /\ length xd = Z.to_nat (Wasm_int.Int32.unsigned drop)
  | IBrIfEqz true drop dst_pc => exists xcond xv xd xs,
      wasm_stack st = xcond :: xv :: xd ++ xs
      /\ length xd = Z.to_nat (Wasm_int.Int32.unsigned drop)
  | IBr false drop dst_pc => exists xd xs,
      wasm_stack st = xd ++ xs
      /\ length xd = Z.to_nat (Wasm_int.Int32.unsigned drop)
  | IBr true drop dst_pc => exists xv xd xs,
      wasm_stack st = xv :: xd ++ xs
      /\ length xd = Z.to_nat (Wasm_int.Int32.unsigned drop)
  | IConversion _signed _is32 VAL64 RES32  => exists x1 xs,
    wasm_stack st = Wasm_int.Z_of_uint i64m x1:: xs
  | IConversion _signed _is32 _ _   => exists x1 xs,
    wasm_stack st = Wasm_int.Z_of_sint i32m x1:: xs                               
  | IDrop => exists x xs, (wasm_stack st) = x :: xs
  | IGlobalSet idx =>
      exists x xs,
        wasm_stack st = (x::xs) /\ 0 <= x < Wasm_int.Int64.modulus
  | ILocalGet is32 offset =>
      exists y, 
      Wasm_int.Int32.unsigned offset > 1
      /\ nth_error (wasm_stack st) (Z.to_nat (Wasm_int.Int32.unsigned offset - 1)) = Some y
  | ILocalSet is32 offset =>
      Wasm_int.Int32.unsigned offset > 1
      /\       exists y ys x xs,
        (wasm_stack st) = y :: ys ++ x :: xs
        /\ length ys =  (Z.to_nat (Wasm_int.Int32.unsigned offset) - 1) %nat
  | ILocalTee is32 offset =>
      Wasm_int.Int32.unsigned offset > 1
      /\       exists y ys x xs,
        (wasm_stack st) = y :: ys ++ x :: xs
        /\ length ys =  (Z.to_nat (Wasm_int.Int32.unsigned offset) - 2) %nat
                                                                        
  | IRel true _ => exists x1 x2 xs,
          wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs)

  | IRel false _ => exists x1 x2 xs,
          wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs)

  | IReturn false drop =>
    exists xs ys,
        wasm_stack st = xs++ys /\ Wasm_int.Int32.unsigned drop  = Z.of_nat (length xs)
  | IReturn true drop =>
    exists x xs ys,
      wasm_stack st = x::xs++ys /\ Wasm_int.Int32.unsigned drop  = Z.of_nat (length xs)
  | ISelect =>
      exists xcond x1 x2 xs,
      wasm_stack st = xcond::x1::x2::xs                       
  | ITest _ =>
    exists x xs,
      wasm_stack st = x::xs
  | IUnary true CTZ =>
      exists x1 xs,
      wasm_stack st = Wasm_int.Z_of_uint i32m x1:: xs
  | IUnary _ _ =>
      exists x1 xs,
    wasm_stack st = Wasm_int.Z_of_uint i64m x1:: xs
  | IMemoryGrow =>
      exists x1 xs,
      wasm_stack st = x1:: xs
  | IStore _ _ _ =>
      exists v base xs,
          wasm_stack st = (v::base::xs)
  | ILoad _ _ _ _ =>
      exists base xs,
          wasm_stack st = (base::xs)
  | IBinBit _ _ =>
      exists x1 x2 xs,
      wasm_stack st = (Wasm_int.Z_of_uint i64m x1:: Wasm_int.Z_of_uint i64m x2::xs)
  | IBrTable _ =>
      forall entries idx e,
          br_tables (wasm_pc st) = Some entries ->
          nth_error entries idx = Some e ->
          if (br_table_keep e)
          then
            exists xid xv xd xs,
              wasm_stack st = xid :: xv :: xd ++ xs
              /\ length xd = Z.to_nat (Wasm_int.Int32.unsigned (br_table_drop e))
          else
            exists xid xd xs,
              wasm_stack st = xid :: xd ++ xs
              /\ length xd = Z.to_nat (Wasm_int.Int32.unsigned (br_table_drop e))
  | ICallIndirect _ =>
    exists x xs, wasm_stack st = x::xs
  | _ => True
  end.

Require Import ZArith.
Require Import Lia.
Require Import ETableModel.
Require Import ETable.

Require Import InjectivityHelper.

Open Scope Z_scope.

Require OpBin OpBinBit OpBinShift OpBr OpBrIf OpBrIfEqz OpBrTable OpCall OpCallIndirect
OpConst OpConversion OpDrop OpGlobalGet OpGlobalSet OpLoad OpLoadHelper
OpLocalGet OpLocalSet OpLocalTee OpMemoryGrow OpMemorySize OpRel OpReturn
OpSelect OpStore OpTest OpUnary.

Axiom opcode_mops_correct_call_host : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct CallHost i.

Lemma all_opcode_mops_correct : forall c i,
    0 <= i ->
    etable_values enabled_cell i = 1 ->
    opcode_mops_correct c i.
Proof.
  intros c i Hrange Henabled.
  assert (Heid_nonzero := eid_nonzero i Hrange Henabled).
  destruct c.
  - eapply OpBinShift.opcode_mops_correct_bin_shift; auto.
  - eapply OpBin.opcode_mops_correct_bin; auto.
  - eapply OpBrIfEqz.opcode_mops_correct_br_if_eqz; auto.
  - eapply OpBrIf.opcode_mops_correct_br_if; auto.  
  - eapply OpBr.opcode_mops_correct_br; auto.
  - eapply OpCall.opcode_mops_correct_call; auto.
  - eapply opcode_mops_correct_call_host; auto.
  - eapply OpConst.opcode_mops_correct_const; auto.    
  - eapply OpConversion.opcode_mops_correct_conversion; auto. 
  - eapply OpDrop.opcode_mops_correct_drop; auto. 
  - eapply OpGlobalGet.opcode_mops_correct_global_get; auto. 
  - eapply OpGlobalSet.opcode_mops_correct_global_set; auto.
  - eapply OpLocalGet.opcode_mops_correct_local_get; auto. 
  - eapply OpLocalSet.opcode_mops_correct_local_set; auto.
  - eapply OpLocalTee.opcode_mops_correct_local_tee; auto.
  - eapply OpRel.opcode_mops_correct_rel; auto.
  - eapply OpReturn.opcode_mops_correct_return; auto.
  - eapply OpSelect.opcode_mops_correct_select; auto.
  - eapply OpTest.opcode_mops_correct_test; auto.
  - eapply OpUnary.opcode_mops_correct_unary; auto.
  - eapply OpLoad.opcode_mops_correct_load; auto.
  - eapply OpStore.opcode_mops_correct_store; auto.
  - eapply OpBinBit.opcode_mops_correct_bin_bit; auto.
  - eapply OpMemorySize.opcode_mops_correct_memory_size; auto.
  - eapply OpMemoryGrow.opcode_mops_correct_memory_grow; auto.
  - eapply OpBrTable.opcode_mops_correct_br_table; auto.
  - eapply OpCallIndirect.opcode_mops_correct_callindirect; auto.
Qed.

Opaque Wasm_int.Int32.unsigned.


Definition next_state (i: Z) (st: WasmState) : WasmState :=
  match (class_of_row i) with
    BinShift =>
      let xr := nth (0%nat) (wasm_stack st) 0 in
      let xl := nth (1%nat) (wasm_stack st) 0 in
      let xs := skipn (2%nat) (wasm_stack st) in
      match  (OpBinShift.BinShift_op i) with
      | SHL =>
          update_stack (incr_iid st) (shl xl xr (64 - etable_values op_bin_shift_is_i32 i * 32) :: xs)
      | SHR_u =>
          update_stack (incr_iid st) (shr_u xl xr (64 - etable_values op_bin_shift_is_i32 i * 32) :: xs)
      | SHR_s =>
            update_stack (incr_iid st)
              (shr_s xl xr (64 - etable_values op_bin_shift_is_i32 i * 32) :: xs)
      | ROTL =>
           update_stack (incr_iid st) (rotl xl xr (64 - etable_values op_bin_shift_is_i32 i * 32) :: xs)
      | ROTR =>
          update_stack (incr_iid st) (rotr xl xr (64 - etable_values op_bin_shift_is_i32 i * 32) :: xs)
      end
  | Bin =>
      let xr := nth (0%nat) (wasm_stack st) 0 in
      let xl := nth (1%nat) (wasm_stack st) 0 in
      let xs := skipn (2%nat) (wasm_stack st) in
      match (OpBin.Bin_op i) with
      | ADD   => update_stack (incr_iid st) ((xl + xr) mod 2 ^ (64 - etable_values op_bin_is_i32 i * 32) :: xs)
      | SUB   => update_stack (incr_iid st) ((xl - xr) mod 2 ^ (64 - etable_values op_bin_is_i32 i * 32) :: xs)
      | MUL   => update_stack (incr_iid st) ((xl * xr) mod 2 ^ (64 - etable_values op_bin_is_i32 i * 32) :: xs)
      | DIV_u => update_stack (incr_iid st) ((xl / xr) :: xs)
      | REM_u => update_stack (incr_iid st) ((xl mod xr) :: xs)
      | DIV_s => update_stack (incr_iid st) (div_s xl xr (64 - etable_values op_bin_is_i32 i * 32) :: xs)
      | REM_s => update_stack (incr_iid st) (rem_s xl xr (64 - etable_values op_bin_is_i32 i * 32) :: xs)
      end
  | BrIfEqz =>
      if bool_of_Z (etable_values op_br_if_eqz_keep_cell i)
      then
        let xcond := nth (0%nat) (wasm_stack st) 0 in
        let xv := nth (1%nat) (wasm_stack st) 0 in
        let xs := skipn (2%nat + Z.to_nat
                (Wasm_int.Int32.unsigned
                   (Wasm_int.Int32.repr (etable_values op_br_if_eqz_drop_cell i))) ) (wasm_stack st) in
        if (Z.eq_dec xcond 0)
        then
          update_stack (move_to_iid st (etable_values op_br_if_eqz_dst_pc_cell i)) (xv::xs)
        else update_stack (incr_iid st) (skipn (1%nat) (wasm_stack st))
      else
        let xcond := nth (0%nat) (wasm_stack st) 0 in
        let xv := nth (1%nat) (wasm_stack st) 0 in
        let xs := skipn (1%nat + Z.to_nat
                (Wasm_int.Int32.unsigned
                   (Wasm_int.Int32.repr (etable_values op_br_if_eqz_drop_cell i))) ) (wasm_stack st) in
        if (Z.eq_dec xcond 0)
        then
          update_stack (move_to_iid st (etable_values op_br_if_eqz_dst_pc_cell i)) xs
        else
          update_stack (incr_iid st) (skipn (1%nat) (wasm_stack st))
  | BrIf => 
      if bool_of_Z (etable_values op_br_if_keep_cell i)
      then
        let xcond := nth (0%nat) (wasm_stack st) 0 in
        let xv := nth (1%nat) (wasm_stack st) 0 in
        let xs := skipn (2%nat + Z.to_nat
                (Wasm_int.Int32.unsigned
                   (Wasm_int.Int32.repr (etable_values op_br_if_drop_cell i))) ) (wasm_stack st) in
        if (Z.eq_dec xcond 0)
        then
          update_stack (incr_iid st) (skipn (1%nat) (wasm_stack st))
        else
          update_stack (move_to_iid st (etable_values op_br_if_dst_pc_cell i)) (xv::xs)
      else
        let xcond := nth (0%nat) (wasm_stack st) 0 in
        let xv := nth (1%nat) (wasm_stack st) 0 in
        let xs := skipn (1%nat + Z.to_nat
                (Wasm_int.Int32.unsigned
                   (Wasm_int.Int32.repr (etable_values op_br_if_drop_cell i))) ) (wasm_stack st) in
        if (Z.eq_dec xcond 0)
        then
          update_stack (incr_iid st) (skipn (1%nat) (wasm_stack st))
        else
          update_stack (move_to_iid st (etable_values op_br_if_dst_pc_cell i)) xs
  | Br => 
      if bool_of_Z (etable_values op_br_keep_cell i)
      then
        let xv := nth (0%nat) (wasm_stack st) 0 in
        let xs := skipn (1%nat + Z.to_nat
                (Wasm_int.Int32.unsigned
                   (Wasm_int.Int32.repr (etable_values op_br_drop_cell i))) ) (wasm_stack st) in
          update_stack (move_to_iid st (etable_values op_br_dst_pc_cell i)) (xv::xs)
      else
        let xv := nth (0%nat) (wasm_stack st) 0 in
        let xs := skipn (Z.to_nat
                (Wasm_int.Int32.unsigned
                   (Wasm_int.Int32.repr (etable_values op_br_drop_cell i))) ) (wasm_stack st) in
          update_stack (move_to_iid st (etable_values op_br_dst_pc_cell i)) xs
  | Call =>   update_callstack (move_to_label st (etable_values op_call_index i, 0))
    ((fst (wasm_pc st), snd (wasm_pc st) + 1) :: wasm_callstack st) 
  | CallHost => st
  | Const =>  update_stack (incr_iid st) (etable_values op_const_value i :: wasm_stack st)
  | Conversion =>
      let srctyp := OpConversion.OpConversion_value_type i in
      let restyp := OpConversion.OpConversion_result_type i in
      match srctyp,restyp with
      | VAL64, RES32 =>
          let x1 := Wasm_int.int_of_Z i64m (nth (0%nat) (wasm_stack st) 0) in
          let xs := skipn (1%nat) (wasm_stack st) in
          update_stack (incr_iid st) (Wasm_int.Z_of_uint i32m (wasm_wrap x1):: xs)
      | _,_ =>
          let x1 := Wasm_int.int_of_Z i32m (nth (0%nat) (wasm_stack st) 0) in
          let xs := skipn (1%nat) (wasm_stack st) in
          let signed := bool_of_Z (etable_values op_conversion_sign_op i) in
          update_stack (incr_iid st)
                 (sign_extend signed srctyp restyp ((Wasm_int.Z_of_sint i32m x1) mod (value_type_modulus srctyp)) :: xs)
      end                    
  | Drop =>
      let xs := skipn 1%nat (wasm_stack st) in
      update_stack (incr_iid st) xs
  | GlobalGet =>
      update_stack (incr_iid st) (etable_values op_global_get_value_u64_cell i :: wasm_stack st)
  | GlobalSet =>
      let x   := nth 0%nat (wasm_stack st) 0 in
      let xs  := skipn 1%nat (wasm_stack st) in
      let idx := Z.to_nat (etable_values op_global_set_idx_cell i) in
      let v   := Wasm.datatypes.VAL_int64 (Wasm_int.Int64.repr  x) in
      match set_glob (wasm_globals st) idx v with
      | Some glbs' => update_globals (update_stack (incr_iid st) xs) glbs'
      | None => st
      end
  | LocalGet =>
      let y := nth (Z.to_nat (etable_values op_local_get_offset_cell i - 1)) (wasm_stack st) 0 in
      update_stack (incr_iid st) (y :: wasm_stack st)
  | LocalSet =>
      let y    := nth 0%nat (wasm_stack st) 0 in
      let off1 := (Z.to_nat (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr
                     (etable_values op_local_set_offset_cell i))) - 1)%nat in
      let ys   := firstn off1 (skipn 1%nat (wasm_stack st)) in
      let xs   := skipn (off1 + 1) (skipn 1%nat (wasm_stack st)) in
      update_stack (incr_iid st) (ys ++ y :: xs)
  | LocalTee =>
      let y    := nth 0%nat (wasm_stack st) 0 in
      let off1 := (Z.to_nat (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr
                     (etable_values op_local_tee_offset_cell i))) - 2)%nat in
      let ys   := firstn off1 (skipn 1%nat (wasm_stack st)) in
      let xs   := skipn (off1 + 1) (skipn 1%nat (wasm_stack st)) in
      update_stack (incr_iid st) (y :: ys ++ y :: xs)
  | Rel =>
      let x1 := nth (0%nat) (wasm_stack st) 0 in
      let x2 := nth (1%nat) (wasm_stack st) 0 in
      let xs := skipn (2%nat) (wasm_stack st) in
      match  (OpRel.Rel_op i) with
      | EQ  => if Z.eq_dec (etable_values op_rel_is_i32 i) 1
               then update_stack (incr_iid st) (Z_of_bool     (Wasm_int.int_eq  i32m (Wasm_int.int_of_Z i32m x2) (Wasm_int.int_of_Z i32m x1)) :: xs)
               else update_stack (incr_iid st) (Z_of_bool     (Wasm_int.int_eq  i64m (Wasm_int.int_of_Z i64m x2) (Wasm_int.int_of_Z i64m x1)) :: xs)
      | NEQ => if Z.eq_dec (etable_values op_rel_is_i32 i) 1
               then update_stack (incr_iid st) (Z_of_bool_opp (Wasm_int.int_eq  i32m (Wasm_int.int_of_Z i32m x2) (Wasm_int.int_of_Z i32m x1)) :: xs)
               else update_stack (incr_iid st) (Z_of_bool_opp (Wasm_int.int_eq  i64m (Wasm_int.int_of_Z i64m x2) (Wasm_int.int_of_Z i64m x1)) :: xs)
      | GT_s => if Z.eq_dec (etable_values op_rel_is_i32 i) 1
               then update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_gt_s i32m (Wasm_int.int_of_Z i32m x2) (Wasm_int.int_of_Z i32m x1)) :: xs)
               else update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_gt_s i64m (Wasm_int.int_of_Z i64m x2) (Wasm_int.int_of_Z i64m x1)) :: xs)
      | GT_u => if Z.eq_dec (etable_values op_rel_is_i32 i) 1
               then update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_gt_u i32m (Wasm_int.int_of_Z i32m x2) (Wasm_int.int_of_Z i32m x1)) :: xs)
               else update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_gt_u i64m (Wasm_int.int_of_Z i64m x2) (Wasm_int.int_of_Z i64m x1)) :: xs)
      | GE_s => if Z.eq_dec (etable_values op_rel_is_i32 i) 1
               then update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_ge_s i32m (Wasm_int.int_of_Z i32m x2) (Wasm_int.int_of_Z i32m x1)) :: xs)
               else update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_ge_s i64m (Wasm_int.int_of_Z i64m x2) (Wasm_int.int_of_Z i64m x1)) :: xs)
      | GE_u => if Z.eq_dec (etable_values op_rel_is_i32 i) 1
               then update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_ge_u i32m (Wasm_int.int_of_Z i32m x2) (Wasm_int.int_of_Z i32m x1)) :: xs)
               else update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_ge_u i64m (Wasm_int.int_of_Z i64m x2) (Wasm_int.int_of_Z i64m x1)) :: xs)
      | LT_s => if Z.eq_dec (etable_values op_rel_is_i32 i) 1
               then update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_lt_s i32m (Wasm_int.int_of_Z i32m x2) (Wasm_int.int_of_Z i32m x1)) :: xs)
               else update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_lt_s i64m (Wasm_int.int_of_Z i64m x2) (Wasm_int.int_of_Z i64m x1)) :: xs)
      | LT_u => if Z.eq_dec (etable_values op_rel_is_i32 i) 1
               then update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_lt_u i32m (Wasm_int.int_of_Z i32m x2) (Wasm_int.int_of_Z i32m x1)) :: xs)
               else update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_lt_u i64m (Wasm_int.int_of_Z i64m x2) (Wasm_int.int_of_Z i64m x1)) :: xs)
      | LE_s => if Z.eq_dec (etable_values op_rel_is_i32 i) 1
               then update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_le_s i32m (Wasm_int.int_of_Z i32m x2) (Wasm_int.int_of_Z i32m x1)) :: xs)
               else update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_le_s i64m (Wasm_int.int_of_Z i64m x2) (Wasm_int.int_of_Z i64m x1)) :: xs)
      | LE_u => if Z.eq_dec (etable_values op_rel_is_i32 i) 1
               then update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_le_u i32m (Wasm_int.int_of_Z i32m x2) (Wasm_int.int_of_Z i32m x1)) :: xs)
               else update_stack (incr_iid st) (Z_of_bool    (Wasm_int.int_le_u i64m (Wasm_int.int_of_Z i64m x2) (Wasm_int.int_of_Z i64m x1)) :: xs)
      end
  | Return =>
      let keep := etable_values op_return_keep i in
      let drop := Z.to_nat (etable_values op_return_drop i) in
      let lbl  := hd (0, 0) (wasm_callstack st) in
      let cs'  := tl (wasm_callstack st) in
      if Z.eq_dec keep 0 then
        let ys := skipn drop (wasm_stack st) in
        update_callstack (update_stack (move_to_label st lbl) ys) cs'
      else
        let x  := nth 0%nat (wasm_stack st) 0 in
        let ys := skipn (drop + 1) (wasm_stack st) in
        update_callstack (update_stack (move_to_label st lbl) (x :: ys)) cs'
  | Select =>
      let xcond := nth 0%nat (wasm_stack st) 0 in
      let x1    := nth 1%nat (wasm_stack st) 0 in
      let x2    := nth 2%nat (wasm_stack st) 0 in
      let xs    := skipn 3%nat (wasm_stack st) in
      update_stack (incr_iid st) (select xcond x1 x2 :: xs)
  | Test =>
      let x1 := nth 0%nat (wasm_stack st) 0 in
      let xs := skipn 1%nat (wasm_stack st) in
      update_stack (incr_iid st) (test x1 :: xs)
  | Unary =>
      let x1 := nth (0%nat) (wasm_stack st) 0 in
      let xs := skipn (1%nat) (wasm_stack st) in
      match (OpUnary.Unary_op i) with
      | CTZ =>
        (if (Z.eq_dec (etable_values op_unary_is_i32 i) 1)
              then 
                update_stack (incr_iid st) ((Wasm_int.Z_of_uint i32m (Wasm_int.int_ctz i32m ( (Wasm_int.int_of_Z i32m x1)))) :: xs)
            else
                update_stack (incr_iid st) ((Wasm_int.Z_of_uint i64m (Wasm_int.int_ctz i64m ( (Wasm_int.int_of_Z i64m x1)))) :: xs))
      | CLZ =>
          update_stack (incr_iid st) ((Wasm_int.Z_of_uint i64m (Wasm_int.int_clz i64m ((Wasm_int.int_of_Z i64m x1))))  - etable_values op_unary_is_i32 i * 32  :: xs) 
      | POPCNT => update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_popcnt i64m (Wasm_int.int_of_Z i64m  x1)) :: xs)
      end
  | Load =>
      let xs := skipn 1%nat (wasm_stack st) in
      update_stack (incr_iid st) (etable_values op_load_res i :: xs)
  | Store =>
      let v    := nth 0%nat (wasm_stack st) 0 in
      let base := nth 1%nat (wasm_stack st) 0 in
      let xs   := skipn 2%nat (wasm_stack st) in
      match Wasm.operations.store (wasm_memory st)
        (Z.to_N base)
        (Z.to_N (etable_values op_store_opcode_store_offset i))
        (Memdata.encode_int (Z.to_nat (etable_values op_store_len i)) v)
        (Z.to_nat (etable_values op_store_len i)) with
      | Some new_mem => update_memory (update_stack (incr_iid st) xs) new_mem
      | None => st
      end
  | BinBit =>
      let x1 := nth (0%nat) (wasm_stack st) 0 in
      let x2 := nth (1%nat) (wasm_stack st) 0 in
      let xs := skipn (2%nat) (wasm_stack st) in
      match  (OpBinBit.BinBit_op i) with
      | AND =>
  update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_and i64m (Wasm_int.int_of_Z i64m x2) (Wasm_int.int_of_Z i64m x1)) :: xs)
      | OR =>
  update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_or i64m (Wasm_int.int_of_Z i64m x2) (Wasm_int.int_of_Z i64m x1)) :: xs)
      | XOR =>
  update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_xor i64m (Wasm_int.int_of_Z i64m x2) (Wasm_int.int_of_Z i64m x1)) :: xs)
      end
  | MemorySize =>
      update_stack (incr_iid st) (Z.of_N (Wasm.operations.mem_size (wasm_memory st)) :: wasm_stack st)
  | MemoryGrow =>
      let x1 := nth 0%nat (wasm_stack st) 0 in
      let xs := skipn 1%nat (wasm_stack st) in
      if Z.eq_dec (etable_values op_memory_grow_success i) 0 then
        update_stack (incr_iid st) (0xFFFFFFFF :: xs)
      else
        match Wasm.operations.mem_grow (wasm_memory st) (Z.to_N x1) with
        | Some mem' => update_memory (update_stack (incr_iid st) (Z.of_N (Wasm.operations.mem_size (wasm_memory st)) :: xs)) mem'
        | None => st
        end
  | BrTable =>
      if Z.eq_dec (etable_values op_br_table_keep i) 0 then
        let xs := skipn (1 + Z.to_nat (etable_values op_br_table_drop i))%nat (wasm_stack st) in
        update_stack (move_to_iid st (etable_values op_br_table_dst_iid i)) xs
      else
        let xv := nth 1%nat (wasm_stack st) 0 in
        let xs := skipn (2 + Z.to_nat (etable_values op_br_table_drop i))%nat (wasm_stack st) in
        update_stack (move_to_iid st (etable_values op_br_table_dst_iid i)) (xv :: xs)
  | CallIndirect =>
      let xs := skipn 1%nat (wasm_stack st) in
      update_callstack
        (move_to_label (update_stack st xs) (etable_values op_call_indirect_func_index i, 0))
        ((etable_values fid_cell i, etable_values iid_cell i + 1) :: wasm_callstack st)
  end.


(* We do not prove the CallHost instruction *)
Axiom simulate_CallHost : forall i st,
    etable_values (ops_cell CallHost) i = 1
    ->
      exists st' : WasmState, step st st' /\ st' = next_state i st /\ state_rel (i + 1) st'.

Lemma bool_of_Z_of_bool :  forall (b:bool), (bool_of_Z (if b then 1 else 0)) = b.
Proof. destruct b; reflexivity. Qed.

Lemma simulate_step : forall (i : Z) st ,
  0 <= i ->
  i+1 < etable_numRow ->
  etable_values enabled_cell i = 1 ->
  state_rel i st ->
  valid_state st ->
  etable_values frame_id_cell i > 0 ->
  exists st',
    step st st' /\ st' = next_state i st /\ state_rel (i+1) st'.
Proof.
  intros i st Hrange Hmorerange Henabled Hrel Hvalid Hframe.
  assert (Hmops := mops_correct all_opcode_mops_correct i ltac:(lia) ltac:(lia) Henabled).
  destruct (class_of_row i) eqn:Hclass_eq;
  assert (Hclass := Hclass_eq);
  rewrite <- (class_of_row_op i _ Henabled) in Hclass.

  - assert (Hdecode := OpBinShift.BinShift_decode i st Hrange Hrel Henabled Hclass).
    destruct Hdecode as [op [Hdecode1 [Hdecode2 Hdecode3]]].
    unfold valid_state in Hvalid; rewrite Hdecode1 in Hvalid.
    destruct Hvalid as [xr [xl [xs Hvalid]]].
    destruct op.
    + eexists; split; [|split].
      3: { eapply OpBinShift.BinShift_Shl_correct; eauto. }
      1: {
        replace (etable_values op_bin_shift_is_i32 i)
          with (Z_of_bool (bool_of_Z (etable_values op_bin_shift_is_i32 i)))
          by (apply bool_of_Z_simpl; apply OpBinShiftModel.is_i32_bit).
        apply step_BinShift_Shl; eauto.
      }
      1: { unfold next_state. rewrite Hvalid. rewrite Hclass_eq. rewrite <- Hdecode3. reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpBinShift.BinShift_Shr_U_correct; eauto. }
      1: {
        replace (etable_values op_bin_shift_is_i32 i)
          with (Z_of_bool (bool_of_Z (etable_values op_bin_shift_is_i32 i)))
          by (apply bool_of_Z_simpl; apply OpBinShiftModel.is_i32_bit).
        apply step_BinShift_Shr_U; eauto.
      }
      1: { unfold next_state. rewrite Hvalid. rewrite Hclass_eq. rewrite <- Hdecode3. reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpBinShift.BinShift_Shr_S_correct; eauto. }
      1: {
        replace (etable_values op_bin_shift_is_i32 i)
          with (Z_of_bool (bool_of_Z (etable_values op_bin_shift_is_i32 i)))
          by (apply bool_of_Z_simpl; apply OpBinShiftModel.is_i32_bit).
        apply step_BinShift_Shr_S; eauto.
      }
      1: { unfold next_state. rewrite Hvalid. rewrite Hclass_eq. rewrite <- Hdecode3. reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpBinShift.BinShift_Rotl_correct; eauto. }
      1: {
        replace (etable_values op_bin_shift_is_i32 i)
          with (Z_of_bool (bool_of_Z (etable_values op_bin_shift_is_i32 i)))
          by (apply bool_of_Z_simpl; apply OpBinShiftModel.is_i32_bit).
        apply step_BinShift_Rotl; eauto.
      }
      1: { unfold next_state. rewrite Hvalid. rewrite Hclass_eq. rewrite <- Hdecode3. reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpBinShift.BinShift_Rotr_correct; eauto. }
      1: {
        replace (etable_values op_bin_shift_is_i32 i)
          with (Z_of_bool (bool_of_Z (etable_values op_bin_shift_is_i32 i)))
          by (apply bool_of_Z_simpl; apply OpBinShiftModel.is_i32_bit).
        apply step_BinShift_Rotr; eauto.
      }
      1: { unfold next_state. rewrite Hvalid. rewrite Hclass_eq. rewrite <- Hdecode3. reflexivity. }
  - assert (Hdecode := OpBin.Bin_decode i st Hrange Hrel Henabled Hclass).
    Opaque Z.add Z.sub Z.mul Z.pow.    
    destruct Hdecode as [op [Hdecode0 [Hdecode1 Hdecode2]]].
    unfold valid_state in Hvalid; rewrite Hdecode1 in Hvalid.
    destruct Hvalid as [xr [xl [xs Hvalid]]].
    destruct op.
    + eexists; split; [|split].
      3: { eapply OpBin.Bin_Add_correct; eauto. }
      1: {
        replace (etable_values op_bin_is_i32 i)
          with (Z_of_bool (bool_of_Z (etable_values op_bin_is_i32 i)))
          by (apply bool_of_Z_simpl; apply OpBinModel.is_i32_bit).
        apply step_Bin_Add; eauto.
      }
      1: { unfold next_state.
           rewrite Hvalid, Hclass_eq, <- Hdecode0.
           reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpBin.Bin_Sub_correct; eauto. }
      1: {
        replace (etable_values op_bin_is_i32 i)
          with (Z_of_bool (bool_of_Z (etable_values op_bin_is_i32 i)))
          by (apply bool_of_Z_simpl; apply OpBinModel.is_i32_bit).
        apply step_Bin_Sub; eauto.
      }
      1: { unfold next_state. rewrite Hvalid, Hclass_eq, <- Hdecode0. reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpBin.Bin_Mul_correct; eauto. }
      1: {
        replace (etable_values op_bin_is_i32 i)
          with (Z_of_bool (bool_of_Z (etable_values op_bin_is_i32 i)))
          by (apply bool_of_Z_simpl; apply OpBinModel.is_i32_bit).
        apply step_Bin_Mul; eauto.
      }
      1: { unfold next_state. rewrite Hvalid, Hclass_eq, <- Hdecode0. reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpBin.Bin_Div_U_correct; eauto. }
      1: {
        replace (etable_values op_bin_is_i32 i)
          with (Z_of_bool (bool_of_Z (etable_values op_bin_is_i32 i)))
          by (apply bool_of_Z_simpl; apply OpBinModel.is_i32_bit).
        eapply step_Bin_Div_U; eauto.
      }
      1: { unfold next_state. rewrite Hvalid, Hclass_eq, <- Hdecode0. reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpBin.Bin_Rem_U_correct; eauto. }
      1: {
        replace (etable_values op_bin_is_i32 i)
          with (Z_of_bool (bool_of_Z (etable_values op_bin_is_i32 i)))
          by (apply bool_of_Z_simpl; apply OpBinModel.is_i32_bit).
        eapply step_Bin_Rem_U; eauto.
      }
      1: { unfold next_state. rewrite Hvalid, Hclass_eq, <- Hdecode0. reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpBin.Bin_Div_S_correct; eauto. }
      1: {
        replace (etable_values op_bin_is_i32 i)
          with (Z_of_bool (bool_of_Z (etable_values op_bin_is_i32 i)))
          by (apply bool_of_Z_simpl; apply OpBinModel.is_i32_bit).
        eapply step_Bin_Div_S; eauto.
      }
      1: { unfold next_state. rewrite Hvalid, Hclass_eq, <- Hdecode0. reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpBin.Bin_Rem_S_correct; eauto. }
      1: {
        replace (etable_values op_bin_is_i32 i)
          with (Z_of_bool (bool_of_Z (etable_values op_bin_is_i32 i)))
          by (apply bool_of_Z_simpl; apply OpBinModel.is_i32_bit).
        eapply step_Bin_Rem_S; eauto.
      }
      1: { unfold next_state. rewrite Hvalid, Hclass_eq, <- Hdecode0. reflexivity. }
  - assert (Hdecode := OpBrIfEqz.BrIfEqz_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    destruct (OpBrIfEqzModel.keep_cell_bit i) as [Hnokeep | Hkeep].
    + rewrite Hnokeep in Hvalid; simpl in Hvalid.
      destruct Hvalid as [xcond [xd [xs [Hvalid1 Hvalid2]]]].
      destruct (Z.eq_dec xcond 0).
      * subst.
        eexists.
        split; [|split].
        3: {
          try rewrite !(common_unsigned_repr _ OpBrIfEqzModel.drop_cell_common) in *; eauto.
          eapply OpBrIfEqz.BrIfEqz_branch_no_keep_correct; eauto. }
        1: {
          rewrite Hnokeep in Hdecode.
          change (bool_of_Z 0) with false in Hdecode.
          replace (etable_values op_br_if_eqz_dst_pc_cell i)
            with (Wasm_int.Int64.unsigned (Wasm_int.Int64.repr (etable_values op_br_if_eqz_dst_pc_cell i))).
          - eapply step_BrIfEqz_branch_no_keep; eauto.
          - rewrite (common_unsigned_repr64 _ OpBrIfEqzModel.dst_pc_cell_common). auto.
        }
        1: {
          unfold next_state. rewrite Hclass_eq, Hvalid1, Hnokeep.
          rewrite <- Hvalid2.
          simpl.
          rewrite skipn_app, skipn_all.
          replace (length xd - length xd)%nat with 0%nat by lia.
          reflexivity. }
      * eexists.
        split; [|split].
        3: { eapply OpBrIfEqz.BrIfEqz_no_branch_correct; eauto. }
        1: { eapply step_BrIfEqz_no_branch; eauto. }
        1: {
          unfold next_state. rewrite Hclass_eq, Hvalid1, Hnokeep.
          rewrite <- Hvalid2.
          simpl.
          rewrite skipn_app, skipn_all.
          replace (length xd - length xd)%nat with 0%nat by lia.
          destruct (Z.eq_dec xcond 0); [lia|].
          reflexivity. }
    + rewrite Hkeep in Hvalid; simpl in Hvalid.
      destruct Hvalid as [xcond [xv [xd [xs [Hvalid1 Hvalid2]]]]].
      destruct (Z.eq_dec xcond 0).
      * subst.
        eexists.
        split; [|split].
        3: {
          try rewrite !(common_unsigned_repr _ OpBrIfEqzModel.drop_cell_common) in *; eauto.
          eapply OpBrIfEqz.BrIfEqz_branch_and_keep_correct; eauto. }
        1: {
          rewrite Hkeep in Hdecode.
          change (bool_of_Z 1) with true in Hdecode.
          replace (etable_values op_br_if_eqz_dst_pc_cell i)
            with (Wasm_int.Int64.unsigned (Wasm_int.Int64.repr (etable_values op_br_if_eqz_dst_pc_cell i))).
          - eapply step_BrIfEqz_branch_and_keep; eauto.
          - rewrite (common_unsigned_repr64 _ OpBrIfEqzModel.dst_pc_cell_common). auto.
        }
        1: {
          unfold next_state. rewrite Hclass_eq, Hvalid1, Hkeep.
          rewrite <- Hvalid2.
          simpl.
          rewrite skipn_app, skipn_all.
          replace (length xd - length xd)%nat with 0%nat by lia.
          reflexivity. }
      * eexists.
        split; [|split].
        3: { eapply OpBrIfEqz.BrIfEqz_no_branch_correct; eauto. }
        1: { eapply step_BrIfEqz_no_branch; eauto. }
        1: {
          unfold next_state. rewrite Hclass_eq, Hvalid1, Hkeep.
          rewrite <- Hvalid2.
          simpl.
          rewrite skipn_app, skipn_all.
          replace (length xd - length xd)%nat with 0%nat by lia.
          destruct (Z.eq_dec xcond 0); [lia|].
          reflexivity. }
  - assert (Hdecode := OpBrIf.BrIf_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    destruct (OpBrIfModel.keep_cell_bit i) as [Hnokeep | Hkeep].
    + rewrite Hnokeep in Hvalid; simpl in Hvalid.
      destruct Hvalid as [xcond [xd [xs [Hvalid1 Hvalid2]]]].
      destruct (Z.eq_dec xcond 0).
      * subst.
        eexists.
        split; [|split].
        3: { eapply OpBrIf.BrIf_no_branch_correct; eauto. }
        1: { eapply step_BrIf_no_branch; eauto. }
        1: {
          unfold next_state. rewrite Hclass_eq, Hvalid1, Hnokeep.
          rewrite <- Hvalid2.
          reflexivity. }
      * eexists.
        split; [|split].
        3: {
          try rewrite !(common_unsigned_repr _ OpBrIfModel.drop_cell_common) in *; eauto.
          eapply OpBrIf.BrIf_branch_no_keep_correct; eauto. }
        1: {
          rewrite Hnokeep in Hdecode.
          change (bool_of_Z 0) with false in Hdecode.
          replace (etable_values op_br_if_dst_pc_cell i)
            with (Wasm_int.Int64.unsigned (Wasm_int.Int64.repr (etable_values op_br_if_dst_pc_cell i))).
          - eapply step_BrIf_branch_no_keep; eauto.
          - rewrite (common_unsigned_repr64 _ OpBrIfModel.dst_pc_cell_common). auto.
        }
        1: {
          unfold next_state. rewrite Hclass_eq, Hvalid1, Hnokeep.
          rewrite <- Hvalid2.
          simpl.
          rewrite skipn_app, skipn_all.
          replace (length xd - length xd)%nat with 0%nat by lia.
          destruct (Z.eq_dec xcond 0); [lia|].
          reflexivity. }
    + rewrite Hkeep in Hvalid; simpl in Hvalid.
      destruct Hvalid as [xcond [xv [xd [xs [Hvalid1 Hvalid2]]]]].
      destruct (Z.eq_dec xcond 0).
      * subst.
        eexists.
        split; [|split].
        3: { eapply OpBrIf.BrIf_no_branch_correct; eauto. }
        1: { eapply step_BrIf_no_branch; eauto. }
        1: {
          unfold next_state. rewrite Hclass_eq, Hvalid1, Hkeep.
          rewrite <- Hvalid2.
          simpl.
          reflexivity. }
      * eexists.
        split; [|split].
        3: {
          try rewrite !(common_unsigned_repr _ OpBrIfModel.drop_cell_common) in *; eauto.
          eapply OpBrIf.BrIf_branch_and_keep_correct; eauto. }
        1: {
          rewrite Hkeep in Hdecode.
          change (bool_of_Z 1) with true in Hdecode.
          replace (etable_values op_br_if_dst_pc_cell i)
            with (Wasm_int.Int64.unsigned (Wasm_int.Int64.repr (etable_values op_br_if_dst_pc_cell i))).
          - eapply step_BrIf_branch_and_keep; eauto.
          - rewrite (common_unsigned_repr64 _ OpBrIfModel.dst_pc_cell_common). auto.
        }
        1: {
          unfold next_state. rewrite Hclass_eq, Hvalid1, Hkeep.
          rewrite <- Hvalid2.
          simpl.
          rewrite skipn_app, skipn_all.
          replace (length xd - length xd)%nat with 0%nat by lia.
          destruct (Z.eq_dec xcond 0); [lia|].
          reflexivity. }
  - assert (Hdecode := OpBr.Br_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    destruct (OpBrModel.keep_cell_bit i) as [Hnokeep | Hkeep].
    + rewrite Hnokeep in Hvalid; simpl in Hvalid.
      destruct Hvalid as [xd [xs [Hvalid1 Hvalid2]]].
      eexists.
      split; [|split].
      3: {
        try rewrite !(common_unsigned_repr _ OpBrModel.drop_cell_common) in *; eauto.
        eapply OpBr.Br_no_keep_correct; eauto. }
      1: {
        rewrite Hnokeep in Hdecode.
        change (bool_of_Z 0) with false in Hdecode.
        replace (etable_values op_br_dst_pc_cell i)
          with (Wasm_int.Int64.unsigned (Wasm_int.Int64.repr (etable_values op_br_dst_pc_cell i))).
        - eapply step_Br_no_keep; eauto.
        - rewrite (common_unsigned_repr64 _ OpBrModel.dst_pc_cell_common). auto.
      }
      1: {
        unfold next_state. rewrite Hclass_eq, Hvalid1, Hnokeep.
        rewrite <- Hvalid2.
        simpl.
        rewrite skipn_app, skipn_all.
        replace (length xd - length xd)%nat with 0%nat by lia.
        reflexivity. }
    + rewrite Hkeep in Hvalid; simpl in Hvalid.
      destruct Hvalid as [xv [xd [xs [Hvalid1 Hvalid2]]]].
      eexists.
      split; [|split].
      3: {
        try rewrite !(common_unsigned_repr _ OpBrModel.drop_cell_common) in *; eauto.
        eapply OpBr.Br_keep_correct; eauto. }
      1: {
        rewrite Hkeep in Hdecode.
        change (bool_of_Z 1) with true in Hdecode.
        replace (etable_values op_br_dst_pc_cell i)
          with (Wasm_int.Int64.unsigned (Wasm_int.Int64.repr (etable_values op_br_dst_pc_cell i))).
        - eapply step_Br_keep; eauto.
        - rewrite (common_unsigned_repr64 _ OpBrModel.dst_pc_cell_common). auto.
      }
      1: {
        unfold next_state. rewrite Hclass_eq, Hvalid1, Hkeep.
        rewrite <- Hvalid2.
        simpl.
        rewrite skipn_app, skipn_all.
        replace (length xd - length xd)%nat with 0%nat by lia.
        reflexivity. }
  - assert (Hdecode := OpCall.Call_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    eexists.
    split; [|split].
    3: { eapply OpCall.Call_correct; eauto. }
    1: {
      replace (etable_values op_call_index i)
        with (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (etable_values op_call_index i))).
      + eapply step_Call; eauto.
      + try rewrite !(common_unsigned_repr _ OpCallModel.index_common) in *; eauto.
    }
    1: { unfold next_state. rewrite Hclass_eq. reflexivity. }
  - intros. apply simulate_CallHost; auto.
  - assert (Hdecode := OpConst.Const_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    eexists.
    split; [|split].
    3: { eapply OpConst.ConstOp_correct; eauto. }
    1: {
      replace (etable_values op_const_value i)
        with (Wasm_int.Int64.unsigned (Wasm_int.Int64.repr (etable_values op_const_value i))).
      + eapply step_Const; eauto.
      + rewrite (U64_unsigned_repr _ OpConstModel.value_U64). auto.
    }
    1: { unfold next_state. rewrite Hclass_eq. reflexivity. }
  - assert (Hdecode := OpConversion.Conversion_decode i st Hrange Hrel Henabled Hclass).
    destruct Hdecode as [signed [srct [rest [Hdecode1 [Hdecode2 [Hdecode3 [Hdecode4 [Hdecode5 Hdecode6]]]]]]]].
    destruct srct; destruct rest.
    + unfold valid_state in Hvalid; rewrite Hdecode4 in Hvalid.
      destruct Hvalid as [x1 [xs Hvalid]].
      eexists.
      split; [|split].
      3: { eapply OpConversion.ConversionOp_Extend_correct; eauto; intros; congruence. }
      1: { eapply step_Conversion_extend; eauto; intros; congruence. }
      1: {
        unfold next_state. rewrite Hclass_eq, Hvalid.
        rewrite (OpConversion.OpConversion_value_type_correct _ _ Hdecode1).
        rewrite (OpConversion.OpConversion_result_type_correct _ _ Hdecode2).
        rewrite Hdecode3.
        simpl.
        rewrite Wasm_int.Int32.int_of_Z_Z_of_sint.
        rewrite bool_of_Z_of_bool.
        reflexivity.
      }
    + unfold valid_state in Hvalid; rewrite Hdecode4 in Hvalid.
      destruct Hvalid as [x1 [xs Hvalid]].
      eexists.
      split; [|split].
      3: { eapply OpConversion.ConversionOp_Extend_correct; eauto; congruence. }
      1: { eapply step_Conversion_extend; eauto; intros; congruence. }
      1: {
        unfold next_state. rewrite Hclass_eq, Hvalid.
        rewrite (OpConversion.OpConversion_value_type_correct _ _ Hdecode1).
        rewrite (OpConversion.OpConversion_result_type_correct _ _ Hdecode2).
        rewrite Hdecode3.
        simpl.
        rewrite Wasm_int.Int32.int_of_Z_Z_of_sint.
        rewrite bool_of_Z_of_bool.
        reflexivity.
      }
    + unfold valid_state in Hvalid; rewrite Hdecode4 in Hvalid.
      destruct Hvalid as [x1 [xs Hvalid]].
      eexists.
      split; [|split].
      3: { eapply OpConversion.ConversionOp_Extend_correct; eauto; congruence. }
      1: { eapply step_Conversion_extend; eauto; intros; congruence. }
      1: {
        unfold next_state. rewrite Hclass_eq, Hvalid.
        rewrite (OpConversion.OpConversion_value_type_correct _ _ Hdecode1).
        rewrite (OpConversion.OpConversion_result_type_correct _ _ Hdecode2).
        rewrite Hdecode3.
        simpl.
        rewrite Wasm_int.Int32.int_of_Z_Z_of_sint.
        rewrite bool_of_Z_of_bool.
        reflexivity.
      }
    + unfold valid_state in Hvalid; rewrite Hdecode4 in Hvalid.
      destruct Hvalid as [x1 [xs Hvalid]].
      eexists.
      split; [|split].
      3: { eapply OpConversion.ConversionOp_Extend_correct; eauto; congruence. }
      1: { eapply step_Conversion_extend; eauto; intros; congruence. }
      1: {
        unfold next_state. rewrite Hclass_eq, Hvalid.
        rewrite (OpConversion.OpConversion_value_type_correct _ _ Hdecode1).
        rewrite (OpConversion.OpConversion_result_type_correct _ _ Hdecode2).
        rewrite Hdecode3.
        simpl.
        rewrite Wasm_int.Int32.int_of_Z_Z_of_sint.
        rewrite bool_of_Z_of_bool.
        reflexivity.
      }
    + unfold valid_state in Hvalid; rewrite Hdecode4 in Hvalid.
      destruct Hvalid as [x1 [xs Hvalid]].
      eexists.
      split; [|split].
      3: { eapply OpConversion.ConversionOp_Extend_correct; eauto; congruence. }
      1: { eapply step_Conversion_extend; eauto; intros; congruence. }
      1: {
        unfold next_state. rewrite Hclass_eq, Hvalid.
        rewrite (OpConversion.OpConversion_value_type_correct _ _ Hdecode1).
        rewrite (OpConversion.OpConversion_result_type_correct _ _ Hdecode2).
        rewrite Hdecode3.
        simpl.
        rewrite Wasm_int.Int32.int_of_Z_Z_of_sint.
        rewrite bool_of_Z_of_bool.
        reflexivity.
      }
    + unfold valid_state in Hvalid; rewrite Hdecode4 in Hvalid.
      destruct Hvalid as [x1 [xs Hvalid]].
      eexists.
      split; [|split].
      3: { eapply OpConversion.ConversionOp_Extend_correct; eauto; congruence. }
      1: { eapply step_Conversion_extend; eauto; intros; congruence. }
      1: {
        unfold next_state. rewrite Hclass_eq, Hvalid.
        rewrite (OpConversion.OpConversion_value_type_correct _ _ Hdecode1).
        rewrite (OpConversion.OpConversion_result_type_correct _ _ Hdecode2).
        rewrite Hdecode3.
        simpl.
        rewrite Wasm_int.Int32.int_of_Z_Z_of_sint.
        rewrite bool_of_Z_of_bool.
        reflexivity.
      }
    + unfold valid_state in Hvalid; rewrite Hdecode4 in Hvalid.
      destruct Hvalid as [x1 [xs Hvalid]].
      eexists.
      split; [|split].
      3: {
        eapply OpConversion.ConversionOp_Wrap_correct; eauto.
        specialize (Hdecode5 eq_refl).
        destruct Hdecode5.
        auto.
      }
      1: { eapply step_Conversion_wrap; eauto. }
      1: {
        unfold next_state. rewrite Hclass_eq, Hvalid.
        rewrite (OpConversion.OpConversion_value_type_correct _ _ Hdecode1).
        rewrite (OpConversion.OpConversion_result_type_correct _ _ Hdecode2).
        simpl.
        rewrite Wasm_int.Int64.repr_unsigned.
        reflexivity.
      }
    + specialize (Hdecode5 eq_refl).
      destruct Hdecode5.
      congruence.
  - assert (Hdecode := OpDrop.drop_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    destruct Hvalid as [x [xs Hstack]].
    eexists.
    split; [|split].
    3: { eapply OpDrop.DropOp_correct; eauto. }
    1: { eapply step_Drop; eauto. }
    1: { unfold next_state. rewrite Hclass_eq, Hstack. simpl. reflexivity. }
  - assert (Hdecode := OpGlobalGet.GlobalGet_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    edestruct (OpGlobalGet.GlobalGet_correct i st (Z.to_nat (etable_values op_global_get_idx_cell i))) as [glbs' [Hcorrect1 [Hcorrect2 [Hcorrect3 [Hcorrect4 Hcorrect5]]]]]; eauto.
    (* Hcorrect4 : glbs' = etable_values op_global_get_value_u64_cell i *)
    { pose (OpGlobalGetModel.idx_common i).
      lia. }
    eexists.
    split; [|split].
    3: { eapply Hcorrect5. }
    1: { eapply step_GlobalGet; eauto. }
    1: { unfold next_state. rewrite Hclass_eq, Hcorrect4. reflexivity. }
  - assert (Hdecode := OpGlobalSet.GlobalSet_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    destruct Hvalid as [x [xs [Hvalid1 Hvalid2]]].
    pose (v  := Wasm.datatypes.VAL_int64 (Wasm_int.Int64.repr x)).
    assert (Hvalue_rel : value_rel x v).
    { apply OpGlobalSet.value_rel_64. auto. }
    edestruct (OpGlobalSet.GlobalSet_correct i st (Z.to_nat (etable_values op_global_set_idx_cell i))) as [glbs' [Hcorrect1 Hcorrect2]]; eauto.
    { pose (OpGlobalSetModel.idx_common i).
      lia. }
    eexists.
    split; [|split].
    3: { eapply Hcorrect2. }
    1: { eapply step_GlobalSet; eauto. }
    1: {
      unfold next_state.
      rewrite  Hclass_eq, Hvalid1.
      simpl.
      unfold v in Hcorrect1.
      rewrite Hcorrect1.
      reflexivity. }
  - assert (Hdecode := OpLocalGet.LocalGet_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    rewrite (common_unsigned_repr _ OpLocalGetModel.offset_common) in *.
    destruct Hvalid as [y [Hvalid1 Hvalid2]].
    eexists.
    split; [|split].
    3: { eapply OpLocalGet.LocalGetOp_correct; eauto. }
    1: { eapply step_LocalGet;
         try rewrite !(common_unsigned_repr _ OpLocalGetModel.offset_common) in *;
         eauto. }
    1: { unfold next_state. rewrite Hclass_eq.
         rewrite (List.nth_error_nth _ _ 0 Hvalid2).
         reflexivity. }
  - assert (Hdecode := OpLocalSet.LocalSet_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    destruct Hvalid as [Hvalid1 [y [ys [x [xs [Hvalid2 Hvalid3]]]]]].
    eexists.
    split; [|split].
    3: { eapply OpLocalSet.LocalSetOp_correct;
          try rewrite !(common_unsigned_repr _ OpLocalSetModel.offset_common) in *; eauto.
    }
    1: { eapply step_LocalSet with (is32 := (bool_of_Z (etable_values op_local_set_is_i32_cell i))).
         (try rewrite !(common_unsigned_repr _ OpLocalSetModel.offset_common) in * );
           eauto.
          eauto.
          eauto.
          rewrite (common_unsigned_repr _ OpLocalSetModel.offset_common) in *. eauto.
    }
    1: { unfold next_state. rewrite Hclass_eq, Hvalid2. simpl.
         rewrite !(common_unsigned_repr _ OpLocalSetModel.offset_common).
         rewrite !(common_unsigned_repr _ OpLocalSetModel.offset_common) in Hvalid3.
         rewrite <- Hvalid3.
         rewrite List.firstn_app, List.firstn_all, Nat.sub_diag, List.firstn_O, List.app_nil_r.
         rewrite List.skipn_app, List.skipn_all2 by lia.
         replace (length ys + 1 - length ys)%nat with 1%nat by lia.
         reflexivity. }
  - assert (Hdecode := OpLocalTee.LocalTee_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    destruct Hvalid as [Hvalid1 [y [ys [x [xs [Hvalid2 Hvalid3]]]]]].
    eexists.
    split; [|split].
    3: { eapply OpLocalTee.LocalTeeOp_correct;
          try rewrite !(common_unsigned_repr _ OpLocalTeeModel.offset_common) in *; eauto.
    }
    1: { eapply step_LocalTee;
         (try rewrite !(common_unsigned_repr _ OpLocalTeeModel.offset_common) in * );
          eauto. }
    1: { unfold next_state. rewrite Hclass_eq, Hvalid2. simpl.
         rewrite !(common_unsigned_repr _ OpLocalTeeModel.offset_common).
         rewrite !(common_unsigned_repr _ OpLocalTeeModel.offset_common) in Hvalid3.
         rewrite <- Hvalid3.
         rewrite List.firstn_app, List.firstn_all, Nat.sub_diag, List.firstn_O, List.app_nil_r.
         rewrite List.skipn_app, List.skipn_all2 by lia.
         replace (length ys + 1 - length ys)%nat with 1%nat by lia.
         reflexivity. }
  - assert (Hdecode := OpRel.Rel_decode i st Hrange Hrel Henabled Hclass).
    destruct Hdecode as [op [Hdecode0 [Hdecode1 Hdecode2]]].
    unfold valid_state in Hvalid; rewrite Hdecode1 in Hvalid.
    destruct (OpRelModel.is_i32_bit i) as [His32 | His32]; rewrite His32 in *;
    destruct Hvalid as [x1 [x2 [xs Hvalid]]]; destruct op; change (bool_of_Z 0) with false in *.
    + eexists; split; [|split].
      3: { eapply OpRel.OpRelEq_64_correct; eauto. }
      1: { apply step_RelEq_64; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int64.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpRel.OpRelNe_64_correct; eauto. }
      1: { apply step_RelNe_64; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int64.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelGt_s_64_correct; eauto. }
      1: { apply step_RelGt_s_64; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int64.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelGt_u_64_correct; eauto. }
      1: { apply step_RelGt_u_64; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int64.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelGe_s_64_correct; eauto. }
      1: { apply step_RelGe_s_64; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int64.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelGe_u_64_correct; eauto. }
      1: { apply step_RelGe_u_64; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int64.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelLt_s_64_correct; eauto. }
      1: { apply step_RelLt_s_64; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int64.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelLt_u_64_correct; eauto. }
      1: { apply step_RelLt_u_64; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int64.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelLe_s_64_correct; eauto. }
      1: { apply step_RelLe_s_64; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int64.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelLe_u_64_correct; eauto. }
      1: { apply step_RelLe_u_64; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int64.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpRel.OpRelEq_32_correct; eauto. }
      1: { apply step_RelEq_32; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int32.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpRel.OpRelNe_32_correct; eauto. }
      1: { apply step_RelNe_32; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int32.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelGt_s_32_correct; eauto. }
      1: { apply step_RelGt_s_32; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int32.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelGt_u_32_correct; eauto. }
      1: { eapply step_RelGt_u_32; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int32.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelGe_s_32_correct; eauto. }
      1: { apply step_RelGe_s_32; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int32.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelGe_u_32_correct; eauto. }
      1: { apply step_RelGe_u_32; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int32.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelLt_s_32_correct; eauto. }
      1: { apply step_RelLt_s_32; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int32.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelLt_u_32_correct; eauto. }
      1: { apply step_RelLt_u_32; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int32.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelLe_s_32_correct; eauto. }
      1: { apply step_RelLe_s_32; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int32.repr_unsigned. reflexivity. }
    + eexists; split; [|split].
      3: { destruct Hdecode2. eapply OpRel.OpRelLe_u_32_correct; eauto. }
      1: { apply step_RelLe_u_32; eauto. }
      1: { unfold next_state.
           rewrite Hclass_eq, His32, <- Hdecode0, Hvalid. simpl.
           rewrite !Wasm_int.Int32.repr_unsigned. reflexivity. }
  - assert (Hdecode := OpReturn.Return_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    destruct (op_return_keep_cell_bit i) as [Hnokeep | Hkeep].
    + rewrite Hnokeep in *.
      simpl in Hvalid.
      destruct Hvalid as [xs [ys [Hvalid1 Hvalid2]]].
      edestruct OpReturn.Return_correct_nokeep
        as [lbl [cs' [Hcorrect1 Hcorrect2]]];
        try rewrite !(common_unsigned_repr _ OpReturnModel.drop_common) in *; eauto.
      eexists.
      split; [|split].
      3: { apply Hcorrect2. }
      1: { eapply step_Return_nokeep; eauto.
           try rewrite !(common_unsigned_repr _ OpReturnModel.drop_common) in *; eauto. }
      1: { unfold next_state. rewrite Hclass_eq.
           destruct (Z.eq_dec (etable_values op_return_keep i) 0) as [_ | H]; [|congruence].
           simpl. rewrite Hcorrect1. simpl.
           rewrite Hvalid1.
           assert (Hdrop : Z.to_nat (etable_values op_return_drop i) = length xs).
           { rewrite Hvalid2. lia. }
           rewrite Hdrop.
           rewrite List.skipn_app, List.skipn_all, Nat.sub_diag, List.skipn_O.
           reflexivity. }
    + rewrite Hkeep in *.
      simpl in Hvalid.
      destruct Hvalid as [x [xs [ys [Hvalid1 Hvalid2]]]].
      edestruct OpReturn.Return_correct_keep
        as [lbl [cs' [Hcorrect1 Hcorrect2]]];
        try rewrite !(common_unsigned_repr _ OpReturnModel.drop_common) in *; eauto.
      eexists.
      split; [|split].
      3: { apply Hcorrect2. }
      1: { eapply step_Return_keep; eauto.
           try rewrite !(common_unsigned_repr _ OpReturnModel.drop_common) in *; eauto. }
      1: { unfold next_state. rewrite Hclass_eq.
           destruct (Z.eq_dec (etable_values op_return_keep i) 0) as [H | _]; [congruence|].
           simpl. rewrite Hcorrect1. simpl.
           rewrite Hvalid1. simpl.
           assert (Hskip : skipn (Z.to_nat (etable_values op_return_drop i) + 1) (x :: xs ++ ys) = ys).
           { rewrite Nat.add_1_r. simpl.
             rewrite Hvalid2, Nat2Z.id.
             rewrite List.skipn_app, List.skipn_all, Nat.sub_diag, List.skipn_O. reflexivity. }
           rewrite Hskip. reflexivity. }
  - assert (Hdecode := OpSelect.Select_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    destruct Hvalid as [xcond [x1 [x2 [xs Hvalid]]]].
    eexists.
    split; [|split].
    3: { eapply OpSelect.SelectOp_correct; eauto. }
    1: { eapply step_Select; eauto. }
    1: { unfold next_state. rewrite Hclass_eq, Hvalid. simpl. reflexivity. }
  - assert (Hdecode := OpTest.Test_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    destruct Hvalid as [x1 [xs Hvalid]].
    eexists.
    split; [|split].
    3: { eapply OpTest.TestOp_correct; eauto. }
    1: { eapply step_Test; eauto. }
    1: { unfold next_state. rewrite Hclass_eq, Hvalid. simpl. reflexivity. }
  - assert (Hdecode := OpUnary.Unary_decode i st Hrange Hrel Henabled Hclass).
    destruct Hdecode as [op [Hdecode0 [Hdecode1 Hdecode2]]].
    destruct op.
    + destruct (OpUnaryModel.is_i32_bit i) as [Hi32 | Hi32].
      * rewrite Hi32 in Hdecode1. change (bool_of_Z 0) with false in Hdecode1.
        unfold valid_state in Hvalid; rewrite Hdecode1 in Hvalid.
        destruct Hvalid as [x1 [xs Hvalid]].
        eexists.
        split; [|split].
        3: { eapply OpUnary.UnaryOp_Ctz_64_correct; eauto. }
        1: { eapply step_Unary_Ctz_64; eauto. }
        1: { unfold  next_state.
             rewrite Hclass_eq, Hvalid, <- Hdecode0, Hi32.
             Opaque Wasm_int.int_ctz.
             simpl.
             rewrite Wasm_int.Int64.repr_unsigned.
             reflexivity. }
      * rewrite Hi32 in Hdecode1. change (bool_of_Z 0) with false in Hdecode1.
        unfold valid_state in Hvalid; rewrite Hdecode1 in Hvalid.
        destruct Hvalid as [x1 [xs Hvalid]].
        eexists.
        split; [|split].
        3: { eapply OpUnary.UnaryOp_Ctz_32_correct; eauto. }
        1: { eapply step_Unary_Ctz_32; eauto. }
        1: { unfold  next_state.
             rewrite Hclass_eq, Hvalid, <- Hdecode0, Hi32. simpl.
             rewrite Wasm_int.Int32.repr_unsigned.
             reflexivity. }
    + unfold valid_state in Hvalid; rewrite Hdecode1 in Hvalid.
      assert (Hvalid' : exists x1 xs, wasm_stack st = Wasm_int.Z_of_uint i64m x1 :: xs).
      { destruct (bool_of_Z (etable_values op_unary_is_i32 i)); destruct Hvalid as [x1 [xs Hvalid]]; eauto. }
      destruct Hvalid' as [x1 [xs Hvalid']].
      eexists.
      split; [|split].
      3: { eapply OpUnary.UnaryOp_Clz_correct; eauto. }
      1: { replace (etable_values op_unary_is_i32 i)
             with (Z_of_bool (bool_of_Z (etable_values op_unary_is_i32 i))).
           eapply step_Unary_Clz; eauto.
           destruct (OpUnaryModel.is_i32_bit i) as [Hi32|Hi32]; rewrite Hi32; reflexivity. }
      1: {
        Opaque Wasm_int.int_clz.
        unfold  next_state.
        rewrite Hclass_eq, <- Hdecode0, Hvalid'. simpl.
        rewrite Wasm_int.Int64.repr_unsigned.
        reflexivity. }
    + unfold valid_state in Hvalid; rewrite Hdecode1 in Hvalid.
      assert (Hvalid' : exists x1 xs, wasm_stack st = Wasm_int.Z_of_uint i64m x1 :: xs).
      { destruct (bool_of_Z (etable_values op_unary_is_i32 i)); destruct Hvalid as [x1 [xs Hvalid]]; eauto. }
      destruct Hvalid' as [x1 [xs Hvalid']].
      eexists.
      split; [|split].
      3: { eapply OpUnary.UnaryOp_Popcnt_correct; eauto. }
      1: { eapply step_Unary_Popcnt; eauto. }
      1: {
       Opaque Wasm_int.int_popcnt.
        unfold  next_state.
        rewrite Hclass_eq, <- Hdecode0, Hvalid'. simpl.
        rewrite Wasm_int.Int64.repr_unsigned.
        reflexivity. }
  - assert (Hdecode := OpLoad.Load_decode i st Hrange Hrel Henabled Hclass).
    destruct Hdecode as [lz [off [Hdecode1 [Hdecode2 Hdecode3]]]].
    unfold valid_state in Hvalid; rewrite Hdecode1 in Hvalid.
    destruct Hvalid as [base [xs Hvalid]].
    edestruct (OpLoad.load_correct i st base xs ((bool_of_Z (etable_values op_load_is_sign i))) lz
    (if (bool_of_Z (etable_values op_load_is_i32 i)) then RES32 else RES64)
              ) as [bs [Hcorrect1 [Hres_eq Hcorrect2]]]; eauto.
    { rewrite bool_of_Z_simpl by (apply OpLoadModel.is_sign_bit).
      reflexivity. }
    { destruct (OpLoadModel.is_i32_bit i) as [H|H]; rewrite H; reflexivity. }
    eexists; split; [|split].
    3: { apply Hcorrect2. }
    1: { eapply step_Load; eauto.
         rewrite Hdecode2 in *.
         rewrite Hdecode3 in *.
         eauto. }
    1: { unfold next_state. rewrite Hclass_eq, Hvalid. simpl. rewrite Hres_eq. reflexivity. }
  - assert (Hdecode := OpStore.Store_decode i st Hrange Hrel Henabled Hclass).
    destruct Hdecode as [lz [off [Hdecode1 [Hdecode2 Hdecode3]]]].
    unfold valid_state in Hvalid; rewrite Hdecode1 in Hvalid.
    destruct Hvalid as [v [base [xs Hvalid]]].
    edestruct OpStore.Store_correct as [new_mem [Hcorrect1 Hcorrect2]]; eauto.
    eexists; split; [|split].
    3: { apply Hcorrect2. }
    1: { eapply step_Store; eauto.
         rewrite Hdecode2 in *.
         rewrite Hdecode3 in *.
         eauto. }
    1: { unfold next_state. rewrite Hclass_eq, Hvalid. simpl. rewrite Hcorrect1. reflexivity. }
  - assert (Hdecode := OpBinBit.BinBit_decode i st Hrange Hrel Henabled Hclass).
    destruct Hdecode as [op [Hdecode0 [Hdecode1 Hdecode2]]].
    unfold valid_state in Hvalid; rewrite Hdecode1 in Hvalid.
    destruct Hvalid as [x1 [x2 [xs Hvalid]]].
    destruct op.
    Opaque Wasm_int.int_and  Wasm_int.int_or Wasm_int.int_xor.    
    + eexists; split; [|split].
      3: { eapply OpBinBit.BitOp_And_correct; eauto. }
      1: { eapply step_BinBit_And; eauto. }
      1: { unfold  next_state.
           rewrite Hclass_eq, Hvalid, <- Hdecode0.
           simpl.
           rewrite !Wasm_int.Int64.repr_unsigned.
           reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpBinBit.BitOp_Or_correct; eauto. }
      1: { eapply step_BinBit_Or; eauto. }
      1: { unfold  next_state.
           rewrite Hclass_eq, Hvalid, <- Hdecode0.
           simpl.
           rewrite !Wasm_int.Int64.repr_unsigned.
           reflexivity. }
    + eexists; split; [|split].
      3: { eapply OpBinBit.BitOp_Xor_correct; eauto. }
      1: { eapply step_BinBit_Xor; eauto. }
      1: { unfold  next_state.
           rewrite Hclass_eq, Hvalid, <- Hdecode0.
           simpl.
           rewrite !Wasm_int.Int64.repr_unsigned.
           reflexivity. }
  - assert (Hdecode := OpMemorySize.MemorySize_decode i st Hrange Hrel Henabled Hclass).
    eexists.
    split; [|split].
    3: { eapply OpMemorySize.MemorySizeOp_correct; eauto. }
    1: { apply step_MemorySize; auto. }
    1: { unfold next_state. rewrite Hclass_eq. reflexivity. }
  - assert (Hdecode := OpMemoryGrow.MemoryGrow_decode i st Hrange Hrel Henabled Hclass).
    unfold valid_state in Hvalid; rewrite Hdecode in Hvalid.
    destruct Hvalid as [x1 [xs Hvalid]].
    destruct (OpMemoryGrowModel.success_bit i) as [Hno_success | Hsuccess].
    + eexists.
      split; [|split].
      3: { eapply OpMemoryGrow.MemoryGrowOp_correct_nosuccess; eauto. }
      1: { eapply step_MemoryGrow_nosuccess; eauto. }
      1: { unfold next_state. rewrite Hclass_eq, Hvalid. simpl.
           destruct (Z.eq_dec (etable_values op_memory_grow_success i) 0); [reflexivity | congruence]. }
    + edestruct OpMemoryGrow.MemoryGrowOp_correct_success as [mem' [Hcorrect1 Hcorrect2]]; eauto.
      eexists.
      split; [|split].
      3: { apply Hcorrect2. }
      1: { eapply step_MemoryGrow_success; eauto. }
      1: { unfold next_state. rewrite Hclass_eq, Hvalid. simpl.
           destruct (Z.eq_dec (etable_values op_memory_grow_success i) 0) as [H | _]; [congruence|].
           rewrite Hcorrect1. reflexivity. }
  - assert (Hdecode := OpBrTable.Br_decode i st Hrange Hrel Henabled Hclass).
    destruct Hdecode as [Hdecode1 [entries [e [Hdecode_entries [Hdecode_len [Hdecode_index [Hdecode_nth [Hdecode_drop [Hdecode_keep Hdecode_dst]]]]]]]]].
    unfold valid_state in Hvalid. rewrite Hdecode1 in Hvalid.
    specialize (Hvalid entries _ e Hdecode_entries Hdecode_nth).
    destruct Hdecode_index as [[Hdecode_index1 Hdecode_index2] | [Hdecode_index1 Hdecode_index2]];
      destruct (br_table_keep e) eqn:He_keep.
    + destruct Hvalid as [xid [xv [xd [xs [Hvalid_stack Hvalid_drop]]]]].
      destruct (OpBrTable.BrTable_branch_and_keep_correct i st xid xv xd xs Hrange Henabled Hmops Hclass Hrel Hvalid_stack) as [Hxid Hrel'].
        { rewrite <- Hdecode_drop. congruence. }
        { symmetry; apply Hdecode_keep. }
      eexists; split; [|split].
      3: { exact Hrel'. }
      1: { rewrite <- Hdecode_dst.
           eapply step_BrTable_noob_keep; eauto.
           - rewrite common_unsigned_repr by (apply OpBrTableModel.targets_len_common); now auto.
           - rewrite common_unsigned_repr by (apply OpBrTableModel.targets_len_common).
             rewrite <- Hxid.
             pose (OpBrTableModel.effective_index_common i).
             lia.
           - rewrite <- Hxid.
             rewrite <- Hdecode_index2.
             apply Hdecode_nth. }
      1: { unfold next_state. rewrite Hclass_eq.
           destruct (Z.eq_dec (etable_values op_br_table_keep i) 0) as [Heq | _].
           { simpl in Hdecode_keep. lia. }
           simpl. rewrite Hvalid_stack. simpl.
           replace (Z.to_nat (etable_values op_br_table_drop i)) with (length xd)
             by (rewrite <- Hdecode_drop; lia).
           rewrite List.skipn_app, List.skipn_all, Nat.sub_diag, List.skipn_O. reflexivity. }
    + destruct Hvalid as [xid [xd [xs [Hvalid_stack Hvalid_drop]]]].
      destruct (OpBrTable.BrTable_branch_no_keep_correct i st xid xd xs Hrange Henabled Hmops Hclass Hrel Hvalid_stack) as [Hxid Hrel'].
      { rewrite <- Hdecode_drop. congruence. }
        { symmetry; apply Hdecode_keep. }
      eexists; split; [|split].
      3: { exact Hrel'. }
      1: { rewrite <- Hdecode_dst.
           eapply step_BrTable_noob_nokeep; eauto.
           - rewrite common_unsigned_repr by (apply OpBrTableModel.targets_len_common); now auto.
           - rewrite common_unsigned_repr by (apply OpBrTableModel.targets_len_common).
             rewrite <- Hxid.
             pose (OpBrTableModel.effective_index_common i).
             lia.
           - rewrite <- Hxid.
             rewrite <- Hdecode_index2.
             apply Hdecode_nth. }
      1: { unfold next_state. rewrite Hclass_eq.
           destruct (Z.eq_dec (etable_values op_br_table_keep i) 0) as [_ | Hneq].
           { simpl. rewrite Hvalid_stack. simpl.
             replace (Z.to_nat (etable_values op_br_table_drop i)) with (length xd)
               by (rewrite <- Hdecode_drop; lia).
             rewrite List.skipn_app, List.skipn_all, Nat.sub_diag, List.skipn_O. reflexivity. }
           { simpl in Hdecode_keep. lia. } }
    + destruct Hvalid as [xid [xv [xd [xs [Hvalid_stack Hvalid_drop]]]]].
      destruct (OpBrTable.BrTable_branch_and_keep_correct i st xid xv xd xs Hrange Henabled Hmops Hclass Hrel Hvalid_stack) as [Hxid Hrel'].
        { rewrite <- Hdecode_drop. congruence. }
        { symmetry; apply Hdecode_keep. }
      eexists; split; [|split].
      3: { exact Hrel'. }
      1: { rewrite <- Hdecode_dst.
           eapply step_BrTable_oob_keep; eauto.
           - rewrite common_unsigned_repr by (apply OpBrTableModel.targets_len_common); now auto.
           - rewrite common_unsigned_repr by (apply OpBrTableModel.targets_len_common).
             rewrite <- Hxid.
             pose (OpBrTableModel.effective_index_common i).
             lia.
           - rewrite common_unsigned_repr by (apply OpBrTableModel.targets_len_common).
             rewrite <- Hdecode_index2.
             apply Hdecode_nth. }
      1: { unfold next_state. rewrite Hclass_eq.
           destruct (Z.eq_dec (etable_values op_br_table_keep i) 0) as [Heq | _].
           { simpl in Hdecode_keep. lia. }
           simpl. rewrite Hvalid_stack. simpl.
           replace (Z.to_nat (etable_values op_br_table_drop i)) with (length xd)
             by (rewrite <- Hdecode_drop; lia).
           rewrite List.skipn_app, List.skipn_all, Nat.sub_diag, List.skipn_O. reflexivity. }
    + destruct Hvalid as [xid [xd [xs [Hvalid_stack Hvalid_drop]]]].
      destruct (OpBrTable.BrTable_branch_no_keep_correct i st xid xd xs Hrange Henabled Hmops Hclass Hrel Hvalid_stack) as [Hxid Hrel'].
        { rewrite <- Hdecode_drop. congruence. }
        { symmetry; apply Hdecode_keep. }
      eexists; split; [|split].
      3: { exact Hrel'. }
      1: { rewrite <- Hdecode_dst.
           eapply step_BrTable_oob_nokeep; eauto.
           - rewrite common_unsigned_repr by (apply OpBrTableModel.targets_len_common); now auto.
           - rewrite common_unsigned_repr by (apply OpBrTableModel.targets_len_common).
             rewrite <- Hxid.
             pose (OpBrTableModel.effective_index_common i).
             lia.
           - rewrite common_unsigned_repr by (apply OpBrTableModel.targets_len_common).
             rewrite <- Hdecode_index2.
             apply Hdecode_nth. }
      1: { unfold next_state. rewrite Hclass_eq.
           destruct (Z.eq_dec (etable_values op_br_table_keep i) 0) as [_ | Hneq].
           { simpl. rewrite Hvalid_stack. simpl.
             replace (Z.to_nat (etable_values op_br_table_drop i)) with (length xd)
               by (rewrite <- Hdecode_drop; lia).
             rewrite List.skipn_app, List.skipn_all, Nat.sub_diag, List.skipn_O. reflexivity. }
           { simpl in Hdecode_keep. lia. } }
  - assert (Hdecode := OpCallIndirect.CallIndirect_decode i st Hrange Hrel Henabled Hclass).
    destruct Hdecode as [Hdecode1 [e [Hdecode_entries [Hdecode_idx [Hdecode_type [Hdecode_offset Hdecode_func]]]]]].
    unfold valid_state in Hvalid. rewrite Hdecode1 in Hvalid.
    destruct Hvalid as [x [xs Hvalid]].
    destruct (OpCallIndirect.CallIndirect_correct i st x xs Hrange Henabled Hmops Hclass Hrel Hvalid) as [Hx Hrel'].
    eexists; split; [|split].
    3: { exact Hrel'. }
    1: { replace (etable_values fid_cell i, etable_values iid_cell i + 1)
           with (fst (wasm_pc st), snd (wasm_pc st) + 1).
         2: { destruct Hrel. rewrite state_pc_rel. reflexivity. }
         replace (etable_values op_call_indirect_func_index i)
           with (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (etable_values op_call_indirect_func_index i))).
         2: { apply common_unsigned_repr. apply OpCallIndirectModel.func_index_common. }
         eapply step_CallIndirect; eauto. }
    1: { unfold next_state. rewrite Hclass_eq, Hvalid. simpl. reflexivity. }
Qed.

Fixpoint extract_states (st:WasmState) (i:Z) (n:nat) :=
  match n with
  | O => nil
  | S n => st :: extract_states (next_state i st) (i+1) n
  end.

Parameter init_st : WasmState.

Axiom type_safety : forall st,  steps init_st st -> valid_state st.

(* This axiom is because the zkWasm circuit does not model the final call and
   final return of the program, instead they are encoded as "static" entries by the front end. *)
Axiom noreturn : forall i,  etable_values frame_id_cell i > 0.

Lemma extract_states_correct : forall n i st,
    0 <= i ->
    i + (Z.of_nat n) < etable_numRow ->
    etable_values enabled_cell (i + (Z.of_nat n)) = 1 ->
    steps init_st st ->
    state_rel i st ->
    exists st_i,
      steps_list st (extract_states st i n) st_i /\ state_rel (i+(Z.of_nat n)) st_i.
Proof.
    induction n.
  - intros i st Hrange0 Hrange Henabled Hvalid Hrel.
    exists st.
    replace (i + Z.of_nat 0) with i by lia.
    split; auto using steps_list_refl.
  - intros i st Hrange0 Hrange Henabled Hvalid Hrel.
    replace  (i+ Z.of_nat (S n)) with  (i+1+(Z.of_nat n)) in Henabled by lia.
    assert (Henabled_prev := enabled_seq_backwards i (i+1+(Z.of_nat n)) ltac:(lia) Henabled).
    destruct (simulate_step i st ltac:(lia) ltac:(lia) Henabled_prev Hrel (type_safety _ Hvalid) (noreturn i))
               as [st' [Hstep [Hnext_state Hrel']]].

    assert (Hvalid' : steps init_st st').
    { eauto using steps_step. }
    specialize (IHn (i+1) st' ltac:(lia) ltac:(lia) Henabled Hvalid' Hrel').
    destruct IHn as [st_i [Hsteps Hrel_i]].
    exists st_i.
    split.
    + simpl.
      apply steps_list_step with st'; auto.
      rewrite <- Hnext_state.
      auto.
    + replace  (i + Z.of_nat (S n))  with  (i + 1 + Z.of_nat n)  by lia.
      auto.
Qed.    

Theorem knowledge_soundness : forall i,
    0 <= i < etable_numRow ->
    etable_values enabled_cell i = 1 ->
    state_rel 0 init_st ->
    exists st_i,
      steps_list init_st (extract_states init_st 0 (Z.to_nat i)) st_i /\ state_rel i st_i.
Proof.
  intros i Hrange Henabled Hrel.
  destruct (extract_states_correct (Z.to_nat i) 0 init_st ltac:(lia) ltac:(lia))
    as [st_i [Hsteps_i Hrel_i]].
  - replace i with (0 + Z.of_nat (Z.to_nat i)) in Henabled by lia.
    exact Henabled.
  - apply steps_refl.
  - auto.
  - exists st_i.
    replace (0 + Z.of_nat (Z.to_nat i)) with i in Hrel_i by lia.
    split; auto.
Qed.

Theorem soundness : forall i,
    0 <= i < etable_numRow ->
    etable_values enabled_cell i = 1 ->
    state_rel 0 init_st ->
    exists st_i,
      steps init_st st_i /\ state_rel i st_i.
Proof.
  intros i Hrange Henabled Hrel.
  destruct (knowledge_soundness i Hrange Henabled Hrel) as [st_i [Hsteps Hrel_i]].
  eauto using steps_list_steps.
Qed.
