(* This file was automatically extracted by prepare_release script. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import ETable.
Require Import MTable.

Require Import OpRelModel.

(* Proofs about op_rel.rs. *)

Require Import Wasm.numerics.
Require Import Lia.
Require Import MTable.
Require Import Bool.

Require Import Relation RelationHelper.

Open Scope Z_scope.

Theorem opcode_mops_correct_rel : forall i,
  0 <= i ->
  etable_values eid_cell i > 0 ->
  opcode_mops_correct Rel i.
Admitted. (* Proof omitted for release, present in original source. *)

Definition bool_to_Z (b: bool) : Z :=
  match b with
    | true => 1
    | false => 0
  end.

Definition bool_to_Z_opp (b: bool) : Z :=
  match b with
    | true => 0
    | false => 1
  end.

(* Wasm_int.int_eq *)
Theorem OpRelEq_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_eq_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_eq i64m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_eq *)
Theorem OpRelEq_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_eq_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_eq i32m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem OpRelNe_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ne_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = ( Wasm_int.Z_of_uint i64m x1 ::  Wasm_int.Z_of_uint i64m x2 :: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z_opp (Wasm_int.int_eq i64m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

Theorem OpRelNe_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ne_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = ( Wasm_int.Z_of_uint i32m x1 ::  Wasm_int.Z_of_uint i32m x2 :: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z_opp (Wasm_int.int_eq i32m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_lt_u *)
Theorem OpRelLt_u_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_lt_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_lt_u i64m x2  x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_lt_u *)
Theorem OpRelLt_u_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_lt_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_lt_u i64m x2  x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_lt_s *)
Theorem OpRelLt_s_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_lt_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_lt_s i64m x2  x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_lt_u *)
Theorem OpRelLt_s_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_lt_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_lt_s i32m x2  x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_gt_u *)
Theorem OpRelGt_u_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_gt_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_gt_u i64m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_gt_u *)
Theorem OpRelGt_u_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_gt_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_gt_u i32m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_gt_s *)
Theorem OpRelGt_s_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_gt_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_gt_s i64m x2  x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_gt_s *)
Theorem OpRelGt_s_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_gt_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_gt_s i32m x2  x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_le_u *)
Theorem OpRelLe_u_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_le_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_le_u i64m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_le_u *)
Theorem OpRelLe_u_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_le_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_le_u i32m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_le_s *)
Theorem OpRelLe_s_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_le_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_le_s i64m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_le_s *)
Theorem OpRelLe_s_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_le_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_le_s i32m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_ge_u *)
Theorem OpRelGe_u_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ge_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_ge_u i64m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_ge_u *)
Theorem OpRelGe_u_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ge_cell i = 1 ->
    etable_values is_sign_cell i = 0 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_ge_u i32m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_ge_s *)
Theorem OpRelGe_s_64_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ge_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 0 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_ge_s i64m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)

(* Wasm_int.int_ge_s *)
Theorem OpRelGe_s_32_correct: forall i st x1 x2 xs,
    0 <= i ->
    (etable_values enabled_cell i) = 1 ->
    mops_at_correct i ->
    etable_values (ops_cell Rel) i = 1 ->
    etable_values op_is_ge_cell i = 1 ->
    etable_values is_sign_cell i = 1 ->
    etable_values is_i32_cell i = 1 ->
    state_rel i st ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    state_rel (i+1) (update_stack (incr_iid st) (bool_to_Z (Wasm_int.int_ge_s i32m x2 x1) :: xs)).
Admitted. (* Proof omitted for release, present in original source. *)
