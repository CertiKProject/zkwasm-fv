(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

(* This file models the optable from rtable.rs. 

   The other tables in rtable.rs are not explicitly modeled, because we consider range
   checks to be part of the cell allocation layer in zkWasm, and instead 
   specify the ranges with axioms in the other model files. 

   In the zkWasm Rust code, the optable consist of Fixed columns which are written by
   for-loops. Here we axiomatize what is written at each loop index. (One possible way
   to get a smaller trusted base could be to pretty-print the actual table from Halo2
   and translate it into Coq to prove that these axioms are in fact satisfied.)
*)

Require Import List.
Require Import ZArith.
Require Import Lia.

Require Import Shared.
Require Import IntegerFunctions.

Inductive op_table_cols :=
| op_op
| op_left
| op_right
| op_result.

Parameter op_table_values : op_table_cols -> Z -> Z.
Parameter op_table_numRow : Z. (* The full table must be bigger than 196993 = 256*256*3 + 256 + 1 + 128 *)


Definition BitOp_And := 0.
Definition BitOp_Or := 1.
Definition BitOp_Xor := 2.
Definition Popcnt_index := 3.
Definition Power_index := 4.

Definition op_table_at i op x y result : Prop :=
     op_table_values op_op i = op
  /\  op_table_values op_left i = x
  /\  op_table_values op_right i = y
  /\  op_table_values op_result i = result.

Definition in_op_table op x y result : Prop :=
exists i,
   0 <= i < op_table_numRow /\ op_table_at i op x y result.

Axiom op_table_and : forall x y,
  0 <= x < 256 ->
  0 <= y < 256 ->
  let i := 256*x+y in
     op_table_at i BitOp_And x y (Z.land x y).

Axiom op_table_or : forall x y,
  0 <= x < 256 ->
  0 <= y < 256 ->
  let i := 256*256 + 256*x+y in
     op_table_at i BitOp_Or x y (Z.lor x y).

Axiom op_table_xor : forall x y,
  0 <= x < 256 ->
  0 <= y < 256 ->
  let i := 2*256*256 + 256*x+y in
     op_table_at i BitOp_Xor x y (Z.lxor x y).

Axiom op_table_popcnt : forall x,
  0 <= x < 256 ->
  let i := 3*256*256 + x in
    op_table_at i Popcnt_index x 0 (popcnt x). 

Axiom op_table_power1 :
  op_table_at (3*256*256 + 256) Power_index 0 0 0.

Axiom op_table_power : forall x,
  0 <= x < 128 ->
  let i := 3*256*256 + 256 + 1 + x in
    op_table_at i Power_index 0 (128+x) (Z.shiftl  1 x). 

Axiom op_table_other : forall i,
   3*256*256 +  256 + 128 <= i ->
    op_table_at i 0 0 0 0.
