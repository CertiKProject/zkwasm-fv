(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

(* This file contains some generic results about the behavior of the
integer functions (bitwise AND, OR, etc). These could all be proven,
but for lack of time we have left some of the as assumptions (since
they seem clearly true) -- search for "Admitted in original source". 

These are currently the only Admits in the zkWasm proofs. *)

Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Wasm.numerics.

Require Import Shared.

(* Same definition as in WasmCert *)
Definition popcnt (x: Z) :=
  (Z.of_nat
     (seq.count (fun b : eqtype.Equality.sort eqtype.bool_eqType => eqtype.eq_op b true)
        (Wasm_int.Int64.power_index_to_bits Wasm_int.Int64.wordsize
           (Zbits.Z_one_bits Wasm_int.Int64.wordsize x 0)))).

(* Shared lemmas about integers. *)

Lemma bound_spec_n : forall x n,
  0 <= n ->
  0 <= x ->
  0 <= x < 2^n <-> (forall k,  n <= k -> Z.testbit x k = false).
Admitted. (* Proof omitted for release, present in original source. *)

Lemma land_bound {a b} :
  0 <= a < 256 ->
  0 <= b < 256 ->
  0 <= Z.land a b < 256.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma lxor_bound {a b} :
  0 <= a < 256 ->
  0 <= b < 256 ->
  0 <= Z.lxor a b < 256.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma lor_bound {a b} :
  0 <= a < 256 ->
  0 <= b < 256 ->
  0 <= Z.lor a b < 256.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma land_bound64 {a b} :
  -1 < a <  Wasm_int.Int64.modulus ->
  -1 < b <  Wasm_int.Int64.modulus ->
  -1 < Z.land a b < Wasm_int.Int64.modulus.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma lxor_bound64 {a b} :
  -1 < a <  Wasm_int.Int64.modulus ->
  -1 < b <  Wasm_int.Int64.modulus ->
  -1 < Z.lxor a b < Wasm_int.Int64.modulus.
Admitted. (* Proof omitted for release, present in original source. *)

Lemma lor_bound64 {a b} :
  -1 < a <  Wasm_int.Int64.modulus ->
  -1 < b <  Wasm_int.Int64.modulus ->
  -1 < Z.lor a b < Wasm_int.Int64.modulus.
Admitted. (* Proof omitted for release, present in original source. *)

    Lemma plus_lor : forall a b,
        0 <= a < 256 ->
        a + Z.shiftl b 8 = Z.lor a (Z.shiftl b 8).
Admitted. (* Proof omitted for release, present in original source. *)

    Lemma plus_lor_n : forall n a b,
        0 <= n ->
        0 <= a < 2^n ->
        a + Z.shiftl b n = Z.lor a (Z.shiftl b n).
Admitted. (* Proof omitted for release, present in original source. *)
    
    Lemma land_compose : forall a b x y,
        0 <= a < 256 ->
        0 <= x < 256 ->
        Z.land (Z.lor a (Z.shiftl b 8))
               (Z.lor x (Z.shiftl y 8))
        = Z.lor (Z.land a x) (Z.shiftl (Z.land b y) 8).
Admitted. (* Proof omitted for release, present in original source. *)

    Lemma lxor_compose : forall a b x y,
        0 <= a < 256 ->
        0 <= x < 256 ->
        Z.lxor (Z.lor a (Z.shiftl b 8))
               (Z.lor x (Z.shiftl y 8))
        = Z.lor (Z.lxor a x) (Z.shiftl (Z.lxor b y) 8).
Admitted. (* Proof omitted for release, present in original source. *)

    Lemma lor_compose : forall a b x y,
        0 <= a < 256 ->
        0 <= x < 256 ->
        Z.lor (Z.lor a (Z.shiftl b 8))
               (Z.lor x (Z.shiftl y 8))
        = Z.lor (Z.lor a x) (Z.shiftl (Z.lor b y) 8).
Admitted. (* Proof omitted for release, present in original source. *)

    Lemma land_ones_high : forall x n,
        0 <= n ->
        Z.land (Z.shiftl x n) (Z.ones n) = 0.
Admitted. (* Proof omitted for release, present in original source. *)
    
    Lemma popcnt_compose :  forall a b,
        0 <= a < 256 ->
        popcnt (Z.lor a (Z.shiftl b 8))
        = popcnt a + popcnt b.
Admitted. (* Admitted in original source *)

    Lemma popcnt_commutes_with_uint :
    forall x,
        popcnt (Wasm_int.Z_of_uint i64m x) =
        Wasm_int.Z_of_uint i64m (Wasm_int.Int64.popcnt x).
Admitted. (* Admitted in original source *)

(* Same definition as in WasmCert *)
Definition clz_64 (x: Z) :=
  (Z.of_nat
     (seq.find (fun b : eqtype.Equality.sort eqtype.bool_eqType => eqtype.eq_op b true)
        (Wasm_int.Int64.power_index_to_bits Wasm_int.Int64.wordsize
           (Zbits.Z_one_bits Wasm_int.Int64.wordsize x 0)))).

Lemma clz_64_definition_matches_wasm : forall x,
    clz_64 (Wasm_int.Z_of_uint i64m x) =
    Wasm_int.Z_of_uint i64m (Wasm_int.Int64.clz x).
Admitted. (* Admitted in original source *)

Lemma clz_64_value : forall x y z,
    0 <= y ->
    0 <= z < 2^y ->
    (x = 2^y + z -> clz_64 x = 64 - y - 1) /\
    (x = 0 -> clz_64 x = 64).
Admitted. (* Admitted in original source *)

(* Same definition as in WasmCert *)
Definition ctz (x : Z) (is_i32 : bool) := 
  if is_i32 then 
  (Z.of_nat
    (seq.find (fun b : eqtype.Equality.sort eqtype.bool_eqType => eqtype.eq_op b true)
      (Wasm_int.Int32.power_index_to_bits Wasm_int.Int32.wordsize
        (seq.rev (Zbits.Z_one_bits Wasm_int.Int32.wordsize x 0)))))
  else 
  (Z.of_nat
    (seq.find (fun b : eqtype.Equality.sort eqtype.bool_eqType => eqtype.eq_op b true)
      (Wasm_int.Int64.power_index_to_bits Wasm_int.Int64.wordsize
        (seq.rev (Zbits.Z_one_bits Wasm_int.Int64.wordsize x 0))))).

Lemma ctz_64_definition_matches_wasm : forall x,
    ctz (Wasm_int.Z_of_uint i64m x) false =
    Wasm_int.Z_of_uint i64m (Wasm_int.Int64.ctz x).
Admitted. (* Admitted in original source *)

Lemma ctz_32_definition_matches_wasm : forall x,
    ctz (Wasm_int.Z_of_uint i32m x) true =
    Wasm_int.Z_of_uint i32m (Wasm_int.Int32.ctz x).
Admitted. (* Admitted in original source *)

Lemma ctz_value_with_trailing_bit : forall x y z b,
    0 <= y ->
    z = 0 \/ z > 2^y ->
    x = z + 2^y ->
    ctz x b = y.
Admitted. (* Admitted in original source *)

