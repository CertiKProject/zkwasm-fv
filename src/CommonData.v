(* This file was automatically extracted by prepare_release script. *)

From Coq Require Import Arith ZArith NArith Nnat Psatz List Znumtheory ZBits.
From Flocq Require Import Zaux.
From mathcomp.ssreflect Require Import seq ssreflect eqtype.

(* Notation overridden of mathcomp to Coq *)
Set Warnings "-notation-overridden".
From mathcomp.ssreflect Require Import ssrnat ssrbool ssrfun.
Set Warnings "+notation-overridden".

From mathcomp Require Import lra zify.

Require Import CommonSeq.

(** * ssr <-> Coq adaptation
  Lemmas used to provide compatibility between ssr and Coq libraries.
*)

(* numerics *)
Open Scope Z_scope.

Require Import IntegerFunctions.

(** * Int (binary representation) related
    Lemmas related to binary representation of integers.
 *)

(** * bits abstraction
    Lemmas for bits abstraction: bitmask and bit-extraction.
*)
Definition bitmask n m val :=
  Z.land val (Z.shiftl (Z.ones m) n).


(** * Bytes related
    Lemmas related to bytes and bits.
 *)

From Wasm Require Import bytes properties.
From compcert Require Import Integers Memdata Archi.
Transparent Archi.big_endian.

