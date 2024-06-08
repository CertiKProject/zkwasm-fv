(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.

Require Import Lia.

Open Scope Z_scope.

Definition Zp := Z.  
  
Record table : Type :=
  mkTable {
      colNames : Set;
      numRows : Z;
      value : colNames -> Z -> Zp   (* Will only be called 0..numRows *)
    }.

Parameter field_order : Z.

Fixpoint ForallP {X:Type }(P : X->Prop) (xs : list X) : Prop :=
  match xs with
  | nil => True
  | x::xs => P x /\ ForallP P xs
  end.

(* Note, currently the tables are treated as unbounded. In the real Halo2, they wrap around
   modulo the table size. This corresponds to one additional constraint, saying that
     forall i, value (i + numRows) = value i
   so it's sound to do the verification without that, we could only prove less. *)

(* N.B., need to change the polynomial to do arithmetic modulo p, but let's first 
   do a few proofs with just Z to see what lemmas we will need. *)

Definition gate (t : table) (exprs: (colNames t -> Z -> Z) -> list Z) : Prop :=
forall n,  0 <= n ->
  let es := exprs (fun c i => value t c ((n + i))) in
   ForallP (fun z =>  z (* mod field_order *) = 0) es.

(* Version that does the arithmetic mod p. *)
Definition pgate (t : table) (exprs: (colNames t -> Z -> Z) -> list Z) : Prop :=
forall n,  0 <= n ->
  let es := exprs (fun c i => value t c ((n + i))) in
   ForallP (fun z =>  z mod field_order = 0) es.

Parameter common : Z.  (* The common range. *)

(* A type of finite maps of integers. It's axiomatized here, although it would be easy to implement it instead. *)
Parameter   map : Set.
Definition key := Z.
Definition val := Z.  

Parameter empty : map.
Parameter get : map -> key -> option val.
Parameter set : map -> key -> val -> map.
Parameter gss : forall s k v,  get (set s k v) k = Some v.
Parameter gempty : forall k, get empty k = None.
Parameter gso : forall s k1 k2 v, k1<>k2 -> get (set s k1 v) k2 = get s k2.
Parameter sso : forall s k1 k2 v1 v2, k1<>k2 -> set (set s k1 v1) k2 v2 = set (set s k2 v2) k1 v1.
