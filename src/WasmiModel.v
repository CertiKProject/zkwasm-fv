(* Copyright (C) CertiK 2024-2026 *)

Require Import ZArith.
Require Import List.
Require Import Wasm.operations.

Open Scope Z_scope.

(* (fid, iid) *)
Definition label : Set := Z * Z.

Record WasmState := {
    wasm_pc : label; (* program counter *)
    wasm_stack : list Z;
    wasm_globals : list Wasm.datatypes.global;
    wasm_memory : Wasm.datatypes.memory;
    wasm_callstack : list label
}.

Definition incr_iid st :=
  match st with
  | Build_WasmState (fid, iid) stk glb mem cs => Build_WasmState (fid, iid+1) stk glb mem cs
  end.

Definition move_to_label st lbl :=
  match st with
  | Build_WasmState _ stk glb mem cs => Build_WasmState lbl stk glb mem cs
  end.

Definition move_to_iid st next_iid :=
  match st with
  | Build_WasmState (fid, iid) stk glb mem cs => Build_WasmState (fid, next_iid) stk glb mem cs
  end.

Definition update_stack st a' :=
  match st with
  | Build_WasmState pc a b c d => {| wasm_pc := pc; wasm_stack := a'; wasm_globals := b; wasm_memory := c; wasm_callstack := d |}
  end.

Definition update_globals st b' :=
  match st with
  | Build_WasmState pc a b c d => {| wasm_pc := pc;  wasm_stack := a; wasm_globals := b'; wasm_memory := c; wasm_callstack := d |}
  end.

Definition update_memory st c' :=
  match st with
  | Build_WasmState pc a b c d => {| wasm_pc := pc; wasm_stack := a; wasm_globals := b; wasm_memory := c'; wasm_callstack := d |}
  end.

Definition update_callstack st d' :=
  match st with
  | Build_WasmState pc a b c d => {| wasm_pc := pc; wasm_stack := a; wasm_globals := b; wasm_memory := c ; wasm_callstack := d' |}
  end.

  (*  Compare with the definition in Wasm.operations:

       Definition sglob_ind (s : store_record) (i : instance) (j : nat) : option nat :=
         List.nth_error (inst_globs i) j.

       Definition sglob (s : store_record) (i : instance) (j : nat) : option global :=
         option_bind (List.nth_error (s_globals s))
           (sglob_ind s i j).

       Definition sglob_val (s : store_record) (i : instance) (j : nat) : option value :=
          option_map g_val (sglob s i j).

      Here we (for now) omit the indirection of global addresses -> globals.
   *)

From mathcomp Require seq.

Definition glob_val (gs : list Wasm.datatypes.global) (j : nat) : option value :=
  option_map g_val (List.nth_error gs j).

Definition set_glob (gs : list Wasm.datatypes.global) (k : nat) (v : Wasm.datatypes.value) : option (list Wasm.datatypes.global) :=
  option_map
    (fun g =>
      let g' := Wasm.datatypes.Build_global (Wasm.datatypes.g_mut g) v in
      seq.set_nth g' gs k g')
    (List.nth_error gs k).

Definition value_rel (z:Z) (v: value) : Prop :=
  match v with
  |  VAL_int32 i => z = Wasm_int.Z_of_uint i32m i
  |  VAL_int64 i => z = Wasm_int.Z_of_uint i64m i
  |  _ => False
  end.

Inductive BinOp :=
  ADD | SUB | MUL | DIV_u | REM_u | DIV_s | REM_s.

Inductive BinShiftOp :=
  SHL | SHR_u | SHR_s | ROTL | ROTR.

Inductive UnaryOp :=
  CTZ | CLZ | POPCNT.


Inductive RelOp :=
  EQ | NEQ | GT_s | GT_u | GE_s | GE_u | LT_s | LT_u | LE_s | LE_u.

Inductive ConvOpSrc :=
  VAL8 | VAL16 | VAL32 | VAL64.

Inductive ConvOpRes :=
  RES32 | RES64.

Inductive BitOp := AND | OR | XOR.

Inductive Instruction :=
| IBinShift : bool -> BinShiftOp -> Instruction
| IBin : bool -> BinOp -> Instruction
| IBrIfEqz : bool -> Wasm_int.Int32.int -> Wasm_int.Int64.int -> Instruction
| IBrIf : bool -> Wasm_int.Int32.int -> Wasm_int.Int64.int -> Instruction
| IBr : bool -> Wasm_int.Int32.int -> Wasm_int.Int64.int -> Instruction
| ICall : Wasm_int.Int32.int -> Instruction
| ICallIndirect : Wasm_int.Int32.int -> Instruction
| ICallHost
| IConst : bool -> Wasm_int.Int64.int -> Instruction
| IConversion : bool -> bool -> ConvOpSrc -> ConvOpRes -> Instruction
| IDrop 
| IGlobalGet : Wasm_int.Int32.int -> Instruction
| IGlobalSet : Wasm_int.Int32.int -> Instruction
| ILocalGet : bool -> Wasm_int.Int32.int -> Instruction
| ILocalSet : bool -> Wasm_int.Int32.int -> Instruction
| ILocalTee : bool -> Wasm_int.Int32.int -> Instruction
| IRel : bool -> RelOp -> Instruction
| IReturn : bool -> Wasm_int.Int32.int -> Instruction
| ISelect
| ITest : bool -> Instruction
| IUnary : bool -> UnaryOp -> Instruction
| ILoad : bool -> ConvOpSrc -> bool -> Wasm_int.Int64.int -> Instruction
| IStore : bool -> ConvOpSrc -> Wasm_int.Int64.int -> Instruction
| IBinBit : bool -> BitOp -> Instruction
| IMemorySize
| IMemoryGrow
| IBrTable : Wasm_int.Int32.int -> Instruction.

Parameter program : label -> Instruction.

(* Target addresses for the call_indirect instruction.  *)
Record CallTableEntry := {
    entry_table_idx :  Wasm_int.Int32.int;
    entry_type_id :  Wasm_int.Int32.int;
    entry_offset :   Wasm_int.Int32.int;
    entry_func_idx :   Wasm_int.Int32.int;
 }.
    
Parameter module_table_entries : CallTableEntry -> Prop.

Record BrTableEntry := {
    br_table_drop : Wasm_int.Int32.int;
    br_table_keep : bool;
    br_table_dst_pc : Wasm_int.Int32.int;
    }.

    
(* Target addresses for the br_table instruction. In the Wasm
   Specification, BrTables are embedded into the instructions
   themselves, like (IBrTable table), but in our specification of
   Wasmi we keep it as a separate parameter because it makes some
   injectivity lemmas simpler. *)
Parameter br_tables : label -> option (list BrTableEntry).


Definition len_of_LoadSize lz :=
  match lz with
  | VAL8 => 1
  | VAL16 => 2
  | VAL32 => 4
  | VAL64 => 8
  end.


Definition shr_u l r modulus := 
    Z.shiftr l (r mod modulus).

Definition shr_s l r modulus := 
  match Z.shiftr l (modulus - 1) with
  | 1 => Z.shiftr l (r mod modulus) 
          + Z.shiftl (2^(r mod modulus) - 1) (modulus - r mod modulus)
  | _ => Z.shiftr l (r mod modulus)
  end.

Definition rotr l r modulus :=
    Z.shiftr l (r mod modulus) +
    Z.shiftl (l mod 2^(r mod modulus)) (modulus - (r mod modulus)).

Definition shl l r modulus :=
    (Z.shiftl l (r mod modulus)) mod 2^modulus.

Definition rotl l r modulus := 
    (Z.shiftl l (r mod modulus)) mod 2^modulus 
    + Z.shiftr l (modulus - (r mod modulus)).

Definition abs x modulus :=
    match Z.shiftr x (modulus - 1) =? 1 with
    | true => 2^modulus - x
    | false => x
    end.

Definition div_s l r modulus :=
  match Z.lxor (Z.shiftr l (modulus - 1)) (Z.shiftr r (modulus - 1)) =? 1 with
  (* when abs l / abs r = 0, result should be 0 *)
  | true => (2^modulus - (abs l modulus) / (abs r modulus)) mod 2^modulus
  | false => (abs l modulus) / (abs r modulus)
  end.

Definition rem_s l r modulus := 
    match Z.shiftr l (modulus - 1) =? 0 with
    | true => (abs l modulus) mod (abs r modulus)
    (* if abs l mod abs r = 0, result is 0 *)
    | false => (2^modulus - ((abs l modulus) mod (abs r modulus))) mod 2^modulus
    end.

Definition test x : Z :=
  match x with
  | 0 => 1
  | _ => 0
  end.

Definition select cond val2 val1 : Z :=
    match cond with
    | 0 => val2
    | _ => val1
    end.

Definition Z_of_bool (b: bool) : Z :=
  match b with
    | true => 1
    | false => 0
  end.


Definition Z_of_bool_opp (b: bool) : Z :=
  match b with
    | true => 0
    | false => 1
  end.

(* wasm_extend_s in WasmCert-Coq only extends I32 to I64 instead of all types, like I8 to I32, and no notion of padding, so we define our own. *)
Definition sign_extend (signed : bool) (src: ConvOpSrc) (res: ConvOpRes) (x : Z) :=
  if signed then
    match res with
    | RES64 => 
        match src with
        | VAL8  => if Z.odd (Z.shiftr x 7)  then  0xFFFFFFFFFFFFFF00 + x else x
        | VAL16 => if Z.odd (Z.shiftr x 15) then  0xFFFFFFFFFFFF0000 + x else x
        | VAL32 => if Z.odd (Z.shiftr x 31) then  0xFFFFFFFF00000000 + x else x
        | VAL64 => x
        end
    | RES32 =>
        match src with
        | VAL8  => if Z.odd (Z.shiftr x 7)  then  0xFFFFFF00 + x else x
        | VAL16 => if Z.odd (Z.shiftr x 15) then  0xFFFF0000 + x else x
        | VAL32 => x
        | VAL64 => x
        end
    end
  else
    x.

Definition value_type_modulus (typ : ConvOpSrc) :=
  match typ with
  | VAL8 => 2^8
  | VAL16 => 2^16
  | VAL32 => 2^32
  | VAL64 => 2^32    (* sic. It's never used. *)
  end.

From compcert.common Require Import Memdata.

Inductive step : WasmState -> WasmState -> Prop :=
| step_BinShift_Shr_U : forall st is32 xr xl xs,
    program (wasm_pc st) = IBinShift is32 SHR_u ->
    wasm_stack st = xr::xl::xs ->
    step st (update_stack (incr_iid st) (shr_u xl xr (64 - Z_of_bool is32 * 32) :: xs))
| step_BinShift_Shr_S : forall st is32 xr xl xs,
    program (wasm_pc st) = IBinShift is32 SHR_s ->
    wasm_stack st = xr::xl::xs ->
    step st (update_stack (incr_iid st) (shr_s xl xr (64 - Z_of_bool is32 * 32) :: xs)) 
| step_BinShift_Rotr : forall st is32 xr xl xs,
    program (wasm_pc st) = IBinShift is32 ROTR ->
    wasm_stack st = xr::xl::xs ->    
    step st (update_stack (incr_iid st) (rotr xl xr (64 - Z_of_bool is32  * 32) :: xs))
| step_BinShift_Shl : forall st is32 xr xl xs,
    program (wasm_pc st) = IBinShift is32 SHL ->
    wasm_stack st = xr::xl::xs ->    
    step st  (update_stack (incr_iid st) (shl xl xr (64 - Z_of_bool is32 * 32) :: xs))
| step_BinShift_Rotl : forall st is32 xr xl xs,
    program (wasm_pc st) = IBinShift is32 ROTL ->
    wasm_stack st = xr::xl::xs ->    
    step st  (update_stack (incr_iid st) (rotl xl xr (64 - Z_of_bool is32 * 32) :: xs))
| step_Bin_Add : forall st is32 xr xl xs,
    program (wasm_pc st) = IBin is32 ADD ->
    wasm_stack st = xr::xl::xs ->    
    step st (update_stack (incr_iid st) ((xl + xr) mod 2^(64 - Z_of_bool is32 * 32) :: xs))
| step_Bin_Sub : forall st is32 xr xl xs,
    program (wasm_pc st) = IBin is32 SUB ->
    wasm_stack st = xr::xl::xs ->    
    step st  (update_stack (incr_iid st) ((xl - xr) mod 2^(64 - Z_of_bool is32 * 32):: xs))
| step_Bin_Mul : forall st is32 xr xl xs,
    program (wasm_pc st) = IBin is32 MUL ->
    wasm_stack st = xr::xl::xs ->    
    step st (update_stack (incr_iid st) ((xl * xr) mod 2^(64 - Z_of_bool is32  * 32):: xs))
| step_Bin_Div_U : forall st is32 xr xl xs,
    program (wasm_pc st) = IBin is32 DIV_u ->
    wasm_stack st = xr::xl::xs ->    
    step st (update_stack (incr_iid st) ((xl / xr):: xs))
| step_Bin_Rem_U : forall st is32 xr xl xs,
    program (wasm_pc st) = IBin is32 REM_u ->
    wasm_stack st = xr::xl::xs ->    
    step st  (update_stack (incr_iid st) ((xl mod xr):: xs))
| step_Bin_Div_S : forall st is32 xr xl xs,
    program (wasm_pc st) = IBin is32 DIV_s ->
    wasm_stack st = xr::xl::xs ->    
    step st (update_stack (incr_iid st) (div_s xl xr (64 - Z_of_bool is32 * 32):: xs))
| step_Bin_Rem_S : forall st is32 xr xl xs,
    program (wasm_pc st) = IBin is32 REM_s ->
    wasm_stack st = xr::xl::xs ->    
    step st  (update_stack (incr_iid st) (rem_s xl xr (64 - Z_of_bool is32 * 32):: xs))
| step_BrIf_no_branch : forall st keep drop dst_pc xs,
    program (wasm_pc st) = IBrIf keep drop dst_pc ->
    wasm_stack st = 0 :: xs ->
    step st (update_stack (incr_iid st) xs)
| step_BrIf_branch_no_keep :  forall st drop dst_pc xcond xd xs,
    program (wasm_pc st) = IBrIf false drop dst_pc ->
    wasm_stack st = xcond :: xd ++ xs ->
    xcond <> 0 ->
    length xd = Z.to_nat (Wasm_int.Int32.unsigned drop) ->
    step st (update_stack (move_to_iid st (Wasm_int.Int64.unsigned dst_pc)) xs)
| step_BrIf_branch_and_keep : forall st drop dst_pc xcond xv xd xs,
    program (wasm_pc st) = IBrIf true drop dst_pc ->
    wasm_stack st = xcond :: xv :: xd ++ xs ->
    xcond <> 0 ->
    length xd = Z.to_nat (Wasm_int.Int32.unsigned drop) ->
    step st (update_stack (move_to_iid st (Wasm_int.Int64.unsigned dst_pc)) (xv :: xs))         
| step_BrIfEqz_no_branch : forall st keep drop dst_pc xcond xs,
    program (wasm_pc st) = IBrIfEqz keep drop dst_pc ->
    xcond <> 0 ->
    wasm_stack st = xcond :: xs ->
    step st (update_stack (incr_iid st) xs)
| step_Br_no_keep : forall st drop dst_pc xd xs,
    program (wasm_pc st) = IBr false drop dst_pc ->
    wasm_stack st = xd ++ xs ->
    length xd = Z.to_nat (Wasm_int.Int32.unsigned drop) ->
    step st (update_stack (move_to_iid st (Wasm_int.Int64.unsigned dst_pc)) xs)
| step_Br_keep : forall st drop dst_pc xv xd xs,
    program (wasm_pc st) = IBr true drop dst_pc ->
    wasm_stack st = xv :: xd ++ xs ->
    length xd = Z.to_nat (Wasm_int.Int32.unsigned drop) ->
    step st (update_stack (move_to_iid st (Wasm_int.Int64.unsigned dst_pc)) (xv :: xs))       
    
| step_BrIfEqz_branch_no_keep :  forall st drop dst_pc xd xs,
    program (wasm_pc st) = IBrIfEqz false drop dst_pc ->
    wasm_stack st = 0 :: xd ++ xs ->
    length xd = Z.to_nat (Wasm_int.Int32.unsigned drop) ->
    step st (update_stack (move_to_iid st (Wasm_int.Int64.unsigned dst_pc)) xs)
| step_BrIfEqz_branch_and_keep : forall st drop dst_pc xv xd xs,
    program (wasm_pc st) = IBrIfEqz true drop dst_pc ->
    wasm_stack st = 0 :: xv :: xd ++ xs ->
    length xd = Z.to_nat (Wasm_int.Int32.unsigned drop) ->
    step st (update_stack (move_to_iid st (Wasm_int.Int64.unsigned dst_pc)) (xv :: xs))         

| step_Call : forall st idx,
    program (wasm_pc st) = ICall idx ->
    step st (update_callstack (move_to_label st (Wasm_int.Int32.unsigned idx, 0))
               ((fst (wasm_pc st), snd (wasm_pc st) + 1) :: wasm_callstack st))
| step_Const : forall st i32 val,
    program (wasm_pc st) = IConst i32 val ->
    step st (update_stack (incr_iid st) (Wasm_int.Int64.unsigned val :: (wasm_stack st)))
| step_Conversion_wrap : forall st signed is32 x1 xs,
    program (wasm_pc st) = IConversion signed is32 VAL64 RES32 ->
    wasm_stack st = Wasm_int.Z_of_uint i64m x1:: xs ->
    step st (update_stack (incr_iid st) (Wasm_int.Z_of_uint i32m (wasm_wrap x1):: xs))
| step_Conversion_extend : forall st signed is32 srctyp restyp x1 xs,
    program (wasm_pc st) = IConversion signed is32 srctyp restyp ->
    (srctyp = VAL32 -> restyp = RES64) ->
    (srctyp <> VAL64) ->
    wasm_stack st = Wasm_int.Z_of_sint i32m x1:: xs ->
    step st (update_stack (incr_iid st)
               (sign_extend signed srctyp restyp ((Wasm_int.Z_of_sint i32m x1) mod (value_type_modulus srctyp)) :: xs))
| step_Drop : forall st x1 xs,
    program (wasm_pc st) = IDrop ->
    wasm_stack st = x1::xs ->
    step st (update_stack (incr_iid st) xs)
| step_GlobalGet : forall st idx x v xs,    
    wasm_stack st = xs ->
    glob_val (wasm_globals st) idx = Some v ->
    value_rel x v ->
    step st (update_stack (incr_iid st) (x :: xs))
| step_GlobalSet : forall st idx glbs glbs' x v xs,
  value_rel x v ->
  wasm_stack st = (x::xs) ->
  wasm_globals st = glbs ->
  (set_glob glbs idx v) = Some glbs' ->
  step st (update_globals (update_stack (incr_iid st) xs) glbs')
| step_LocalGet : forall st is32 offset y xs,
    program (wasm_pc st) = ILocalGet is32 offset ->
    wasm_stack st = xs ->
    Wasm_int.Int32.unsigned offset > 1 ->
    nth_error xs (Z.to_nat (Wasm_int.Int32.unsigned offset - 1)) = Some y ->
    step st (update_stack (incr_iid st) (y :: xs))
| step_LocalSet : forall st is32 offset y ys x xs,
    program (wasm_pc st) = ILocalSet is32 offset ->
    wasm_stack st = y :: ys ++ x :: xs ->
    Wasm_int.Int32.unsigned offset > 1 ->
    length ys =  (Z.to_nat (Wasm_int.Int32.unsigned offset) - 1) %nat ->
    step st (update_stack (incr_iid st) (ys ++ y :: xs))
  (* Note: The way Wasmi specifies the offset for LocalTee and
   LocalSet differ by 1, and zkWasm then follows that convention,
   which is why the Tee spec has -2 where the Set spec has -1. *)         
| step_LocalTee : forall st is32 offset y ys x xs,
    program (wasm_pc st) = ILocalTee is32 offset ->
    wasm_stack st = y :: ys ++ x :: xs ->
    Wasm_int.Int32.unsigned offset > 1 ->
    length ys =  (Z.to_nat (Wasm_int.Int32.unsigned offset) - 2) %nat ->
    step st (update_stack (incr_iid st) (y ::ys ++ y :: xs))

| step_RelEq_64: forall st x1 x2 xs,
    program (wasm_pc st) = IRel false EQ ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_eq i64m x2 x1) :: xs))
| step_RelEq_32: forall st x1 x2 xs,
    program (wasm_pc st) = IRel true EQ ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_eq i32m x2 x1) :: xs))
| step_RelNe_64: forall st x1 x2 xs,
    program (wasm_pc st) = IRel false NEQ ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool_opp (Wasm_int.int_eq i64m x2 x1) :: xs))
| step_RelNe_32: forall st x1 x2 xs,
    program (wasm_pc st) = IRel true NEQ ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool_opp (Wasm_int.int_eq i32m x2 x1) :: xs))
| step_RelLt_u_64: forall st x1 x2 xs,
    program (wasm_pc st) = IRel false LT_u ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_lt_u i64m x2 x1) :: xs))
| step_RelLt_u_32: forall st x1 x2 xs,
    program (wasm_pc st) = IRel true LT_u ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_lt_u i32m x2 x1) :: xs))
| step_RelLt_s_64: forall st x1 x2 xs,
    program (wasm_pc st) = IRel false LT_s ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_lt_s i64m x2 x1) :: xs))
| step_RelLt_s_32: forall st x1 x2 xs,
    program (wasm_pc st) = IRel true LT_s ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_lt_s i32m x2 x1) :: xs))
| step_RelLe_u_64: forall st x1 x2 xs,
    program (wasm_pc st) = IRel false LE_u ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_le_u i64m x2 x1) :: xs))
| step_RelLe_u_32: forall st x1 x2 xs,
    program (wasm_pc st) = IRel true LE_u ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_le_u i32m x2 x1) :: xs))
| step_RelLe_s_64: forall st x1 x2 xs,
    program (wasm_pc st) = IRel false LE_s ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_le_s i64m x2 x1) :: xs))
| step_RelLe_s_32: forall st x1 x2 xs,
    program (wasm_pc st) = IRel true LE_s ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_le_s i32m x2 x1) :: xs))
| step_RelGt_u_32: forall st x1 x2 xs,
    program (wasm_pc st) = IRel true GT_u ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_gt_u i32m x2 x1) :: xs))
| step_RelGt_u_64: forall st x1 x2 xs,
    program (wasm_pc st) = IRel false GT_u ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_gt_u i64m x2 x1) :: xs))
| step_RelGt_s_32: forall st x1 x2 xs,
    program (wasm_pc st) = IRel true GT_s ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_gt_s i32m x2 x1) :: xs))
| step_RelGt_s_64: forall st x1 x2 xs,
    program (wasm_pc st) = IRel false GT_s ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_gt_s i64m x2 x1) :: xs))
| step_RelGe_u_32: forall st x1 x2 xs,
    program (wasm_pc st) = IRel true GE_u ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_ge_u i32m x2 x1) :: xs))
| step_RelGe_u_64: forall st x1 x2 xs,
    program (wasm_pc st) = IRel false GE_u ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_ge_u i64m x2 x1) :: xs))
| step_RelGe_s_32: forall st x1 x2 xs,
    program (wasm_pc st) = IRel true GE_s ->
    wasm_stack st = (Wasm_int.Z_of_uint i32m x1 :: Wasm_int.Z_of_uint i32m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_ge_s i32m x2 x1) :: xs))
| step_RelGe_s_64: forall st x1 x2 xs,
    program (wasm_pc st) = IRel false GE_s ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1 :: Wasm_int.Z_of_uint i64m x2:: xs) ->
    step st (update_stack (incr_iid st) (Z_of_bool (Wasm_int.int_ge_s i64m x2 x1) :: xs))
         
| step_Return_nokeep : forall st xs drop ys lbl cs',
    program (wasm_pc st) = IReturn false drop ->
    wasm_stack st = xs++ys ->
    wasm_callstack st = lbl::cs' ->
    (Wasm_int.Int32.unsigned drop) = Z.of_nat (length xs) ->
    step st  (update_callstack (update_stack (move_to_label st lbl) ys) cs')
| step_Return_keep : forall st x xs drop ys lbl cs',
    program (wasm_pc st) = IReturn true drop ->
    wasm_stack st = x::xs++ys ->
    wasm_callstack st = lbl::cs' ->
    (Wasm_int.Int32.unsigned drop) = Z.of_nat (length xs) ->
    step st  (update_callstack (update_stack (move_to_label st lbl) (x::ys)) cs')
| step_Select : forall st xcond x1 x2 xs,
  wasm_stack st = xcond:: x2 :: x1:: xs ->
  step st (update_stack (incr_iid st) ((select xcond x2 x1):: xs))
| step_Test : forall st is32 x1 xs,
    program (wasm_pc st) = ITest is32 ->
    wasm_stack st = x1::xs ->
    step st (update_stack (incr_iid st) ((test x1)::xs))
| step_MemorySize : forall st xs,
    program (wasm_pc st) = IMemorySize ->
    wasm_stack st = xs ->
    step st (update_stack (incr_iid st) (Z.of_N (Wasm.operations.mem_size (wasm_memory st)) :: xs))
(* The zkWasm constraints are less deterministic than WasmCert, it may refuse to grow
   a memory even if it is within the limit, and then let a later grow operation 
   succeed. (This probably is allowed by the English-language Wasm specification, even if 
   it would not be done by Wasmi.) So we have two cases, one when the operation succeeds
   and one it doesn't. *)
| step_MemoryGrow_nosuccess : forall st x1 xs,
    program (wasm_pc st) = IMemoryGrow ->
    wasm_stack st = x1:: xs ->
    step st (update_stack (incr_iid st) (0xFFFFFFFF :: xs))
| step_MemoryGrow_success : forall st x1 xs mem',
    program (wasm_pc st) = IMemoryGrow ->
    wasm_stack st = x1:: xs ->
    Wasm.operations.mem_grow (wasm_memory st) (Z.to_N x1) = Some mem' ->
    step st (update_memory (update_stack (incr_iid st) (Z.of_N (Wasm.operations.mem_size (wasm_memory st)) :: xs)) mem')


| step_Unary_Clz : forall st is32 x1 xs,
    program (wasm_pc st) = IUnary is32 CLZ ->
    wasm_stack st = Wasm_int.Z_of_uint i64m x1:: xs ->
    step st (update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_clz i64m x1) - (Z_of_bool is32) * 32:: xs))

| step_Unary_Ctz_64 : forall st x1 xs,
    program (wasm_pc st) = IUnary false CTZ ->
    wasm_stack st = Wasm_int.Z_of_uint i64m x1:: xs ->
    step st (update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_ctz i64m x1):: xs))

| step_Unary_Ctz_32 : forall st x1 xs,
    program (wasm_pc st) = IUnary true CTZ ->
    wasm_stack st = Wasm_int.Z_of_uint i32m x1:: xs ->
    step st (update_stack (incr_iid st) (Wasm_int.Z_of_uint i32m (Wasm_int.int_ctz i32m x1):: xs))
         
| step_Unary_Popcnt : forall st is32 x1 xs,
    program (wasm_pc st) = IUnary is32 POPCNT ->
    wasm_stack st = Wasm_int.Z_of_uint i64m x1:: xs ->
    step st (update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_popcnt i64m x1):: xs))

| step_Store : forall st is32 sz offset v base xs new_mem,
    program (wasm_pc st) = IStore is32 sz offset ->
    wasm_stack st = (v::base::xs) ->
    Wasm.operations.store (wasm_memory st) (Z.to_N base)
      (Z.to_N (Wasm_int.Int64.unsigned offset))
      (Memdata.encode_int (Z.to_nat (len_of_LoadSize sz)) v)
    (Z.to_nat (len_of_LoadSize sz)) = Some (new_mem) ->
    step st (update_memory (update_stack (incr_iid st) xs) new_mem)

| step_Load : forall st is32 sz sign offset bs base xs,
    program (wasm_pc st) = ILoad is32 sz sign offset ->
    wasm_stack st = (base::xs) ->
    Wasm.operations.load (wasm_memory st)
      (Z.to_N base)
      (Z.to_N (Wasm_int.Int64.unsigned offset))
      (Z.to_nat (len_of_LoadSize sz)) = Some bs ->
    step st (update_stack (incr_iid st)
               (sign_extend sign sz (if is32 then RES32 else RES64) (Memdata.decode_int bs) ::xs))
    
| step_BinBit_And : forall st is32 x1 x2 xs,
    program (wasm_pc st) = IBinBit is32 AND ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1:: Wasm_int.Z_of_uint i64m x2::xs) ->
    step st ((update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_and i64m x2 x1) :: xs)))
| step_BinBit_Or : forall st is32 x1 x2 xs,
    program (wasm_pc st) = IBinBit is32 OR ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1:: Wasm_int.Z_of_uint i64m x2::xs) ->
    step st ((update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_or i64m x2 x1) :: xs)))
| step_BinBit_Xor : forall st is32 x1 x2 xs,
    program (wasm_pc st) = IBinBit is32 XOR ->
    wasm_stack st = (Wasm_int.Z_of_uint i64m x1:: Wasm_int.Z_of_uint i64m x2::xs) ->
    step st ((update_stack (incr_iid st) (Wasm_int.Z_of_uint i64m (Wasm_int.int_xor i64m x2 x1) :: xs)))

| step_BrTable_noob_nokeep : forall st len xid xd xs entries e,
    program (wasm_pc st) = IBrTable len ->
    wasm_stack st = xid :: xd ++ xs ->
    br_tables (wasm_pc st) = Some entries ->
    Z.of_nat (List.length entries) = Wasm_int.Int32.unsigned len ->
    0 <= xid < Wasm_int.Int32.unsigned len ->
    List.nth_error entries (Z.to_nat xid) = Some e ->
    br_table_keep e = false ->
    length xd = Z.to_nat (Wasm_int.Int32.unsigned (br_table_drop e)) ->
    step st (update_stack (move_to_iid st (Wasm_int.Int32.unsigned (br_table_dst_pc e))) xs)

| step_BrTable_oob_nokeep : forall st len xid xd xs entries e,
    program (wasm_pc st) = IBrTable len ->
    wasm_stack st = xid :: xd ++ xs ->
    br_tables (wasm_pc st) = Some entries ->
    Z.of_nat (List.length entries) = Wasm_int.Int32.unsigned len ->
    xid >= Wasm_int.Int32.unsigned len ->
    List.nth_error entries (Z.to_nat (Wasm_int.Int32.unsigned len - 1)) = Some e ->
    br_table_keep e = false ->
    length xd = Z.to_nat (Wasm_int.Int32.unsigned (br_table_drop e)) ->
    step st (update_stack (move_to_iid st (Wasm_int.Int32.unsigned (br_table_dst_pc e))) xs)

| step_BrTable_noob_keep : forall st len xid xv xd xs entries e,
    program (wasm_pc st) = IBrTable len ->
    wasm_stack st = xid :: xv :: xd ++ xs ->
    br_tables (wasm_pc st) = Some entries ->
    Z.of_nat (List.length entries) = Wasm_int.Int32.unsigned len ->
    0 <= xid < Wasm_int.Int32.unsigned len ->
    List.nth_error entries (Z.to_nat xid) = Some e ->
    br_table_keep e = true ->
    length xd = Z.to_nat (Wasm_int.Int32.unsigned (br_table_drop e)) ->
    step st (update_stack (move_to_iid st (Wasm_int.Int32.unsigned (br_table_dst_pc e))) (xv::xs))

| step_BrTable_oob_keep : forall st len xid xv xd xs entries e,
    program (wasm_pc st) = IBrTable len ->
    wasm_stack st = xid :: xv :: xd ++ xs ->
    br_tables (wasm_pc st) = Some entries ->
    Z.of_nat (List.length entries) = Wasm_int.Int32.unsigned len ->
    xid >= Wasm_int.Int32.unsigned len ->
    List.nth_error entries (Z.to_nat (Wasm_int.Int32.unsigned len - 1)) = Some e ->
    br_table_keep e = true ->
    length xd = Z.to_nat (Wasm_int.Int32.unsigned (br_table_drop e)) ->
    step st (update_stack (move_to_iid st (Wasm_int.Int32.unsigned (br_table_dst_pc e))) (xv::xs))

(* Full Wasm supports multiple indirect call tables but zkWasm only supports one, which 
   is why the table index is hard-coded to 0. *) 
| step_CallIndirect : forall st x xs  e offset type_index f,
    program (wasm_pc st) = ICallIndirect type_index ->
    wasm_stack st = x::xs ->
    module_table_entries e ->
    entry_table_idx e = Wasm_int.Int32.repr 0 ->
    entry_type_id e = type_index  ->
    entry_offset e = offset ->
    entry_func_idx e = f ->
    step st (update_callstack (move_to_label (update_stack st xs) (Wasm_int.Int32.unsigned f, 0))
               ((fst (wasm_pc st), snd (wasm_pc st) + 1) :: wasm_callstack st))
.
