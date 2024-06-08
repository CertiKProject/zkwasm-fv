(* This file was automatically extracted by prepare_release script. *)

(* Copyright (C) 2024 CertiK. *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import Wasm.numerics.
Require        Wasm.datatypes.
Require Import Lia.
Require Import  ImageTableModel.
Require MTableModel MTable JTableModel.

Require Export ETableModel.

Require Import Wasm.operations.

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

Require MTable.

Fixpoint stack_rel (stk_map : map) (sp : Z) (stk : list Z) :=
  match stk with
  | nil => True
  | x::xs => get stk_map sp = Some x
             /\ stack_rel stk_map (sp+1) xs
  end. 

Definition stk_map eid :=
  MTable.gather_entries eid MTableModel.LocationType_Stack 0 MTableModel.mtable_numRow empty. 

Definition globals_map eid :=
  MTable.gather_entries eid MTableModel.LocationType_Global 0 MTableModel.mtable_numRow empty. 

  (*  Compare with the definition in Wasm.operations:

       Definition sglob_ind (s : store_record) (i : instance) (j : nat) : option nat :=
         List.nth_error (inst_globs i) j.



      Here we (for now) omit the indirection of global addresses -> globals.
   *)

Definition value_rel (z:Z) (v: value) : Prop :=
  match v with
  |  VAL_int32 i => z = Wasm_int.Z_of_uint i32m i
  |  VAL_int64 i => z = Wasm_int.Z_of_uint i64m i
  |  _ => False
  end.

From mathcomp Require seq.

Definition glob_val (gs : list Wasm.datatypes.global) (j : nat) : option value :=
  option_map g_val (List.nth_error gs j).

Definition set_glob (gs : list Wasm.datatypes.global) (k : nat) (v : Wasm.datatypes.value) : option (list Wasm.datatypes.global) :=
  option_map
    (fun g =>
      let g' := Wasm.datatypes.Build_global (Wasm.datatypes.g_mut g) v in
      seq.set_nth g' gs k g')
    (List.nth_error gs k).

Record globals_rel glob_map (gs : list global) := {
    globals_rel_domain : MTable.domain MTableModel.LocationType_Global < Z.of_nat (List.length gs);
    globals_rel_lookup : forall (j:nat) (z:Z), get glob_map (Z.of_nat j) = Some z ->
                                     exists v,  glob_val gs j = Some v /\ value_rel z v;
  }.

Definition heap_map eid :=
  MTable.gather_entries eid MTableModel.LocationType_Heap 0 MTableModel.mtable_numRow empty. 

Record heap_rel (heap_map : map) (size limit : Z) (mem : memory) := {
    heap_rel_lookup : forall (block:N) (z:Z),
      (8 * block + 8 <= mem_length mem) %N ->
      get heap_map (Z.of_N block) = Some z ->
      exists bs,
        read_bytes mem (8 * block) 8 = Some bs /\ Memdata.decode_int bs = z;
    heap_size: size = Z.of_N (mem_size mem);
    heap_valid: ml_valid (mem_data mem);
    heap_bounded: forall block z,
      get heap_map block = Some z -> (8 * block + 8) <= (Z.of_N operations.page_size) * size;
    heap_limit : mem_max_opt mem = Some (Z.to_N limit);
    heap_limit_valid : limit <= Z.of_N Wasm.operations.page_limit
  }.

Fixpoint callstack_rel (current_id current_fid : Z) (cs : list label) :=
  match cs with
  | nil => current_id = 0
  | l :: cs' =>
      0 < current_id < common
      /\ exists next_id,
        0 <= next_id < common
        /\ 0 <= fst l < common
        /\ 0 <= snd l < common
        /\ JTableModel.in_jtable (encode_frame_table_entry current_id next_id current_fid (fst l) (snd l))
        /\ callstack_rel next_id (fst l) cs'
  end.

(* "The i:th row of etable represents the state st". *)
Record state_rel (i : Z) (st : WasmState) := {
    state_pc_rel : (wasm_pc st) = (etable_values fid_cell i, 
                                  etable_values iid_cell i);
    state_stack_rel : stack_rel (stk_map (etable_values eid_cell i))
                                (etable_values sp_cell i + 1)
                                (wasm_stack st);
    state_globals_rel : globals_rel (globals_map (etable_values eid_cell i))
                                    (wasm_globals st);
    state_heap_rel  : heap_rel  (heap_map (etable_values eid_cell i))
                                (etable_values mpages_cell i)
                                (etable_values maximal_memory_pages_cell i)
                                (wasm_memory st);
    state_callstack_rel :   callstack_rel (etable_values frame_id_cell i)
                                          (etable_values fid_cell i)
                                          (wasm_callstack st)

  }.
