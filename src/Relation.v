(* Copyright (C) CertiK 2024-2026 *)

Require Import ZArith.
Require Import List.
Require Import Shared.
Require Import Wasm.numerics.
Require        Wasm.datatypes.
Require Import Lia.
Require Import  ImageTableModel.
Require MTableModel MTable JTableModel.
Require Import Wasm.operations.

Require Export WasmiModel.
Require Export ETableModel.


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
