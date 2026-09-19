# Evaluation of Verus for zkVM verification

This repo contains a proof in Verus of the BitTable module of the zkWasm zero-knowledge virtual machine, which is adapted from the corresponding part our zkWasm correctness proof in Rocq. By comparing the two proofs one can get an estimate of how much proof effort can be saved through Verus's use of SMT solver for automated theorem proving, compared to Rocq's more manual approach.

## Contents

The new proofs are in `src` directory. The `original` directory contains the corresponding files from the Rocq development, for ease of comparison. They are the same files as in the main artifact *except* that we have deleted all the lemmas from `IntegerFunctions.v` which were not related to BitTable. In other words, the lemmas that remain in that file are the same that are proven in the Verus development, for a fair comparison of the amount of proof.

## Compiling the proofs

Install Verus following [the instructions](https://github.com/verus-lang/verus/blob/main/INSTALL.md) (these proofs were tested with the 0.2026.04.12.f1166c4 release, but should work with any recent version). The proof file can then be checked by

```shell
cd src
verus bittable.rs
```

## Structure of the Proof

The proof verifies the correctness of zkWasm's constraints for the "BitTable", which is used in the implementation of the Wasm bitwise instructions (AND, OR, XOR, POPCNT). Specifically, it proves that any table data that satisfies the constraints will be a tabulation of the result of bitwise operations applied to some values. The table has columns names `block_sel`, `lhs`, `rhs`, `op` and `result`, and we prove that for each table row, if `block_sel = 1` then `result = lhs OP rhs`. (In the table, the block_sel is set on every 11th row, and the following 10 rows serve as scratch space to compute the value.)

In order to make a fair comparison, both proofs follow the exact same sequence of axioms and lemmas. The Verus proof is in [src](./src) directory, while for the reference the corresponding Rocq proofs are in [original](./original).  There is first a `model` file with axioms, which represent the zkWasm constrain code. The model file is a hand-translated version of [the corresponding zkWasm file](https://github.com/DelphinusLab/zkWasm/blob/main/crates/zkwasm/src/circuits/bit_table/mod.rs), which is written in Rust using the Halo2 embedded DSL. In both the Rocq and Verus version we translate it into an uninterpreted function representing the table content and an axiom for each zk constraint.

The correctness proofs then considers an arbitrary block of eleven table rows. The lemmas `is_block_values`, `is_u32_values`, and `is_lookup_values` notes the fixed pattern of the control bit columns (same for every block). The lemmas `compose_l_1`, `compose_l_6`, etc, notes that the final values of the `lhs`, `rhs` and `results` columns are obtained by shifting and adding together bytes from the scratch rows. Finally, `bitop_or_spec`, `bitop_xor_spec`, `bitop_and_spec` and `bitop_popcnt_spec` state the correctness of the value in the `result` column. (In the Rocq development these proofs rely on lemmas about bitwise functions from the `IntegerFunctions.v` file.)

## Evaluation

The headline result is impressive: we replaced 2440 lines of code (`IntegerFunctions.v` + `BitTable.v`) with 595 lines of code (bittable.rs). However reasoning about bitwise functions is a particularly good domain for SMT solvers. We can get a better idea about how this will generalize to proofs about zkVMs in general by considering just the main proof file (`bittable.rs` verus `BitTable.v`). The original file had 727 lines of tactics and rewrite hints, while the ported file had 292 lines of proof function bodies (40%). This count somewhat underestimates the difference in effort, because Rocq tactics need more attention while many of the lines of Verus just mention the needed lemma and lets the SMT solver figure out how to use it.

The proofs are shorter for two main reasons. First, Rocq proofs in general are more manual. Compare the two proofs for the `compose_res_1` lemma:


```
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
```

```
proof fn compose_res_1 (i:int)  by (nonlinear_arith)
    requires    val(block_sel,i+1)==1
	     && val(op,i) != Popcnt_index
    ensures  val(result,i+1)
	     ==
	     val(result,i+2)
	     + val(result,i+3)*(1u64<<8)
	     + val(result,i+4)*(1u64<<16)
	     + val(result,i+5)*(1u64<<24)
{
    is_u32_values(i);
    is_lookup_values(i);
    is_op_values(i);
    is_popcnt_false(i+1);
    gate_2_3(i+1);
}
```

Both of them work by refering to a constraint, "gate 2", which has the required equation. But in Rocq the programmer must request to look at the definition of the `compose_u32_if_bit` function, which Verus can automatically use. And further, the equation in the gate is multiplied by the `is_bit` and `is_u32` columns and we need to explicitly use the fact that these column are nonzero (the reasoning starting with `apply circuit_if`). In Verus we can just invoke the lemmas, and the SMT solver will automatically simplify  `is_bit*is_u32*e == 0` to `e == 0`.

The other reason the proof are shorter is that the Verus SMT backend (Z3) supports stronger mathematical theories. In particular, we spent 1033 lines of proof (in `IntegerFunctions.v`) to prove a set of basic facts about bitwise operators, such as

```
Lemma lor_compose : forall a b x y,
    0 <= a < 256 ->
    0 <= x < 256 ->
    Z.lor (Z.lor a (Z.shiftl b 8))
	   (Z.lor x (Z.shiftl y 8))
    = Z.lor (Z.lor a x) (Z.shiftl (Z.lor b y) 8).
```

Using Z3's bitvector theory all such facts can be proven completely automatically. This benefit of course only applies to a subset of instructions in a zkVM, but in general having automated theory solvers available is a powerful tool.

