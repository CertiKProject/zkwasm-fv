use vstd::prelude::*;

verus! {

    pub const m1 : u64  = 0x5555555555555555; 
    pub const m2 : u64  = 0x3333333333333333; //binary: 00110011..
    pub const m4 : u64  = 0x0f0f0f0f0f0f0f0f; //binary:  4 zeros,  4 ones ...
    pub const m8 : u64  = 0x00ff00ff00ff00ff; //binary:  8 zeros,  8 ones ...
    pub const m16 : u64 = 0x0000ffff0000ffff; //binary: 16 zeros, 16 ones ...
    pub const m32 : u64 = 0x00000000ffffffff; //binary: 32 zeros, 32 ones

    pub open spec fn popcnt (x : u64) -> u64
    {
	let x1  = add((x & m1 ), ((x >>  1) & m1 )); //put count of each  2 bits into those  2 bits 
	let x2  = add((x1 & m2 ), ((x1 >>  2) & m2)); //put count of each  4 bits into those  4 bits 
	let x4  = add((x2 & m4 ), ((x2 >>  4) & m4)); //put count of each  8 bits into those  8 bits 
	let x8  = add((x4 & m8 ), ((x4 >>  8) & m8)); //put count of each 16 bits into those 16 bits 
	let x16 = add((x8 & m16), ((x8 >> 16) & m16)); //put count of each 32 bits into those 32 bits 
	let x32 = add((x16 & m32),((x16 >> 32) & m32)); //put count of each 64 bits into those 64 bits 
	x32
    }
    
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
    pub struct Column{
	pub index: usize,
    }

    pub uninterp spec fn val(col: Column, row: int) -> int;

    
    pub spec const BitOp_And : int = 0;
    pub spec const BitOp_Or : int = 1;
    pub spec const BitOp_Xor : int = 2;
    pub spec const Popcnt_index : int = 3;
    pub spec const Power_index : int = 4;


    pub spec const block_sel : Column = Column{index: 0};
    pub spec const lookup_sel : Column = Column{index: 1};
    pub spec const u32_sel : Column = Column{index: 2};
    pub spec const op : Column = Column{index: 3};
    pub spec const helper : Column = Column{index: 4};
    pub spec const left : Column = Column{index: 5};
    pub spec const right : Column = Column{index: 6};
    pub spec const result : Column = Column{index: 7};

    #[verifier::external_body]   // `external_body` makes Verus treat it as an uninterpreted parameter.
    pub spec const bit_table_start : int = 0;

    pub spec const STEP_SIZE : int  = 11;

    pub broadcast axiom fn block_sel_spec (i:int)
	ensures ({let k = (i-bit_table_start)%STEP_SIZE;
		  (#[trigger] val(block_sel,i)) == (if (k == 1) {1int} else {0int})})
    ;

    pub broadcast axiom fn u32_sel_spec (i:int)
	ensures ((#[trigger] val(u32_sel,i))
		  == {let k = (i-bit_table_start)%STEP_SIZE;
		      (if (k == 1 || k == 6) {1int} else {0int})})
    ;
    
    pub broadcast axiom fn lookup_sel_spec (i:int)
	ensures ({let k = (i-bit_table_start)%STEP_SIZE;
		  (#[trigger] val(lookup_sel,i)) == (if (k==2 || k==3 || k==4 || k==5 ||k==7 ||k==8 || k==9 || k==10) {1int} else {0int})})
    ;
    

/*
     meta.create_gate("bit table: 1. op consistent", |meta| {
     vec![
	 (fixed_curr!(meta, u32_sel) + fixed_curr!(meta, lookup_sel))
	     * (prev!(meta, op) - curr!(meta, op)),
	 fixed_curr!(meta, u32_sel)
	     * curr!(meta, helper)
	     * (curr!(meta, op) - constant_from!(BitTableOp::Popcnt.index())),
	 fixed_curr!(meta, u32_sel)
	     * (curr!(meta, helper) - constant_from!(1))
	     * curr!(meta, op)  // - constant_from!(BitOp::And)): 0
	     * (curr!(meta, op) - constant_from!(BitOp::Or))
	     * (curr!(meta, op) - constant_from!(BitOp::Xor)),
	 // is_popcnt cell is bit
	 fixed_curr!(meta, u32_sel)
	     * curr!(meta, helper)
	     * (curr!(meta, helper) - constant_from!(1)),
     ]
 });

*/

    pub axiom fn gate_1_1 (i:int)
	ensures (val(u32_sel, i) + val(lookup_sel,i)) * (val(op,i-1)-val(op,i)) == 0
    ;


    pub axiom fn gate_1_2 (i:int)
	ensures val(u32_sel, i) * val(helper,i) * (val(op,i) - Popcnt_index) == 0
    ;

    pub axiom fn gate_1_3 (i:int)
	ensures  val(u32_sel,i)
	     * (val(helper,i) -1)
	     * (val(op,i))
	     * (val(op,i) - BitOp_Or)
	     * (val(op,i) - BitOp_Xor) == 0
    ;




    /*
    macro_rules! compose_u32_helper {
        ($col:expr) => {
            (0..4)
                .into_iter()
                .map(|x| {
                    if x == 0 {
                        nextn!(meta, $col, 1)
                    } else {
                        (nextn!(meta, $col, x + 1)) * constant_from!(1u64 << (8 * x))
                    }
                })
                .reduce(|acc, x| acc + x)
                .unwrap()
        };
   } */
    pub open spec fn compose_u32_helper (col: Column, i: int) -> int {
	val(col,i+1) + val(col, i+2)*(1u64<<8) + val(col,i+3)*(1u64<<16) + val(col,i+4)*(1u64<<24)
    }

    /* macro_rules! acc_u32_helper {
                ($col:expr) => {
                    (0..4)
                        .into_iter()
                         .map(|x| (nextn!(meta, $col, 1 + x)))
                        .reduce(|acc, x| acc + x)
                        .unwrap()
                };
            }
     */
    pub open spec fn acc_u32_helper (col: Column, i: int) -> int {
	val(col,i+1) + val(col,i+2) + val(col,i+3) + val(col,i+4)
    }

    /* 
            macro_rules! compose_u32 {
                ($col:ident) => {
                    fixed_curr!(meta, u32_sel) * (compose_u32_helper!($col) - curr!(meta, $col))
                };
            }
     */
    pub open spec fn compose_u32(col: Column, i:int) -> int {
	val(u32_sel,i) * (compose_u32_helper(col,i) - val(col,i))
    }

    /*
    
                macro_rules! compose_u32_if_bit {
                ($col:ident) => {
                    compose_u32!($col) * is_bit.clone()
                };
            }
     */
    pub open spec fn compose_u32_if_bit(col: Column, i:int) -> int {
	compose_u32(col,i) * (1-val(helper,i))
    }

    /*    macro_rules! acc_u32_if_popcnt {
                ($col:ident) => {
                    fixed_curr!(meta, u32_sel)
                        * (acc_u32_helper!($col) - curr!(meta, $col))
                        * is_popcnt
                };
     */
    pub open spec fn acc_u32_if_popcnt(col: Column, i:int) -> int {
	val(u32_sel,i) * (acc_u32_helper(col,i) - val(col,i)) * val(helper,i)
    }

    /*
            macro_rules! compose_u64 {
                ($col: expr) => {
                    fixed_curr!(meta, block_sel)
                        * (prev!(meta, $col)
                            - curr!(meta, $col)
                            - nextn!(meta, $col, 5) * constant_from!(1u64 << 32))
                };
            }

            macro_rules! compose_u64_if_bit {
                ($col: expr) => {
                    compose_u64!($col) * is_bit.clone()
                };
            }

            macro_rules! acc_u64_if_popcnt {
                ($col: expr) => {
                    fixed_curr!(meta, block_sel)
                        * is_popcnt
                        * (prev!(meta, $col) - curr!(meta, $col) - nextn!(meta, $col, 5))
                };
            }
     */
    pub open spec fn compose_u64(col: Column, i:int) -> int {
	val(block_sel,i) * (val(col,i-1) - val(col,i) - val(col,i+5)*(1u64<<32))
    }

    pub open spec fn compose_u64_if_bit(col:Column, i:int) -> int {
	compose_u64(col,i) * (1-val(helper,i))
    }

    pub open spec fn acc_u64_if_popcnt(col:Column, i:int) -> int {
	val(block_sel,i)
	    * val(helper,i)
	    * (val(col,i-1) - val(col,i) - val(col,i+5))
    }

    pub axiom fn gate_2_1 (i:int)
	ensures compose_u32(left,i) == 0
    ;

    pub axiom fn gate_2_2 (i:int)
	ensures compose_u32(right,i) == 0
    ;

    pub axiom fn gate_2_3 (i:int)
	ensures compose_u32_if_bit(result,i) == 0
    ;

    pub axiom fn gate_2_4 (i:int)
	ensures acc_u32_if_popcnt(result,i) == 0
    ;

    pub axiom fn gate_3_1 (i:int)
	ensures compose_u64(left,i) == 0
    ;

    pub axiom fn gate_3_2 (i:int)
	ensures compose_u64(right,i) == 0
    ;

    pub axiom fn gate_3_3 (i:int)
	ensures compose_u64_if_bit(result,i) == 0
    ;

    pub axiom fn gate_3_4 (i:int)
	ensures acc_u64_if_popcnt(result,i) == 0
    ;


    // Axioms about lookups into the RTable. In the full zkWasm Rocq verification, these are proven in the RTable.v proofs.

    
    pub broadcast axiom fn bitop_and (i:int)
	requires    val(lookup_sel,i)==1
	         && (#[trigger] val(op,i))==(#[trigger] BitOp_And)
	ensures     val(result,i) as u8 == (val(left,i) as u8)&(val(right,i) as u8)
    ;

    pub broadcast axiom fn bitop_or (i:int)
	requires    val(lookup_sel,i)==1
	         && (#[trigger] val(op,i))==(#[trigger] BitOp_Or)
	ensures     val(result,i) as u8 == (val(left,i) as u8)|(val(right,i) as u8)
    ;

    pub broadcast axiom fn bitop_xor (i:int)
	requires    val(lookup_sel,i)==1
	         && (#[trigger] val(op,i))==(#[trigger] BitOp_Xor)
	ensures     val(result,i) as u8 == (val(left,i) as u8)^(val(right,i) as u8)
    ;


    pub broadcast axiom fn bitop_popcnt (i:int)
	requires    val(lookup_sel,i)==1
	         && (#[trigger] val(op,i))==(#[trigger]Popcnt_index)
	ensures     val(result,i) as u8 == popcnt(val(left,i) as u8 as u64)
    ;
    
    pub broadcast axiom fn lookup_bounded_u8 (i:int)
	requires (#[trigger] val(lookup_sel,i))==1
	ensures     val(left,i)==val(left,i) as u8 as int
                 && val(right,i)==val(right,i) as u8 as int
                 && val(result,i)==val(result,i) as u8 as int
    ;
			  
    
}    
