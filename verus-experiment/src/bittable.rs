use vstd::prelude::*;

mod bittable_model;
use bittable_model::*;

verus!{    
    broadcast proof fn op_preserved(i : int) by (nonlinear_arith)
	ensures (val(u32_sel,i) + val(lookup_sel, i) != 0) ==>
                 ((#[trigger] val(op,i)) == val(op, i-1))

    {
	gate_1_1(i);
    }

    proof fn i_val (i:int) by (nonlinear_arith)
	requires val(block_sel,i+1)==1
	ensures (i-bit_table_start)%STEP_SIZE == 0
    {
	block_sel_spec(i+1);
    }

    proof fn is_block_values (i:int) by (nonlinear_arith)
	requires val(block_sel,i+1)==1
	ensures  val(block_sel,i)==0
	      && val(block_sel,i+2)==0
	      && val(block_sel,i+3)==0
	      && val(block_sel,i+4)==0
	      && val(block_sel,i+5)==0
	      && val(block_sel,i+6)==0
	      && val(block_sel,i+7)==0
	      && val(block_sel,i+8)==0
	      && val(block_sel,i+9)==0
	      && val(block_sel,i+10)==0
    {
	i_val(i);
	broadcast use block_sel_spec;
    }

    proof fn is_u32_values (i:int)
	requires val(block_sel,i+1)==1
	ensures  val(u32_sel,i)==0
	      && val(u32_sel,i+1)==1
	      && val(u32_sel,i+2)==0
	      && val(u32_sel,i+3)==0
	      && val(u32_sel,i+4)==0
	      && val(u32_sel,i+5)==0
	      && val(u32_sel,i+6)==1
	      && val(u32_sel,i+7)==0
	      && val(u32_sel,i+8)==0
	      && val(u32_sel,i+9)==0
	      && val(u32_sel,i+10)==0
    {
	i_val(i);
	broadcast use u32_sel_spec;
    }
    
    proof fn is_lookup_values (i:int)
	requires val(block_sel,i+1)==1
	ensures  val(lookup_sel,i)==0
	      && val(lookup_sel,i+1)==0
	      && val(lookup_sel,i+2)==1
	      && val(lookup_sel,i+3)==1
	      && val(lookup_sel,i+4)==1
	      && val(lookup_sel,i+5)==1
	      && val(lookup_sel,i+6)==0
	      && val(lookup_sel,i+7)==1
	      && val(lookup_sel,i+8)==1
	      && val(lookup_sel,i+9)==1
	      && val(lookup_sel,i+10)==1
    {
	i_val(i);
	broadcast use lookup_sel_spec;
    }

    broadcast use lookup_bounded_u8;
    

    proof fn is_op_values (i:int)
	requires val(block_sel,i+1)==1
	ensures    val(op,i+1)==val(op,i)
	        && val(op,i+2)==val(op,i)
	        && val(op,i+3)==val(op,i)
	        && val(op,i+4)==val(op,i)
	        && val(op,i+5)==val(op,i)
	        && val(op,i+6)==val(op,i)
	        && val(op,i+7)==val(op,i)
	        && val(op,i+8)==val(op,i)
	        && val(op,i+9)==val(op,i)
	        && val(op,i+10)==val(op,i)
    {
	is_u32_values(i);
	is_lookup_values(i);
	broadcast use op_preserved;
    }

    
    proof fn compose_l_1 (i:int)
	requires val(block_sel,i+1)==1
	ensures  val(left,i+1) ==
	         val(left,i+2)
    	         + val(left, i+3) * (1u64<<8)
                 + val(left, i+4) * (1u64<<16)
                 + val(left, i+5) * (1u64<<24)
    {
	is_u32_values(i);
	is_lookup_values(i);
	gate_2_1(i+1);
    }

    proof fn compose_l_6 (i:int)
	requires val(block_sel,i+1)==1
	ensures  val(left,i+6) ==
	         val(left,i+7)
    	         + val(left, i+8) * (1u64<<8)
                 + val(left, i+9) * (1u64<<16)
                 + val(left, i+10) * (1u64<<24)
    {
	is_u32_values(i);
	is_lookup_values(i);
	gate_2_1(i+6);
    }

    proof fn compose_l_0 (i:int)
	requires val(block_sel,i+1)==1
	ensures  val(left,i) ==
	         val(left,i+1) + val(left,i+6)*(1u64<<32)
    {
	is_u32_values(i);
	is_lookup_values(i);
	gate_3_1(i+1);
    }
    
    
    proof fn compose_r_1 (i:int)
	requires val(block_sel,i+1)==1
	ensures  val(right,i+1) ==
	         val(right,i+2)
    	         + val(right, i+3) * (1u64<<8)
                 + val(right, i+4) * (1u64<<16)
                 + val(right, i+5) * (1u64<<24)
    {
	is_u32_values(i);
	is_lookup_values(i);
	gate_2_2(i+1);
    }

    proof fn compose_r_6 (i:int)
	requires val(block_sel,i+1)==1
	ensures  val(right,i+6) ==
	         val(right,i+7)
    	         + val(right, i+8) * (1u64<<8)
                 + val(right, i+9) * (1u64<<16)
                 + val(right, i+10) * (1u64<<24)
    {
	is_u32_values(i);
	is_lookup_values(i);
	gate_2_2(i+6);
    }

    proof fn compose_r_0 (i:int)
	requires val(block_sel,i+1)==1
	ensures  val(right,i) ==
	         val(right,i+1) + val(right,i+6)*(1u64<<32)
    {
	is_u32_values(i);
	is_lookup_values(i);
	gate_3_2(i+1);
    }

    
    proof fn l_0_spec (i:int)
	requires val(block_sel,i+1)==1
	ensures  val(left,i) ==
	           val(left,i+2)
	         + val(left,i+3)*(1u64<<8)
	         + val(left,i+4)*(1u64<<16)
	         + val(left,i+5)*(1u64<<24)
	         + val(left,i+7)*(1u64<<32)
	         + val(left,i+8)*(1u64<<40)
	         + val(left,i+9)*(1u64<<48)
  	         + val(left,i+10)*(1u64<<56)
    {
	is_lookup_values(i);

	let val2 = val(left,i+2) as u8;
	let val3 = val(left,i+3) as u8;
	let val4 = val(left,i+4) as u8;
	let val5 = val(left,i+5) as u8;
	let val7 = val(left,i+7) as u8;
	let val8 = val(left,i+8) as u8;
	let val9 = val(left,i+9) as u8;
	let val10 = val(left,i+10) as u8;
	
	assert((val7
    	         + val8 * (1u64<<8)
                 + val9 * (1u64<<16)
                + val10 * (1u64<<24))*(1u64<<32)
	       == (val7*(1u64<<32)
	         + val8*(1u64<<40)
	         + val9*(1u64<<48)
  	           + val10*(1u64<<56)))
	    by (bit_vector);

	compose_l_0(i);
	compose_l_1(i);
	compose_l_6(i); 
    }

    proof fn r_0_spec (i:int)
	requires val(block_sel,i+1)==1
	ensures  val(right,i) ==
	           val(right,i+2)
	         + val(right,i+3)*(1u64<<8)
	         + val(right,i+4)*(1u64<<16)
	         + val(right,i+5)*(1u64<<24)
	         + val(right,i+7)*(1u64<<32)
	         + val(right,i+8)*(1u64<<40)
	         + val(right,i+9)*(1u64<<48)
  	         + val(right,i+10)*(1u64<<56)
    {
	is_lookup_values(i);

	let val2 = val(right,i+2) as u8;
	let val3 = val(right,i+3) as u8;
	let val4 = val(right,i+4) as u8;
	let val5 = val(right,i+5) as u8;
	let val7 = val(right,i+7) as u8;
	let val8 = val(right,i+8) as u8;
	let val9 = val(right,i+9) as u8;
	let val10 = val(right,i+10) as u8;
	
	assert((val7
    	         + val8 * (1u64<<8)
                 + val9 * (1u64<<16)
                + val10 * (1u64<<24))*(1u64<<32)
	       == (val7*(1u64<<32)
	         + val8*(1u64<<40)
	         + val9*(1u64<<48)
  	           + val10*(1u64<<56)))
	    by (bit_vector);

	compose_r_0(i);
	compose_r_1(i);
	compose_r_6(i); 
    }


    proof fn add_lemma (x2 : int, x3:int, x4:int, x5:int, x7:int, x8:int, x9:int, x10:int)
	requires     x2 == x2 as u8 as int
                  && x3 == x3 as u8 as int
                  && x4 == x4 as u8 as int
                  && x5 == x5 as u8 as int
                  && x7 == x7 as u8 as int
                  && x8 == x8 as u8 as int
                  && x9 == x9 as u8 as int
                  && x10 == x10 as u8 as int
	ensures
	           x2
	         + x3*(1u64<<8)
	         + x4*(1u64<<16)
	         + x5*(1u64<<24)
	         + x7*(1u64<<32)
	         + x8*(1u64<<40)
	         + x9*(1u64<<48)
  	         + x10*(1u64<<56)
	 ==     add(add(add(add(add(add(add((x2 as u8 as u64),
	                   ((x3 as u8 as u64)<<8u64)),
			   (x4 as u8 as u64)<<16u64),
			   (x5 as u8 as u64)<<24u64),
	                   (x7 as u8 as u64)<<32u64),
		           (x8 as u8 as u64)<<40u64),
	                   (x9 as u8 as u64)<<48u64),
  	                   (x10 as u8 as u64)<<56u64)
   {
       let x2u : u64 = x2 as u8 as u64;
       let x3u : u64 = x3 as u8 as u64;
       let x4u : u64 = x4 as u8 as u64;
       let x5u : u64 = x5 as u8 as u64;
       let x7u : u64 = x7 as u8 as u64;
       let x8u : u64 = x8 as u8 as u64;
       let x9u : u64 = x9 as u8 as u64;
       let x10u : u64 = x10 as u8 as u64;

       assert(((x3u) << 8u64) ==  ((x3u)*(1u64<<8u64))) by (bit_vector) requires (x3u < 256) ;
       assert(((x4u) << 16u64) ==  ((x4u)*(1u64<<16u64))) by (bit_vector) requires (x4u < 256) ;
       assert(((x5u) << 24u64) ==  ((x5u)*(1u64<<24u64))) by (bit_vector) requires (x5u < 256) ;
       assert(((x7u) << 32u64) ==  ((x7u)*(1u64<<32u64))) by (bit_vector) requires (x7u < 256) ;
       assert(((x8u) << 40u64) ==  ((x8u)*(1u64<<40u64))) by (bit_vector) requires (x8u < 256) ;
       assert(((x9u) << 48u64) ==  ((x9u)*(1u64<<48u64))) by (bit_vector) requires (x9u < 256) ;
       assert(((x10u) << 56u64) ==  ((x10u)*(1u64<<56u64))) by (bit_vector) requires (x10u < 256) ;

       assert((	   x2u
	         + x3u*(1u64<<8)
	         + x4u*(1u64<<16)
	         + x5u*(1u64<<24)
	         + x7u*(1u64<<32)
	         + x8u*(1u64<<40)
	         + x9u*(1u64<<48)
  	         + x10u*(1u64<<56)
	 ==     add(add(add(add(add(add(add((x2u),
	                   ((x3u)<<8u64)),
			   (x4u)<<16u64),
			   (x5u)<<24u64),
	                   (x7u)<<32u64),
		           (x8u)<<40u64),
	                   (x9u)<<48u64),
                    (x10u)<<56u64)))
	    by (bit_vector)
	requires
	    x2u < 256, x3u < 256, x4u < 256, x5u < 256, x7u < 256, x8u < 256, x9u < 256, x10u < 256;
    }
    
    proof fn is_popcnt_false (i:int)  by (nonlinear_arith)
	requires    val(u32_sel,i)==1
	         && val(op,i) != Popcnt_index
	ensures  val(helper,i) == 0
    {	
	gate_1_2(i);
    }


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

    proof fn compose_res_6 (i:int)  by (nonlinear_arith)
	requires    val(block_sel,i+1)==1
	         && val(op,i) != Popcnt_index
	ensures  val(result,i+6)
	         ==
	         val(result,i+7)
                 + val(result,i+8)*(1u64<<8)
	         + val(result,i+9)*(1u64<<16)
	         + val(result,i+10)*(1u64<<24)
    {
	is_u32_values(i);
	is_lookup_values(i);
	is_op_values(i);
	is_popcnt_false(i+6);	
	gate_2_3(i+6);
    }

    proof fn compose_res_0 (i:int)  by (nonlinear_arith)
	requires    val(block_sel,i+1)==1
	         && val(op,i) != Popcnt_index
	ensures  val(result,i)
	         ==
	         val(result,i+1)
	         + val(result,i+6)*(1u64<<32)
    {
	is_u32_values(i);
	is_lookup_values(i);
	is_op_values(i);
	is_popcnt_false(i+1);		
	gate_3_3(i+1);
    }

    proof fn is_popcnt_true (i:int)  by (nonlinear_arith)
	requires    val(u32_sel,i)==1
	         && val(op,i) == Popcnt_index
	ensures  val(helper,i) == 1
    {
	gate_1_3(i);
    }

    
    proof fn compose_res_1_popcnt (i:int)  by (nonlinear_arith)
	requires    val(block_sel,i+1)==1
	         && val(op,i) == Popcnt_index
	ensures  val(result,i+1)
	         ==
	         val(result,i+2)
                 + val(result,i+3)
	         + val(result,i+4)
	         + val(result,i+5)
    {
	is_u32_values(i);
	is_lookup_values(i);
	is_op_values(i);
	is_popcnt_true(i+1);
	gate_2_4(i+1);
    }

    proof fn compose_res_6_popcnt (i:int)  by (nonlinear_arith)
	requires    val(block_sel,i+1)==1
	         && val(op,i) == Popcnt_index
	ensures  val(result,i+6)
	         ==
	         val(result,i+7)
                 + val(result,i+8)
	         + val(result,i+9)
	         + val(result,i+10)
    {
	is_u32_values(i);
	is_lookup_values(i);
	is_op_values(i);
	is_popcnt_true(i+6);	
	gate_2_4(i+6);
    }

    proof fn compose_res_0_popcnt (i:int)  by (nonlinear_arith)
	requires    val(block_sel,i+1)==1
	         && val(op,i) == Popcnt_index
	ensures  val(result,i)
	         ==
	         val(result,i+1)
	         + val(result,i+6)
    {
	is_u32_values(i);
	is_lookup_values(i);
	is_op_values(i);
	is_popcnt_true(i+1);		
	gate_3_4(i+1);
    }

    proof fn res_0_spec_popcnt (i:int)
	requires val(block_sel,i+1)==1
	         && val(op,i) == Popcnt_index
	ensures  val(result,i) ==
	                  (val(result,i+2) as u8)
   	                  + (val(result,i+3) as u8)
			  + (val(result,i+4) as u8)
			  + (val(result,i+5) as u8)
	                  + (val(result,i+7) as u8)
		          + (val(result,i+8) as u8)
	                  + (val(result,i+9) as u8)
  	                  + (val(result,i+10)as u8)
    {
	compose_res_1_popcnt(i);
	compose_res_6_popcnt(i);
	compose_res_0_popcnt(i);
	is_lookup_values(i);
    }
    
    proof fn res_0_spec (i:int) 
	requires val(block_sel,i+1)==1
	           && val(op,i) != Popcnt_index
	ensures  val(result,i) ==
	           val(result,i+2)
	         + val(result,i+3)*(1u64<<8)
	         + val(result,i+4)*(1u64<<16)
	         + val(result,i+5)*(1u64<<24)
	         + val(result,i+7)*(1u64<<32)
	         + val(result,i+8)*(1u64<<40)
	         + val(result,i+9)*(1u64<<48)
  	         + val(result,i+10)*(1u64<<56)
    {
	is_lookup_values(i);
	
	let val2 = val(result,i+2) as u8;
	let val3 = val(result,i+3) as u8;
	let val4 = val(result,i+4) as u8;
	let val5 = val(result,i+5) as u8;
	let val7 = val(result,i+7) as u8;
	let val8 = val(result,i+8) as u8;
	let val9 = val(result,i+9) as u8;
	let val10 = val(result,i+10) as u8;
	
	assert((val7
    	         + val8 * (1u64<<8)
                 + val9 * (1u64<<16)
                + val10 * (1u64<<24))*(1u64<<32)
	       == (val7*(1u64<<32)
	         + val8*(1u64<<40)
	         + val9*(1u64<<48)
  	           + val10*(1u64<<56)))
	    by (bit_vector);

	compose_res_0(i);
	compose_res_1(i);
	compose_res_6(i); 
    }

    proof fn bitop_and_spec (i:int) 
	requires val(block_sel,i+1)==1
	           && val(op,i)==BitOp_And
	ensures  val(result,i) == (val(left,i) as u64) & (val(right,i) as u64)
    {
	is_lookup_values(i);
	is_op_values(i);
	broadcast use bitop_and;

	l_0_spec(i);
	add_lemma(val(left,i+2), val(left,i+3), val(left,i+4), val(left,i+5), val(left,i+7), val(left,i+8), val(left,i+9), val(left,i+10));
	r_0_spec(i);
	add_lemma(val(right,i+2), val(right,i+3), val(right,i+4), val(right,i+5), val(right,i+7), val(right,i+8), val(right,i+9), val(right,i+10));
	res_0_spec(i);
	add_lemma(val(result,i+2), val(result,i+3), val(result,i+4), val(result,i+5), val(result,i+7), val(result,i+8), val(result,i+9), val(result,i+10));


	let l2 = val(left,i+2) as u8;
	let l3 = val(left,i+3) as u8;
	let l4 = val(left,i+4) as u8;
	let l5 = val(left,i+5) as u8;
	let l7 = val(left,i+7) as u8;
	let l8 = val(left,i+8) as u8;
	let l9 = val(left,i+9) as u8;
	let l10 = val(left,i+10) as u8;
	
	let r2 = val(right,i+2) as u8;
	let r3 = val(right,i+3) as u8;
	let r4 = val(right,i+4) as u8;
	let r5 = val(right,i+5) as u8;
	let r7 = val(right,i+7) as u8;
	let r8 = val(right,i+8) as u8;
	let r9 = val(right,i+9) as u8;
	let r10 = val(right,i+10) as u8;
	
	let res2 = val(result,i+2) as u8;
	let res3 = val(result,i+3) as u8;
	let res4 = val(result,i+4) as u8;
	let res5 = val(result,i+5) as u8;
	let res7 = val(result,i+7) as u8;
	let res8 = val(result,i+8) as u8;
	let res9 = val(result,i+9) as u8;
	let res10 = val(result,i+10) as u8;

	assert ((  add(add(add(add(add(add(add((l2 as u64), ((l3 as u64)<<8u64)), ((l4 as u64)<<16u64)), ((l5 as u64)<<24u64)), ((l7 as u64)<<32u64)), ((l8 as u64)<<40u64)), ((l9 as u64)<<48u64)), ((l10 as u64)<<56u64)))
	       &(  add(add(add(add(add(add(add((r2 as u64), ((r3 as u64)<<8u64)), ((r4 as u64)<<16u64)), ((r5 as u64)<<24u64)), ((r7 as u64)<<32u64)), ((r8 as u64)<<40u64)), ((r9 as u64)<<48u64)), ((r10 as u64)<<56u64)))
	       == (  add(add(add(add(add(add(add(((l2 as u64)&(r2 as u64)), (((l3 as u64)&(r3 as u64))<<8u64)), (((l4 as u64)&(r4 as u64))<<16u64)), (((l5 as u64)&(r5 as u64))<<24u64)), (((l7 as u64)&(r7 as u64))<<32u64)), (((l8 as u64)&(r8 as u64))<<40u64)),(((l9 as u64)&(r9 as u64))<<48u64)), (((l10 as u64)&(r10 as u64))<<56u64))))
	    by (bit_vector);

    }

    proof fn bitop_or_spec (i:int) 
	requires val(block_sel,i+1)==1
	           && val(op,i)==BitOp_Or
	ensures  val(result,i) == (val(left,i) as u64) | (val(right,i) as u64)
    {
	is_lookup_values(i);
	is_op_values(i);
	broadcast use bitop_or;

	l_0_spec(i);
	add_lemma(val(left,i+2), val(left,i+3), val(left,i+4), val(left,i+5), val(left,i+7), val(left,i+8), val(left,i+9), val(left,i+10));
	r_0_spec(i);
	add_lemma(val(right,i+2), val(right,i+3), val(right,i+4), val(right,i+5), val(right,i+7), val(right,i+8), val(right,i+9), val(right,i+10));
	res_0_spec(i);
	add_lemma(val(result,i+2), val(result,i+3), val(result,i+4), val(result,i+5), val(result,i+7), val(result,i+8), val(result,i+9), val(result,i+10));

	let l2 = val(left,i+2) as u8;
	let l3 = val(left,i+3) as u8;
	let l4 = val(left,i+4) as u8;
	let l5 = val(left,i+5) as u8;
	let l7 = val(left,i+7) as u8;
	let l8 = val(left,i+8) as u8;
	let l9 = val(left,i+9) as u8;
	let l10 = val(left,i+10) as u8;
	
	let r2 = val(right,i+2) as u8;
	let r3 = val(right,i+3) as u8;
	let r4 = val(right,i+4) as u8;
	let r5 = val(right,i+5) as u8;
	let r7 = val(right,i+7) as u8;
	let r8 = val(right,i+8) as u8;
	let r9 = val(right,i+9) as u8;
	let r10 = val(right,i+10) as u8;
	
	let res2 = val(result,i+2) as u8;
	let res3 = val(result,i+3) as u8;
	let res4 = val(result,i+4) as u8;
	let res5 = val(result,i+5) as u8;
	let res7 = val(result,i+7) as u8;
	let res8 = val(result,i+8) as u8;
	let res9 = val(result,i+9) as u8;
	let res10 = val(result,i+10) as u8;


	assert ((  add(add(add(add(add(add(add((l2 as u64), ((l3 as u64)<<8u64)), ((l4 as u64)<<16u64)), ((l5 as u64)<<24u64)), ((l7 as u64)<<32u64)), ((l8 as u64)<<40u64)), ((l9 as u64)<<48u64)), ((l10 as u64)<<56u64)))
	       |(  add(add(add(add(add(add(add((r2 as u64), ((r3 as u64)<<8u64)), ((r4 as u64)<<16u64)), ((r5 as u64)<<24u64)), ((r7 as u64)<<32u64)), ((r8 as u64)<<40u64)), ((r9 as u64)<<48u64)), ((r10 as u64)<<56u64)))
	       == (  add(add(add(add(add(add(add(((l2 as u64)|(r2 as u64)), (((l3 as u64)|(r3 as u64))<<8u64)), (((l4 as u64)|(r4 as u64))<<16u64)), (((l5 as u64)|(r5 as u64))<<24u64)), (((l7 as u64)|(r7 as u64))<<32u64)), (((l8 as u64)|(r8 as u64))<<40u64)),(((l9 as u64)|(r9 as u64))<<48u64)), (((l10 as u64)|(r10 as u64))<<56u64))))
	    by (bit_vector);
    }

    proof fn bitop_xor_spec (i:int) 
	requires val(block_sel,i+1)==1
	           && val(op,i)==BitOp_Xor
	ensures  val(result,i) == (val(left,i) as u64) ^ (val(right,i) as u64)
    {
	is_lookup_values(i);
	is_op_values(i);
	broadcast use bitop_xor;

	l_0_spec(i);
	add_lemma(val(left,i+2), val(left,i+3), val(left,i+4), val(left,i+5), val(left,i+7), val(left,i+8), val(left,i+9), val(left,i+10));
	r_0_spec(i);
	add_lemma(val(right,i+2), val(right,i+3), val(right,i+4), val(right,i+5), val(right,i+7), val(right,i+8), val(right,i+9), val(right,i+10));
	res_0_spec(i);
	add_lemma(val(result,i+2), val(result,i+3), val(result,i+4), val(result,i+5), val(result,i+7), val(result,i+8), val(result,i+9), val(result,i+10));

	let l2 = val(left,i+2) as u8;
	let l3 = val(left,i+3) as u8;
	let l4 = val(left,i+4) as u8;
	let l5 = val(left,i+5) as u8;
	let l7 = val(left,i+7) as u8;
	let l8 = val(left,i+8) as u8;
	let l9 = val(left,i+9) as u8;
	let l10 = val(left,i+10) as u8;
	
	let r2 = val(right,i+2) as u8;
	let r3 = val(right,i+3) as u8;
	let r4 = val(right,i+4) as u8;
	let r5 = val(right,i+5) as u8;
	let r7 = val(right,i+7) as u8;
	let r8 = val(right,i+8) as u8;
	let r9 = val(right,i+9) as u8;
	let r10 = val(right,i+10) as u8;
	
	let res2 = val(result,i+2) as u8;
	let res3 = val(result,i+3) as u8;
	let res4 = val(result,i+4) as u8;
	let res5 = val(result,i+5) as u8;
	let res7 = val(result,i+7) as u8;
	let res8 = val(result,i+8) as u8;
	let res9 = val(result,i+9) as u8;
	let res10 = val(result,i+10) as u8;

	assert ((  add(add(add(add(add(add(add((l2 as u64), ((l3 as u64)<<8u64)), ((l4 as u64)<<16u64)), ((l5 as u64)<<24u64)), ((l7 as u64)<<32u64)), ((l8 as u64)<<40u64)), ((l9 as u64)<<48u64)), ((l10 as u64)<<56u64)))
	       ^(  add(add(add(add(add(add(add((r2 as u64), ((r3 as u64)<<8u64)), ((r4 as u64)<<16u64)), ((r5 as u64)<<24u64)), ((r7 as u64)<<32u64)), ((r8 as u64)<<40u64)), ((r9 as u64)<<48u64)), ((r10 as u64)<<56u64)))
	       == (  add(add(add(add(add(add(add(((l2 as u64)^(r2 as u64)), (((l3 as u64)^(r3 as u64))<<8u64)), (((l4 as u64)^(r4 as u64))<<16u64)), (((l5 as u64)^(r5 as u64))<<24u64)), (((l7 as u64)^(r7 as u64))<<32u64)), (((l8 as u64)^(r8 as u64))<<40u64)),(((l9 as u64)^(r9 as u64))<<48u64)), (((l10 as u64)^(r10 as u64))<<56u64))))
	    by (bit_vector);

    }

    proof fn bitop_popcnt_spec (i:int) 
	requires val(block_sel,i+1)==1
	           && val(op,i)==Popcnt_index 
	ensures  val(result,i) == popcnt(val(left,i) as u64) 
    {
	is_lookup_values(i);
	is_op_values(i);
	broadcast use bitop_popcnt;

	l_0_spec(i);
	add_lemma(val(left,i+2), val(left,i+3), val(left,i+4), val(left,i+5), val(left,i+7), val(left,i+8), val(left,i+9), val(left,i+10));
	res_0_spec_popcnt(i);

	let l2 = val(left,i+2) as u8;
	let l3 = val(left,i+3) as u8;
	let l4 = val(left,i+4) as u8;
	let l5 = val(left,i+5) as u8;
	let l7 = val(left,i+7) as u8;
	let l8 = val(left,i+8) as u8;
	let l9 = val(left,i+9) as u8;
	let l10 = val(left,i+10) as u8;
	
	assert(
	    popcnt(add(add(add(add(add(add(add(l2 as u64, ((l3 as u64)<<8u64)), ((l4 as u64)<<16u64)), ((l5 as u64)<<24u64)), ((l7 as u64)<<32u64)), ((l8 as u64)<<40u64)), ((l9 as u64)<<48u64)), ((l10 as u64)<<56u64)))
		== popcnt(l2 as u64) + popcnt(l3 as u64) + popcnt(l4 as u64) + popcnt(l5 as u64) + popcnt(l7 as u64) + popcnt(l8 as u64) + popcnt(l9 as u64) + popcnt(l10 as u64))
	    by (bit_vector);
	
    }
    
fn main() {
}

} // verus!
