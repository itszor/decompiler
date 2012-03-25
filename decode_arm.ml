open Insn

exception Bad_condition_code of int

let cond_of_code = function
    0b0000 -> Some Eq
  | 0b0001 -> Some Ne
  | 0b0010 -> Some Cs
  | 0b0011 -> Some Cc
  | 0b0100 -> Some Mi
  | 0b0101 -> Some Pl
  | 0b0110 -> Some Vs
  | 0b0111 -> Some Vc
  | 0b1000 -> Some Hi
  | 0b1001 -> Some Ls
  | 0b1010 -> Some Ge
  | 0b1011 -> Some Lt
  | 0b1100 -> Some Gt
  | 0b1101 -> Some Le
  | 0b1110 -> None
  | x -> raise (Bad_condition_code x)

let bad_insn =
  { opcode = BAD;
    write_operands = [| |];
    read_operands = [| |];
    condition = None }

(* Decode 28 remaining bits of NV space.  *)
let decode_nv_space ibits =
  bad_insn

let decode_movw cond ibits =
  bad_insn

let decode_movt cond ibits =
  bad_insn

let decode_msr_and_hints cond op1 rest =
  bad_insn

let decode_dp_imm cond op1 rest =
  bad_insn

let decode_misc cond op1 bits19_8 op2 bits3_0 =
  bad_insn

let decode_halfword_mul_mac cond op1 bints19_8 op2 bits3_0 =
  bad_insn

let decode_mul_mac cond op1 bits19_8 bits3_0 =
  bad_insn

let decode_sync cond op1 bits19_8 bits3_0 =
  bad_insn

let decode_extra_ld_st ~unpriv cond op1 bits19_8 bits3_0 =
  bad_insn

let decode_dp_reg cond bits24_0 =
  bad_insn

let decode_dp_reg_shifted_reg cond op1 bits19_8 op2 bits3_0 =
  bad_insn

(* Decode 32 bits of data-processing & media instructions.  *)
let decode_dp_misc cond ibits =
  bitmatch ibits with
    { _ : 4;
      0b001 : 3;
      op1 : 5 : bitstring;
      rest : 20 : bitstring } ->
        (bitmatch op1 with
	  { 0b10000 : 5 : littleendian } -> decode_movw cond rest
	| { 0b10100 : 5 : littleendian } -> decode_movt cond rest
	| { (0b10010 | 0b10110) : 5 : littleendian } ->
	  decode_msr_and_hints cond op1 rest
	| { _ } -> decode_dp_imm cond op1 rest)
  | { _ : 4;
      0b000 : 3;
      op1 : 5 : bitstring;
      bits19_8 : 12 : bitstring;
      op2 : 4 : bitstring;
      bits3_0 : 4 : bitstring } ->
        let bits24_0 = Bitstring.concat [op1; bits19_8; op2; bits3_0] in
        (bitmatch (Bitstring.concat [op1; op2]) with
	  { 0b10 : 2; _ : 2; false : 1;
	    false : 1; _ : 3 } ->
	    decode_misc cond op1 bits19_8 op2 bits3_0
	| { 0b10 : 2; _ : 2; false : 1;
	    true : 1; _ : 2; false : 1 } ->
	    decode_halfword_mul_mac cond op1 bits19_8 op2 bits3_0
        | { false : 1; _ : 4;
	    0b1001 : 4 } -> decode_mul_mac cond op1 bits19_8 bits3_0
	| { true : 1; _ : 4;
	    0b1001 : 4 } -> decode_sync cond op1 bits19_8 bits3_0
	| { false : 1; _ : 2; true : 1; _ : 1;
	    (0b1011 | 0b1101 | 0b1111) : 4 } ->
	    decode_extra_ld_st ~unpriv:true cond op1 bits19_8 bits3_0
	| { _ : 5;
	    (0b1011 | 0b1101 | 0b1111) : 4 } ->
	    decode_extra_ld_st ~unpriv:false cond op1 bits19_8 bits3_0
	| { _ : 5;
	    _ : 3; false : 1 } -> decode_dp_reg cond bits24_0
	| { _ : 5;
	    false : 1; _ : 2; true : 1 } ->
	    decode_dp_reg_shifted_reg cond op1 bits19_8 op2 bits3_0)

let decode_insn ibits =
  bitmatch ibits with
    { 0b1111 : 4 : littleendian; rest : 28 : bitstring } ->
      decode_nv_space rest
  | { cond : 4 : littleendian;
      (0b000 | 0b001) : 3 : littleendian;
      _ : 25 : bitstring } ->
      decode_dp_misc (cond_of_code cond) ibits
  | { _ } ->
      bad_insn
  
let decode_insns ibits num_insns =
  let rec scan acc ibits insns_left =
    if insns_left = 0 then
      (List.rev acc), ibits
    else
      bitmatch ibits with
        { insn : 32 : bitstring;
	  rest : -1 : bitstring } ->
          let decoded_insn = decode_insn insn in
	  scan (decoded_insn :: acc) rest (pred insns_left)
      | { bad : -1 : bitstring } -> scan acc bad 0 in
  scan [] ibits num_insns
