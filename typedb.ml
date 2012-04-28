module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

type infotag =
    Used_as_addr of CT.mem
  | Loaded_pc_rel
  | Type_known of ctype
  | Byte_loads
  | Signed_byte_loads
  | Byte_stores
  | Halfword_loads
  | Signed_halfword_loads
  | Halfword_stores
  | Word_loads
  | Word_stores
  | Code_pointer

and implication =
    Int
  | Pointer
    (* In (reg, type, implied_type), if REG is TYPE, we have type
       IMPLIED_TYPE.  *)
  | Unary_imp of ssa_reg_id * implication * implication
    (* Similar, but (reg1, type1, reg2, type2, implied type), and both
       reg1/type1 and reg2/type2 must be true for implied type to be true.  *)
  | Binary_imp of ssa_reg_id * implication * ssa_reg_id * implication
		  * implication
  | One_of of implication list

and ctype =
    C_void
  | C_int
  | C_short
  | C_char
  | C_signed of ctype
  | C_unsigned of ctype
  | C_pointer of ctype
  | C_const of ctype

and ssa_reg_id = CT.reg * int

let string_of_ssa_reg reg num =
  Printf.sprintf "%s_%d" (CT.string_of_reg reg) num

let record_info ht reg info =
  try
    let infos = Hashtbl.find ht reg in
    if not (List.mem info infos) then
      Hashtbl.replace ht reg (info::infos)
  with Not_found ->
    Hashtbl.add ht reg [info]

let info_of_mem_type ~load = function
    Irtypes.Word -> if load then Word_loads else Word_stores
  | Irtypes.U8 -> if load then Byte_loads else Byte_stores
  | Irtypes.U16 -> if load then Halfword_loads else Halfword_stores
  | Irtypes.S8 -> if load then Signed_byte_loads else Byte_stores
  | Irtypes.S16 -> if load then Signed_halfword_loads else Halfword_stores

let gather_info blk_arr =
  let ht = Hashtbl.create 10 in
  let impl_ht = Hashtbl.create 10 in
  Array.iter
    (fun blk ->
      CS.iter
        (fun insn ->
	  match insn with
	    C.Set (C.SSAReg (rd, rdn), C.Load (memtype,
		     C.Binary (Irtypes.Add, C.SSAReg (rb, rbn), C.Immed _)))
	  | C.Set (C.SSAReg (rd, rdn), C.Load (memtype,
		     C.SSAReg (rb, rbn))) ->
	      record_info ht (rd, rdn) (info_of_mem_type ~load:true memtype);
	      record_info ht (rb, rbn) (Used_as_addr memtype);
	      record_info impl_ht (rb, rbn) Pointer
	  | C.Store (memtype, C.Binary (Irtypes.Add,
					C.SSAReg (rb, rbn), C.Immed _),
		     C.SSAReg (rs, rsn))
	  | C.Store (memtype, C.SSAReg (rb, rbn), C.SSAReg (rs, rsn)) ->
	      record_info ht (rb, rbn) (Used_as_addr memtype);
	      record_info ht (rs, rsn) (info_of_mem_type ~load:false memtype);
	      record_info impl_ht (rb, rbn) Pointer
	  | C.Set (C.SSAReg (rd, rdn), C.Binary ((Irtypes.Add | Irtypes.Sub),
		     C.SSAReg (ra, ran), C.SSAReg (rb, rbn))) ->
	      record_info impl_ht (rd, rdn)
		(One_of
		  [Binary_imp ((ra, ran), Int, (rb, rbn), Int, Int);
		   Binary_imp ((ra, ran), Pointer, (rb, rbn), Int, Pointer);
		   Binary_imp ((ra, ran), Int, (rb, rbn), Pointer, Pointer)])
	  | C.Set (C.SSAReg (rd, rdn), C.Binary ((Irtypes.Add | Irtypes.Sub),
		    C.SSAReg (ra, ran), C.Immed _)) ->
	      record_info impl_ht (rd, rdn)
	        (One_of
		  [Unary_imp ((ra, ran), Int, Int);
		   Unary_imp ((ra, ran), Pointer, Pointer)])
	  | C.Set (C.SSAReg (rd, rdn),
		   C.Binary ((Irtypes.Mul | Irtypes.And | Irtypes.Eor
			      | Irtypes.Or),
			     C.SSAReg (ra, ran), C.SSAReg (rb, rbn))) ->
	      (* If we're doing multiplies/logic ops, the destination is
	         unlikely to be a pointer, but it's not impossible!  Maybe
		 make this more configurable.  *)
	      record_info impl_ht (rd, rdn)
	        (Binary_imp ((ra, ran), Int, (rb, rbn), Int, Int))
	  | _ -> ())
	blk.Block.code)
    blk_arr;
  ht, impl_ht

let string_of_info = function
    Used_as_addr meminfo ->
      Printf.sprintf "used as addr (%s)" (CT.string_of_mem meminfo)
  | Loaded_pc_rel -> "loaded PC-relative"
  | Type_known _ -> "type known (...)"
  | Byte_loads -> "byte loads"
  | Signed_byte_loads -> "signed byte loads"
  | Halfword_loads -> "halfword loads"
  | Signed_halfword_loads -> "signed halfword loads"
  | Halfword_stores -> "halfword stores"
  | Word_loads -> "word loads"
  | Word_stores -> "word stores"
  | Code_pointer -> "used as code pointer"

let rec string_of_implied_info = function
    Int -> "int"
  | Pointer -> "pointer"
  | Unary_imp ((reg, regn), rtyp, rimp) ->
      Printf.sprintf "%s(%s) -> %s" (string_of_ssa_reg reg regn)
	(string_of_implied_info rtyp) (string_of_implied_info rimp)
  | Binary_imp ((reg1, regn1), rtyp1, (reg2, regn2), rtyp2, rimp) ->
      Printf.sprintf "%s(%s) && %s(%s) -> %s" (string_of_ssa_reg reg1 regn1)
	(string_of_implied_info rtyp1) (string_of_ssa_reg reg2 regn2)
	(string_of_implied_info rtyp2) (string_of_implied_info rimp)
  | One_of impl_list ->
      String.concat "\n| " (List.map string_of_implied_info impl_list)

let print_info ht =
  Hashtbl.iter
    (fun (reg, regn) infolist ->
      List.iter
        (fun info ->
	  Printf.printf "%s : %s\n" (string_of_ssa_reg reg regn)
				    (string_of_info info))
	infolist)
    ht

let print_implied_info ht =
  Hashtbl.iter
    (fun (reg, regn) impllist ->
      List.iter
        (fun impl ->
	  Printf.printf "%s : %s\n" (string_of_ssa_reg reg regn)
				    (string_of_implied_info impl))
	impllist)
    ht
