open Ctype

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

(* This is a really basic kind of type information, derived by scanning
   instructions.  Attempt to tell apart values which are used as pointers
   from those which are not (scalars).  The aim (so far) is just to help
   resolve minipool references.  *)
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

and ssa_reg_id = CT.reg * int

type info_record =
  {
    infotag : (ssa_reg_id, infotag list) Hashtbl.t;
    implications : (ssa_reg_id, implication) Hashtbl.t
  }

let string_of_ssa_reg reg num =
  Printf.sprintf "%s_%d" (CT.string_of_reg reg) num

let used_as_addr regid ht =
  try
    let features = Hashtbl.find ht regid in
    List.exists (function Used_as_addr _ -> true | _ -> false) features
  with Not_found -> false

let implied_pointer regid hti =
  try
    match Hashtbl.find hti regid with
      Pointer -> true
    | _ -> false
  with Not_found -> false

let probably_pointer regid inforec =
  used_as_addr regid inforec.infotag
  || implied_pointer regid inforec.implications

let record_info ht reg info =
  try
    let infos = Hashtbl.find ht reg in
    if not (List.mem info infos) then
      Hashtbl.replace ht reg (info::infos)
  with Not_found ->
    Hashtbl.add ht reg [info]

let record_impl ht reg info =
  if not (Hashtbl.mem ht reg) then
    Hashtbl.add ht reg info

let rec info_of_mem_type ~load = function
    Irtypes.Word -> if load then Word_loads else Word_stores
  | Irtypes.U8 -> if load then Byte_loads else Byte_stores
  | Irtypes.U16 -> if load then Halfword_loads else Halfword_stores
  | Irtypes.S8 -> if load then Signed_byte_loads else Byte_stores
  | Irtypes.S16 -> if load then Signed_halfword_loads else Halfword_stores
  (*| Irtypes.Block { Irtypes.access_size = k } -> info_of_mem_type ~load k*)

let basic_type impl_ht regid =
  let datas = Hashtbl.find_all impl_ht regid in
  try
    let i = List.find (function Int | Pointer -> true | _ -> false) datas in
    Some i
  with Not_found ->
    None

let rec simplify_one_implication impl_ht impl =
  let known_type regid typ =
    try 
      (Hashtbl.find impl_ht regid) = typ
    with Not_found -> false in
  match impl with
    Int | Pointer -> impl
  | Unary_imp (regid, typ, impltyp) when known_type regid typ -> impltyp
  | Binary_imp (regid1, typ1, regid2, typ2, impltyp)
      when known_type regid1 typ1 && known_type regid2 typ2 -> impltyp
  | Binary_imp (regid1, typ1, regid2, typ2, impltyp)
      when known_type regid1 typ1 -> Unary_imp (regid2, typ2, impltyp)
  | Binary_imp (regid1, typ1, regid2, typ2, impltyp)
      when known_type regid2 typ2 -> Unary_imp (regid1, typ1, impltyp)
  | One_of il ->
      let newlist = List.map (fun i -> simplify_one_implication impl_ht i)
			     il in
      begin try
        List.find
	  (function Int | Pointer -> true | _ -> false)
	  newlist
      with Not_found ->
        One_of newlist
      end
  | x -> x

let simplify_implications impl_ht =
  let finished = ref false in
  let old_contents = ref [] in
  let rec iterate () =
    let contents =
      Hashtbl.fold
	(fun reg impl reg_impl_list -> (reg, impl)::reg_impl_list)
	impl_ht
	[] in
    let contents' = List.map
      (fun (regid, impl) ->
	let impl' = simplify_one_implication impl_ht impl in
	(regid, impl'))
      contents in
    (* Quite inefficient, but never mind...  *)
    if contents' = !old_contents then
      finished := true
    else
      old_contents := contents';
    Hashtbl.clear impl_ht;
    List.iter
      (fun (regid, impl) ->
	match impl, basic_type impl_ht regid with
          (Int | Pointer), None -> Hashtbl.add impl_ht regid impl
	| (Int | Pointer) as newtype, Some othertype
	    when newtype <> othertype ->
	    Log.printf 3 "types don't match for '%s'\n"
	      (string_of_ssa_reg (fst regid) (snd regid))
	| (Int | Pointer) as newtype, _ ->
            Hashtbl.replace impl_ht regid newtype
	| _, Some _ ->
            ()
	| _, _ ->
            Hashtbl.add impl_ht regid impl)
      contents';
    if not !finished then iterate () in
  iterate ()

let create_info () =
  {
    infotag = Hashtbl.create 10;
    implications = Hashtbl.create 10
  }

let gather_info blk_arr inforec =
  let ht = inforec.infotag
  and impl_ht = inforec.implications in
  Array.iter
    (fun blk ->
      CS.iter
        (fun insn ->
	  match insn with
	    C.Set (C.SSAReg (rd, rdn), C.Load (memtype,
		     C.Binary (Irtypes.Add, C.SSAReg (rb, rbn), C.Immed _)))
	  | C.Set (C.SSAReg (rd, rdn), C.Load (memtype,
		     C.SSAReg (rb, rbn))) ->
	      (* Load [reg] and load [reg+immediate].  *)
	      record_info ht (rd, rdn) (info_of_mem_type ~load:true memtype);
	      record_info ht (rb, rbn) (Used_as_addr memtype);
	      record_impl impl_ht (rb, rbn) Pointer
	  | C.Store (memtype, C.Binary (Irtypes.Add,
					C.SSAReg (rb, rbn), C.Immed _),
		     C.SSAReg (rs, rsn))
	  | C.Store (memtype, C.SSAReg (rb, rbn), C.SSAReg (rs, rsn)) ->
	      (* Store [reg] and store [reg+immediate].  *)
	      record_info ht (rb, rbn) (Used_as_addr memtype);
	      record_info ht (rs, rsn) (info_of_mem_type ~load:false memtype);
	      record_impl impl_ht (rb, rbn) Pointer
	  | C.Set (C.SSAReg (rd, rdn), C.SSAReg (rs, rsn)) ->
	      (* Move rd <- rs.  *)
	      record_impl impl_ht (rd, rdn)
	        (One_of
		  [Unary_imp ((rs, rsn), Int, Int);
		   Unary_imp ((rs, rsn), Pointer, Pointer)])
	  | C.Set (C.SSAReg (rd, rdn), C.Binary (Irtypes.Add,
		     C.SSAReg (ra, ran), C.SSAReg (rb, rbn))) ->
	      (* Add, rd <- ra + rb.  *)
	      record_impl impl_ht (rd, rdn)
		(One_of
		  [Binary_imp ((ra, ran), Int, (rb, rbn), Int, Int);
		   Binary_imp ((ra, ran), Pointer, (rb, rbn), Int, Pointer);
		   Binary_imp ((ra, ran), Int, (rb, rbn), Pointer, Pointer)])
	  | C.Set (C.SSAReg (rd, rdn), C.Binary (Irtypes.Sub,
		     C.SSAReg (ra, ran), C.SSAReg (rb, rbn))) ->
	      (* Add, rd <- ra - rb.  *)
	      record_impl impl_ht (rd, rdn)
		(One_of
		  [Binary_imp ((ra, ran), Int, (rb, rbn), Int, Int);
		   Binary_imp ((ra, ran), Pointer, (rb, rbn), Int, Pointer);
		   Binary_imp ((ra, ran), Int, (rb, rbn), Pointer, Pointer);
		   Binary_imp ((ra, ran), Pointer, (rb, rbn), Pointer, Int)])
	  | C.Set (C.SSAReg (rd, rdn), C.Binary ((Irtypes.Add | Irtypes.Sub),
		    C.SSAReg (ra, ran), C.Immed _)) ->
	      (* Add or sub immediate, rd <- ra [+-] imm.  *)
	      record_impl impl_ht (rd, rdn)
	        (One_of
		  [Unary_imp ((ra, ran), Int, Int);
		   Unary_imp ((ra, ran), Pointer, Pointer)])
	  | C.Set (C.SSAReg (rd, rdn),
		   C.Binary ((Irtypes.Mul | Irtypes.And | Irtypes.Eor
			      | Irtypes.Or),
			     C.SSAReg (ra, ran), C.SSAReg (rb, rbn))) ->
	      (* If we're doing multiplies/logic ops, none of the operands
	         involved is likely to be a pointer, but it's not impossible! 
		 Maybe make this more configurable.  *)
	      record_impl impl_ht (rd, rdn) Int;
	      record_impl impl_ht (ra, ran) Int;
	      record_impl impl_ht (rb, rbn) Int
	  | C.Control (C.CompJump_ext (_, C.SSAReg (rc, rcn))) ->
	      record_info ht (rc, rcn) Code_pointer
	  | _ ->
	      Log.printf 3 "gathered no info for '%s'\n"
			    (C.string_of_code insn);
	      ())
	blk.Block.code)
    blk_arr;
  simplify_implications impl_ht

let string_of_info = function
    Used_as_addr meminfo ->
      Printf.sprintf "used as addr (%s)" (CT.string_of_mem meminfo)
  | Loaded_pc_rel -> "loaded PC-relative"
  | Type_known _ -> "type known (...)"
  | Byte_loads -> "loaded as byte"
  | Byte_stores -> "stored as byte"
  | Signed_byte_loads -> "loaded as signed byte"
  | Halfword_loads -> "loaded as halfword"
  | Signed_halfword_loads -> "loaded as signed halfword"
  | Halfword_stores -> "stored as halfword"
  | Word_loads -> "loaded as word"
  | Word_stores -> "stored as word"
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
      String.concat "\n  | " (List.map string_of_implied_info impl_list)

let print_info ht =
  Hashtbl.iter
    (fun (reg, regn) infolist ->
      List.iter
        (fun info ->
	  Log.printf 3 "%s : %s\n" (string_of_ssa_reg reg regn)
				   (string_of_info info))
	infolist)
    ht

let print_implied_info ht =
  Hashtbl.iter
    (fun (reg, regn) impl ->
      Log.printf 3 "%s : %s\n" (string_of_ssa_reg reg regn)
			       (string_of_implied_info impl))
    ht

