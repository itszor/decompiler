(* Opcodes & registers for optimising macro assembler.  *)

module type CODETYPES =
  sig
    type reg
    type nulop
    type unop
    type binop
    type triop
    type extop
    type mem
    type immed
    type addr
    type abi
    type entity
    
    val string_of_reg : reg -> string
    val string_of_nulop : nulop -> string
    val string_of_unop : unop -> string
    val string_of_binop : binop -> string
    val string_of_triop : triop -> string
    val string_of_extop : extop -> string
    val string_of_mem : mem -> string
    val string_of_immed : immed -> string
    val string_of_addr : addr -> string
    val string_of_abi : abi -> string
    val string_of_entity : entity -> string
  end

(* We have an abstract block reference type, but we also need to impose an
   ordering on blocks for efficiency, etc. This is done with to_index and
   of_index, which should return monotonically-increasing integer indices
   per-block.
   
   This flexibility allows, e.g., blocks to be referenced by strings, if
   desired.  *)

module type BLOCKSEQ =
  sig
    type 'a t
    type blockref
    type reftable
    
    val empty : 'a t
    val is_empty : 'a t -> bool
    val cons : 'a -> 'a t -> 'a t
    val head : 'a t -> 'a
    val tail : 'a t -> 'a t
    (*val get_last : 'a t -> 'a*)
    val lookup : 'a t -> int -> 'a
    val update : 'a t -> int -> 'a -> 'a t
    val lookup_ref : 'a t -> reftable -> blockref -> 'a
    val length : 'a t -> int
    val fold_right : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
    val iter : ('a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val to_index : reftable -> blockref -> int
    val of_index : reftable -> int -> blockref
    val of_list : 'a list -> 'a t
    val of_list_rev : 'a list -> 'a t
    
    val string_of_blockref : blockref -> string
  end

(*module type CODE = functor (CT : CODETYPES) -> functor (BS : BLOCKSEQ) ->
  sig
    type code =
        Reg of CT.reg
      | Mem of CT.mem * code
      | Immed of CT.immed
      | Nary of CT.extop * int * code list
      | Trinary of CT.triop * code * code * code
      | Binary of CT.binop * code * code
      | Unary of CT.unop * code
      | Nullary of CT.nulop
      | Set of code * code
      | Control of control
      | Phi of code array

    and control =
        Jump of code list * BS.blockref
      | Call of code list * BS.blockref * BS.blockref
      | Branch of code * BS.blockref * BS.blockref
      | Return
      | Jump_ind of code
      | Call_ind of code
      | Jump_ext of CT.addr  (* External branches to OS routines, etc.  *)
      | Call_ext of code list * CT.addr
    
    val get_last : code BS.t -> code
    val get_control : code BS.t -> control
    val int_of_reg : CT.reg -> int
    val reg_of_int : int -> CT.reg
  end*)

module type CODESEQ =
  sig
    type 'a t
    
    val empty : 'a t
    val cons : 'a -> 'a t -> 'a t
    val snoc : 'a t -> 'a -> 'a t
    val fold_right : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
    val map : ('a -> 'b) -> 'a t -> 'b t
    val iter : ('a -> unit) -> 'a t -> unit
    val get_last : 'a t -> 'a
    val length : 'a t -> int
    val nth : 'a t -> int -> 'a
  end

module Code (CT : CODETYPES) (CS : CODESEQ) (BS : BLOCKSEQ) =
  struct
    type code =
        Reg of CT.reg
      | SSAReg of CT.reg * int
      | Load of CT.mem * code
      | Store of CT.mem * code * code
      | Immed of CT.immed
      | Nary of CT.extop * code list
      | Trinary of CT.triop * code * code * code
      | Binary of CT.binop * code * code
      | Unary of CT.unop * code
      | Nullary of CT.nulop
      | Set of code * code
      | Control of control
      | Phi of code array
      | Entity of CT.entity
      (* Just for iterating over code sequences.  Don't process "protected"
         child nodes.  *)
      | Protect of code

    (* FIXME: Seems like these need sanitizing a bit.  *)
    and control =
        TailCall of BS.blockref * code
      | Call of BS.blockref * code * BS.blockref * code
      | Jump of BS.blockref
      | Branch of code * BS.blockref * BS.blockref
      | Return of code
      | CompTailCall of code * code
      | CompCall of code * code * BS.blockref * code
      | CompJump of code * BS.blockref list
      (* External branches to OS routines, libraries, etc.  *)
      | TailCall_ext of CT.abi * CT.addr * code
      | Call_ext of CT.abi * CT.addr * code * BS.blockref * code
      | Jump_ext of CT.abi * CT.addr
      | CompJump_ext of CT.abi * code
    
    let get_last blk = CS.get_last blk
    
    let str = Printf.sprintf
    
    let rec string_of_control = function
      TailCall (tailr, targs) ->
	str "tailcall (%s, %s)" (BS.string_of_blockref tailr)
	  (string_of_code targs)
    | Call (callr, cargs, retr, rargs) ->
        str "call (%s, %s, %s, %s)" (BS.string_of_blockref callr)
	  (string_of_code cargs) (BS.string_of_blockref retr)
	  (string_of_code rargs)
    | Jump jumpr ->
        str "jump (%s)" (BS.string_of_blockref jumpr)
    | CompJump (jumpc, targs) ->
        str "compjump (%s, {%s})" (string_of_code jumpc)
	  (String.concat ", " (List.map BS.string_of_blockref targs))
    | Branch (cond, truer, falser) ->
        str "branch (%s, %s, %s)" (string_of_code cond)
	  (BS.string_of_blockref truer) (BS.string_of_blockref falser)
    | Return code ->
        str "return (%s)" (string_of_code code)
    | CompTailCall (tailc, targs) ->
        str "tailcall_ind (%s, %s)" (string_of_code tailc)
	  (string_of_code targs)
    | CompCall (callc, cargs, retr, rargs) ->
        str "call_ind (%s, %s, %s, %s)" (string_of_code callc)
	  (string_of_code cargs) (BS.string_of_blockref retr)
	  (string_of_code rargs)
    | TailCall_ext (abi, addr, targs) ->
        str "tailcall_ext (%s, %s, %s)" (CT.string_of_abi abi)
	  (CT.string_of_addr addr) (string_of_code targs)
    | Call_ext (abi, addr, cargs, retr, rargs) ->
        str "call_ext (%s, %s, %s, %s, %s)" (CT.string_of_abi abi)
	  (CT.string_of_addr addr) (string_of_code cargs)
	  (BS.string_of_blockref retr) (string_of_code rargs)
    | Jump_ext (abi, addr) ->
        str "jump_ext (%s, %s)" (CT.string_of_abi abi) (CT.string_of_addr addr)
    | CompJump_ext (abi, code) ->
        str "compjump_ext (%s, %s)" (CT.string_of_abi abi) (string_of_code code)
    
    and string_of_code = function
      Reg r -> CT.string_of_reg r
    | SSAReg (r, n) -> str "%s_%s" (CT.string_of_reg r) (string_of_int n)
    | Load (m, c) -> str "load-%s[%s]" (CT.string_of_mem m) (string_of_code c)
    | Store (m, c, v) -> str "store-%s[%s] <- %s" (CT.string_of_mem m)
			  (string_of_code c) (string_of_code v)
    | Immed i -> CT.string_of_immed i
    | Nary (eo, cl) ->
        str "%s (%s)" (CT.string_of_extop eo)
	  (String.concat ", " (List.map string_of_code cl))
    | Trinary (triop, a, b, c) ->
        str "%s (%s, %s, %s)" (CT.string_of_triop triop) (string_of_code a)
	  (string_of_code b) (string_of_code c)
    | Binary (binop, a, b) ->
        str "%s (%s, %s)" (CT.string_of_binop binop) (string_of_code a)
	  (string_of_code b)
    | Unary (unop, a) ->
        str "%s (%s)" (CT.string_of_unop unop) (string_of_code a)
    | Nullary nul -> CT.string_of_nulop nul
    | Set (dst, src) ->
        str "%s := %s" (string_of_code dst) (string_of_code src)
    | Control ctl ->
        str "--> %s" (string_of_control ctl)
    | Phi carr ->
        str "phi (%s)" (String.concat ", " (Array.to_list
	  (Array.map string_of_code carr)))
    | Entity e -> CT.string_of_entity e
    | Protect x -> str "*protect* (%s)" (string_of_code x)
  
  let string_of_codeseq cs =
    let buf = CS.fold_left
      (fun buf code ->
        Buffer.add_string buf (string_of_code code);
	Buffer.add_char buf '\n';
	buf)
      (Buffer.create 20)
      cs in
    Buffer.contents buf
  
  let get_control blk =
    match get_last blk with
      Control ctl -> ctl
    | x ->
      let insn = string_of_code x in
      failwith (Printf.sprintf
	"Last instruction of block (%s) does no control flow" insn)

  let rec fold_postorder ?inhibit_set_dest fn code acc =
    match code with
      Entity _ | Reg _ | SSAReg _ | Immed _ | Nullary _ -> fn code acc
    | Nary (_, clist) ->
        let acc' = List.fold_right fn clist acc in
	fn code acc'
    | Trinary (_, a, b, c) ->
        let acc' = fold_postorder ?inhibit_set_dest fn a acc in
	let acc'' = fold_postorder ?inhibit_set_dest fn b acc' in
	let acc''' = fold_postorder ?inhibit_set_dest fn c acc'' in
	fn code acc'''
    | Binary (_, a, b) ->
        let acc' = fold_postorder ?inhibit_set_dest fn a acc in
	let acc'' = fold_postorder ?inhibit_set_dest fn b acc' in
	fn code acc''
    | Unary (_, a) | Load (_, a) ->
        let acc' = fold_postorder ?inhibit_set_dest fn a acc in
	fn code acc'
    | Store (_, a, b) ->
        let acc' = fold_postorder ?inhibit_set_dest fn a acc in
	let acc'' = fold_postorder ?inhibit_set_dest fn b acc' in
	fn code acc''
    | Set (d, s) ->
        begin match inhibit_set_dest with
	  Some true ->
	    let acc' = fold_postorder ?inhibit_set_dest fn s acc in
	    fn code acc'
	| _ ->
            let acc' = fold_postorder ?inhibit_set_dest fn d acc in
	    let acc'' = fold_postorder ?inhibit_set_dest fn s acc' in
	    fn code acc''
	end
    | Control c ->
        let acc' = fold_ctl_postorder ?inhibit_set_dest fn c acc in
	fn code acc'
    | Phi parr ->
        let acc' = Array.fold_right fn parr acc in
	fn code acc'
  
  and fold_ctl_postorder ?inhibit_set_dest fn ctl acc =
    match ctl with
      TailCall (_, code) | Branch (code, _, _) | CompJump (code, _)
    | TailCall_ext (_, _, code) | Return code | CompJump_ext (_, code) ->
        fold_postorder ?inhibit_set_dest fn code acc
    | Call (_, c1, _, c2) | CompTailCall (c1, c2)
    | Call_ext (_, _, c1, _, c2) ->
        let acc' = fold_postorder ?inhibit_set_dest fn c1 acc in
	fold_postorder fn c2 acc'
    | CompCall (c1, c2, _, c3) ->
        let acc' = fold_postorder ?inhibit_set_dest fn c1 acc in
	let acc'' = fold_postorder ?inhibit_set_dest fn c2 acc' in
	fold_postorder ?inhibit_set_dest fn c3 acc''
    | Jump _ | Jump_ext _ -> acc
  
  let map fn ?(ctl_fn = fun x -> x) code =
    let rec scan e =
      match fn e with
	(Entity _ | Reg _ | SSAReg _ | Immed _ | Nullary _) as x -> x
      | Load (mem, code) ->
	  Load (mem, scan code)
      | Store (mem, code, v) ->
	  Store (mem, scan code, scan v)
      | Nary (op, clist) ->
	  Nary (op, List.map scan clist)
      | Trinary (op, a, b, c) ->
	  Trinary (op, scan a, scan b, scan c)
      | Binary (op, a, b) ->
	  Binary (op, scan a, scan b)
      | Unary (op, a) ->
	  Unary (op, scan a)
      | Set (d, s) ->
	  Set (scan d, scan s)
      | Control c ->
	  Control (scan_ctl c)
      | Phi parr ->
	  Phi (Array.map scan parr)
      | Protect child -> child
    and scan_ctl e =
      match ctl_fn e with
	TailCall (br, code) ->
	  TailCall (br, scan code)
      | Call (call, carg, ret, retarg) ->
	  Call (call, scan carg, ret, scan retarg)
      | Jump _ -> e
      | Branch (code, tr, fa) ->
	  Branch (scan code, tr, fa)
      | Return code ->
	  Return (scan code)
      | CompTailCall (dst, arg) ->
	  CompTailCall (scan dst, scan arg)
      | CompCall (dst, arg, ret, retarg) ->
	  CompCall (scan dst, scan arg, ret, scan retarg)
      | CompJump (code, dl) ->
	  CompJump (scan code, dl)
      | TailCall_ext (abi, addr, code) ->
	  TailCall_ext (abi, addr, scan code)
      | Call_ext (abi, addr, arg, ret, retarg) ->
	  Call_ext (abi, addr, scan arg, ret, scan retarg)
      | Jump_ext _ -> e
      | CompJump_ext (abi, dst) ->
	  CompJump_ext (abi, scan dst) in
    scan code
	
  end

