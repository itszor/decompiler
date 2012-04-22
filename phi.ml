open Block
open Getoption

(* The algorithm for inserting PHI-nodes is as follows.
   (from "Modern compiler implementation in ML", Andrew Appel)
   (...with errata fixed)

  Place-PHI-Functions =
    for each node n
      for each variable a in Aorig[n]
        defsites[a] <- defsites[a] U {n}
    for each variable a
      W <- defsites[a]
        while W not empty
          remove some node n from W
          for each Y in DF[n]
            if a not in Aphi[Y]
              insert statement a <- PHI(a, a, ..., a) at top of
                block Y, where the PHI-function has as many arguments
                as Y has predecessors
              Aphi[Y] <- Aphi[Y] U {a}
              if a not in Aorig[Y]
                W <- W U {Y}

  U : union
  W : linked list (worklist)
  Aphi[n] : A (subscript) phi - set of variables with phi functions at node n
  Aorig[n] : A (subscript) orig - set of variables defined in node n
  G : graph of nodes (for each node n...)
  
  For testing membership of W: mark bit in representation of each node n.

*)

module PhiPlacement (CT : Code.CODETYPES) (CS : Code.CODESEQ)
                    (BS : Code.BLOCKSEQ) =
  struct
    open Block
    module C = Code.Code (CT) (CS) (BS)
        
    (* A set of registers.  *)
    module R = Set.Make (
      struct
        type t = CT.reg
	let compare = compare
      end)
    
    let regs_assigned_in_block blk regset =
      CS.fold_right
        (fun node regset' ->
	  match node with
	    C.Set (C.Reg r, _) -> R.add r regset'
	  | _ -> regset')
	blk.code
	regset
    
    let add_blk_for_reg htab reg blk =
      try
        let existing = Hashtbl.find htab reg in
	Hashtbl.replace htab reg (blk :: existing)
      with Not_found ->
        Hashtbl.add htab reg [blk]
    
    let regs_and_defsites_in_blockseq blk_arr =
      let defsites = Hashtbl.create 10 in
      let defined_regs = Array.fold_right
        (fun blk defined_regs' ->
	  let in_blk = regs_assigned_in_block blk R.empty in
	  R.iter
	    (fun reg ->
	      Printf.printf "reg %s defined in %d\n"
	        (CT.string_of_reg reg) blk.dfnum;
	      add_blk_for_reg defsites reg blk.dfnum)
	    in_blk;
	  R.union in_blk defined_regs')
	blk_arr
	R.empty in
      defined_regs, defsites
    
    let place blk_arr =
      let regset, defsites = regs_and_defsites_in_blockseq blk_arr in
      let phi_for_reg = Array.make (Array.length blk_arr) R.empty in
      let reg_has_phi_node_for_blk_p reg blk =
        let regset = phi_for_reg.(blk) in
	R.mem reg regset
      and mark_phi_node_for_reg_in_blk reg blk =
        let regset = phi_for_reg.(blk) in
	phi_for_reg.(blk) <- R.add reg regset
      and reg_defined_in_blk reg blk =
        let blks_for_reg = Hashtbl.find defsites reg in
	List.mem blk blks_for_reg in
      R.iter
        (fun reg ->
	  let defs = Hashtbl.find defsites reg in
	  let rec scan = function
	    [] -> ()
	  | n::defs ->
	      Printf.printf "reg %s, blk %d.\n" (CT.string_of_reg reg) n;
	      let defs_remaining = ref defs in
	      List.iter
	        (fun blk_in_df ->
		  if not (reg_has_phi_node_for_blk_p reg blk_in_df) then begin
		    let num_predecessors =
		      List.length blk_arr.(blk_in_df).predecessors in
		    let new_phi = C.Set (C.Reg reg,
					 C.Phi (Array.init num_predecessors
						  (fun _ -> C.Reg reg))) in
		    let prepended_code
		      = CS.cons new_phi blk_arr.(blk_in_df).code in
		    Printf.printf "*** inserting phi in blk %d\n" blk_in_df;
		    blk_arr.(blk_in_df).code <- prepended_code;
		    mark_phi_node_for_reg_in_blk reg blk_in_df;
		    if not (reg_defined_in_blk reg blk_in_df) then
		      defs_remaining := blk_in_df :: !defs_remaining;
		  end)
		blk_arr.(n).domfront;
	      scan !defs_remaining in
	  scan defs)
        regset;
      regset

    (* Create an (arbitrary) mapping of registers to consecutive integers as a
       hash table, to allow registers to be used as array indices.  *)
    let enumerate_regs regs =
      let htab = Hashtbl.create 10 in
      let numregs = R.fold
        (fun reg rnum ->
	  Hashtbl.add htab reg rnum;
	  succ rnum)
	regs
	0 in
      htab, numregs

    (* Algorithm for renaming variables
       also stolen shamelessly from Appel

      Initialisation:
	for each variable a
	  Count[a] <- 0
	  Stack[a] <- empty
	  push 0 onto Stack[a]

      Rename(n) =
	for each statement S in block n
	  if S is not a phi-function
            for each use of some variable x in S
              i <- top(Stack[x])
              replace the use of x with x_i in S
	  for each definition of some variable a in S
            Count[a] <- Count[a] + 1
            i <- Count[a]
            push i onto Stack[a]
            replace definition of a with definition of a_i in S
	for each successor Y of block n
	  Suppose n is the jth predecessor of Y
	  for each phi-function in Y
            suppose the jth operand of the phi-function is a
            i <- top(Stack[a])
            replace the jth operand with a_i
	for each child X of n
	  Rename(X)
	for each definition of some variable a in the original n  (!)
	  pop Stack[a]
	  
       (!) Algorithm in book reads "in the original S", but that doesn't make
           any sense.  I think this is the correct fix.
    *)

    (* Rename variables into SSA variables (both uses and definitions).  Works
       on a blockseq, i.e. the code within a single function.  *)
    let rename blk_arr entry_pt_idx all_regs =
      let rnum_htab, num_regs = enumerate_regs all_regs in
      let count = Array.make num_regs 0
      and stack = Array.make num_regs [0] in
      (* rewrite_statements is functional: returns a new modified copy of the
         code sequence.  *)
      let rewrite_statements blk_n =
        CS.fold_left
	  (fun codeseq node ->
            let node' = C.map_postorder
	      ~inhibit_set_dest:true
	      (function
	          (* We set inhibit_set_dest so this rule can match without
		     matching the LHS "Reg" first (since we're performing a
		     postorder traversal).  *)
		  C.Set (C.Reg rd, rhs) ->
		    let rdnum = Hashtbl.find rnum_htab rd in
		    count.(rdnum) <- count.(rdnum) + 1;
		    let idx = count.(rdnum) in
		    stack.(rdnum) <- idx :: stack.(rdnum);
		    C.Set (C.SSAReg (rd, idx), rhs)
		| C.Reg ru ->
		    let runum = Hashtbl.find rnum_htab ru in
		    let idx = List.hd stack.(runum) in
		    C.SSAReg (ru, idx)
		| x -> x)
	      node in
	    CS.snoc codeseq node')
	  CS.empty
	  blk_n.code in
      (* ...but rewrite_phi_nodes is imperative, and modifies the block
         sequence in-place, so we must be careful.  *)
      let rewrite_phi_nodes blk_n =
        List.iter
	  (fun blk_y ->
	    let jth_pred, _ = List.fold_right
	      (fun chk_pred (found, num) ->
	        if chk_pred.dfnum = blk_n.dfnum then
		  (num, succ num)
		else
		  (found, succ num))
	      blk_y.predecessors
	      (-1, 0) in
	    assert (jth_pred != -1);
	    let new_code = CS.map
	      (function
	        C.Set (lhs, C.Phi args) ->
		  let jth_arg = args.(jth_pred) in
		  let rewrote_reg = match jth_arg with
		    C.Reg r ->
		      let rnum = Hashtbl.find rnum_htab r in
		      let idx = List.hd stack.(rnum) in
		      C.SSAReg (r, idx)
		  | x -> x (* failwith "Non-register in PHI node" *) in
		  args.(jth_pred) <- rewrote_reg;
		  C.Set (lhs, C.Phi args)
	      | x -> x)
	      blk_y.code in
	    blk_y.code <- new_code)
	  blk_n.successors in
      let rec rename' blk_arr blk_idx =
        let blk_n = blk_arr.(blk_idx) in
	blk_n.code <- rewrite_statements blk_n;
	rewrite_phi_nodes blk_n;
	blk_arr.(blk_idx) <- blk_n;
	List.iter
	  (fun child ->
	    rename' blk_arr child)
	  blk_n.idomchild; (* The right children?  *)
	(* Pop variables originally defined in block off the stack.  *)
	CS.iter
	  (function
	      C.Set (C.SSAReg _, C.Phi _) -> ()
	    | C.Set (C.SSAReg (rd, _), _) ->
	        let rdnum = Hashtbl.find rnum_htab rd in
		stack.(rdnum) <- List.tl stack.(rdnum)
	    | _ -> ())
	  blk_n.code in
      (* Perform renaming.  *)
      rename' blk_arr entry_pt_idx
      
  end
  

(*
(* Add a block to the places a particular id is referenced. *)
let union defsites id blocknum =
  try
    let bits = Sets.RegOrPseudoMap.find id defsites in
    let bits' = Sets.IntSet.add blocknum bits in
    Sets.RegOrPseudoMap.add id bits' defsites
  with Not_found ->
    let bits = Sets.IntSet.singleton blocknum in
    Sets.RegOrPseudoMap.add id bits defsites

let member defsites id blocknum =
  try
    let defbits = Sets.RegOrPseudoMap.find id defsites in
    Sets.IntSet.mem blocknum defbits
  with Not_found ->
    false

let ids_in_block block acc =
  Block.block_fold_forwards
    (fun acc ast ->
      match ast with
        Ast.Register(id, typ, _) ->
          Sets.RegOrPseudoSet.add (Id.PhysReg(id, typ)) acc
      | _ -> acc)
    acc
    block

let all_ids vertices =
  let acc = ref Sets.RegOrPseudoSet.empty in
  for i = 0 to (DynArray.length vertices)-1 do
    let tag = DynArray.get vertices i in
    acc := ids_in_block tag.block !acc
  done;
  !acc

(* Create a virtual root block (for definitions of variables prior to
 * entry of the real root block), and link it backwards & forwards to
 * the real root block, 0.
 *)
let make_root vertices =
  let num = DynArray.length vertices
  and zero = DynArray.get vertices 0 in
  let vroot = {
    domfront = [];
    parent = None;
    predecessors = [];
    successors = [zero];
    semi = None;
    idom = None;
    idomchild = [zero];
    ancestor = None;
    samedom = None;
    bucket = [];
    dfnum = num;
    block = Block([], Jump(Local zero));
    selected = [];
    refno = 0l;
    writeidx = None;
    live_in = Sets.RegOrPseudoSet.empty;
    live_out = Sets.RegOrPseudoSet.empty
  } in
  zero.parent <- Some vroot;
  zero.predecessors <- vroot :: zero.predecessors;
  (* Some other fields might be important! *)
  DynArray.add vertices vroot;
  num

(* All variables are implicitly defined in the start block.
 * The "start" block is a new virtual block which we will number <start>,
 * which contains definitions for all variables prior to the "real" root
 * block.
 *)
let implicit_root_defs vertices defsites start =
  let allids = all_ids vertices in
  Sets.RegOrPseudoSet.fold
    (fun id defsites -> union defsites id start)
    allids
    defsites

(* Ids defined in a list of ast nodes *)
let defined_ids astlist =
  Ast.list_fold_forwards
    (fun acc ast ->
      match ast with
        Ast.Register(id, typ, Ast.Assign)
      | Ast.Register(id, typ, Ast.FixedAssign) ->
          Sets.RegOrPseudoSet.add (Id.PhysReg(id, typ)) acc
      | _ -> acc)
    Sets.RegOrPseudoSet.empty
    astlist

(* We have a DynArray of vertices to iterate over.
   We should build a map (RegOrPseudoMap) from reg_or_pseudos to BitSet
   (=DFS block num)
*)
let defsites vertices vroot =
  let defsites,_ = DynArray.fold_left
    (fun (defsites, i) tag ->
      let Block(insns,term) = tag.block in
      let defined = defined_ids insns in
      let defsites' = Sets.RegOrPseudoSet.fold
        (fun regorpseudo defsites -> union defsites regorpseudo i)
        defined
        defsites
      in
        defsites', i+1)
    (Sets.RegOrPseudoMap.empty, 0)
    vertices
  in
    implicit_root_defs vertices defsites vroot

(* Make a list of numbers from each set bit in a bitset *)
let nums_from_bitset bits =
  Sets.IntSet.elements bits

let rec display_worklist = function
    [] -> Printf.fprintf stderr "\n"
  | m::ms -> Printf.fprintf stderr "node: %d\n" m; display_worklist ms

(* let list_union li n =
  let rec scan thru =
    match thru with
      [] -> n :: li
    | t::ts -> if t=n then li else scan ts
  in
    scan li *)

(* Block.tag DynArray.t -> BitSet.t Sets.RegOrPseudoMap.t -> unit *)

let place vertices defsites =
  let aphi = ref Sets.RegOrPseudoMap.empty in
  Sets.RegOrPseudoMap.iter
    (fun a defsitebits ->
      let worklist = nums_from_bitset defsitebits in
      let rec consume = function
        [] -> ()
      | n::ns ->
          let tag = DynArray.get vertices n in
          let nsr = ref ns in
          List.iter
            (fun y ->
              if not (member !aphi a y.dfnum) then begin
                let Block(insns,term) = y.block in
                let astified_reg = Ast.ast_of_reg_or_pseudo a
                and npred = List.length y.predecessors in
                let ncopies = Array.make npred (astified_reg Ast.Use) in
                y.block <- Block(insns @ [Ast.Move(astified_reg Ast.Assign,
                                          Ast.Phi ncopies)],
                                 term);
                aphi := union !aphi a y.dfnum;
                if not (member defsites a y.dfnum) then begin
                  nsr := y.dfnum :: !nsr
                end;
              end)
            tag.domfront;
          consume !nsr
      in
        consume worklist)
    defsites


type countstack = {
  mutable count : int;
  mutable stack : int list;
}

(* the set of ids is easy to find, it is the keys from the defsites PMap *)
let ids defsites =
  Sets.RegOrPseudoMap.map (fun _ -> {count = 0; stack = [0];}) defsites

let stacktop entry =
  match entry.stack with
    [] -> failwith "Empty stack"
  | top::_ -> top

(* Find non-subscripted version of a reg *)
let find_nosub num typ ids =
  try
    Sets.RegOrPseudoMap.find (Id.PhysReg((num, Id.Unset), typ)) ids
  with Not_found ->
    let prefix = match typ with
      Id.IntType -> "r"
    | Id.PtrType -> "p"
    | Id.FloatType -> "f"
    in failwith ("reg not found: " ^ prefix ^ (string_of_int num))

let rewrite_uses ast ids =
  Ast.map_postorder
    (fun node ->
      match node with
        Ast.Register((num, _), typ, (Ast.Use as usage))
      | Ast.Register((num, _), typ, (Ast.LastUse as usage)) ->
          let entry = find_nosub num typ ids in
          Ast.Register((num, Id.Suf (stacktop entry)), typ, usage)
      | x -> x)
    ast

let rewrite_defs ast ids =
  Ast.map_postorder
    (fun node ->
      match node with
        Ast.Register((num, _), typ, (Ast.Assign as usage))
      | Ast.Register((num, _), typ, (Ast.FixedAssign as usage)) ->
          let entry = find_nosub num typ ids in
          entry.count <- entry.count + 1;
          let i = entry.count in
          entry.stack <- i :: entry.stack;
          Ast.Register((num, Id.Suf i), typ, usage)
      | x -> x)
    ast

let rewrite_blkref blkref ids =
  match blkref with
    Indirect ast -> Indirect(rewrite_uses ast ids)
  | x -> x

let rewrite_term term ids =
  match term with
    CondBranch(weight, cond, trueblk, falseblk) ->
      CondBranch(weight, rewrite_uses cond ids,
                         rewrite_blkref trueblk ids,
                         rewrite_blkref falseblk ids)
  | Call(toblk, retblk) -> Call(rewrite_blkref toblk ids,
                                rewrite_blkref retblk ids)
  | Jump(toblk) -> Jump(rewrite_blkref toblk ids)
  | Return -> Return

let rewrite_statements block ids =
  let rec walklist src acc =
    match src with
      [] -> acc
    | ast::asts ->
        let uses_renamed =
          begin match Stmt.classify ast with
            Stmt.PhiFunc -> ast  (* phi node, no rewrite *)
          | _ ->
            rewrite_uses ast ids
          end
        in let defs_renamed = rewrite_defs uses_renamed ids in
        walklist asts (defs_renamed :: acc)
  in let Block(astlist,term) = block in
  let astlist' = walklist (List.rev astlist) [] in
  let term' = rewrite_term term ids in
  Block(astlist', term')

let rewrite_phi_node p j ids =
  let Block(astlist, term) = p.block in
  List.iter
    (fun stmt ->
      match stmt with
        Ast.Move(dest, Ast.Phi nodes) ->
          begin match nodes.(j) with
            Ast.Register((num, loc), typ, usage) ->
              let entry = find_nosub num typ ids in
              nodes.(j) <- Ast.Register((num, Id.Suf (stacktop entry)), typ, 
                                        usage)
          | _ -> ()
          end
      | _ -> ())
    astlist

let seek_nth_predecessor preds blk =
  let rec scan preds' j =
    match preds' with
      [] ->
        Printf.printf "this dfnum=%d\n" blk.dfnum;
        List.iter (fun p -> Printf.printf "predecessor dfnum=%d\n" p.dfnum)
                  preds;
        failwith "Successor/predecessor mismatch"
    | p::ps -> if p==blk then j else scan ps (j+1)
  in
    scan preds 0

let rewrite_phi_nodes block ids =
  let rec walk successors =
    match successors with
      [] -> ()
    | successor :: rest ->
        let j = seek_nth_predecessor successor.predecessors block in
        rewrite_phi_node successor j ids;
        walk rest
  in
    walk block.successors

let pop_defs block ids =
  let Block(astlist,_) = block in
  List.iter
    (fun stmt -> Ast.iter
      (fun node ->
        match node with
          Ast.Register((num,_), typ, Ast.Assign)
        | Ast.Register((num,_), typ, Ast.FixedAssign) ->
            let entry = find_nosub num typ ids in
            entry.stack <- List.tl entry.stack
        | _ -> ())
      stmt)
    astlist

(* Check use of idomchild here! *)
let rename root defsites =
  let vars = ids defsites in
  let rec rename' tag =
    tag.block <- rewrite_statements tag.block vars;
    rewrite_phi_nodes tag vars;
    List.iter rename' tag.idomchild;
    pop_defs tag.block vars
  in
    rename' root

(* Modifies the array "mods" in-place!
   FIXME: This can fail at runtime if a phi node has sometihng other than
   a plain register as one of its sources. Perhaps we should use full-blown
   instruction selection? That could require extra registers to be allocated,
   though.
   I think we should probably disallow putting non-register things in Phi
   nodes.
   FIXME: That's too difficult to do with constant elimination as is works
   currently. Solutions would be (a) "proper" rematerialisation, (b) re-using
   instruction selection machinery here, or (c) doing a hack to be able to
   reload constants ourselves (requiring ISA-dependent code here).
   We should really go for (b).
   (b) can introduce new pseudos in the general case, though our ISA allows
   us to not have to. It'd be nice to be able to ask the instruction selection
   functions to never create new pseudos though, just in case.  *)

let eliminate_phi_in mods selectedlist preds =
  List.fold_right
    (fun i acc ->
      match i.Select.s_asm with
        Ast.Iphi(dest, nodes) ->
          for i=0 to (Array.length nodes)-1 do
            let dtag = preds.(i) in
            let ddfnum = dtag.dfnum in
            let ast = Ast.Move(dest, nodes.(i)) in
            (* FIXME: Here we'd really like to request that no new pseudos
               be created, but we don't. This could lead to crashes later.
               FIXME: -1 will need fixing if we ever need the insn numbers
               for anything (spill code insertion?). *)
            let acc, _ = Select.accum_insns_for_ast ast mods.(ddfnum) (-1) in
            mods.(ddfnum) <- acc
          done;
          acc
      | _ -> i::acc)
    selectedlist
    []

(* Convert phi nodes into moves *)
let eliminate vertices =
  let num = DynArray.length vertices in
  let mods = Array.make num [] in
  for i=0 to num-1 do
    let tag = DynArray.get vertices i in
    let preds = Array.of_list tag.predecessors in
    tag.selected <- eliminate_phi_in mods tag.selected preds
  done;
  (* Insert move instructions at the end of predecessor blocks.  *)
  for i=0 to num-1 do
    let tag = DynArray.get vertices i in
    tag.selected <- tag.selected @ mods.(tag.dfnum)
  done
*)
