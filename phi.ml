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
	      Log.printf 3 "reg %s defined in %d\n"
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
	      Log.printf 3 "reg %s, blk %d.\n" (CT.string_of_reg reg) n;
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
		    Log.printf 3 "*** inserting phi in blk %d\n" blk_in_df;
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
            let node' = C.map
	      (function
	        C.Set (lhs, (C.Phi _ as rhs)) ->
		  (* Don't process phi nodes.  *)
		  C.Protect (C.Set (lhs, rhs))
	      | C.Set (lhs, rhs) ->
	          (* Only interested in uses, not defs.  *)
	          C.Set (C.Protect lhs, rhs)
	      | C.Reg ru as node ->
		  begin try
		    let runum = Hashtbl.find rnum_htab ru in
		    let idx = List.hd stack.(runum) in
		    C.SSAReg (ru, idx)
		  with Not_found as e ->
		    Printf.fprintf stderr "reg %s not in rnum_htab\n"
		      (CT.string_of_reg ru);
		    raise e
		  end
	      | x -> x)
	      node in
	    let node'' = C.map
	      (function
		C.Set ((C.Reg rd as lhs), rhs) ->
		  begin try
		    let rdnum = Hashtbl.find rnum_htab rd in
		    count.(rdnum) <- count.(rdnum) + 1;
		    let idx = count.(rdnum) in
		    stack.(rdnum) <- idx :: stack.(rdnum);
		    let ssa_var = C.SSAReg (rd, idx) in
		    C.Protect (C.Set (ssa_var, rhs))
		  with Not_found as e ->
		    Printf.fprintf stderr "reg %s not in rnum_htab\n"
		      (CT.string_of_reg rd);
		    raise e
		  end
	      | x -> x)
	      node' in
	    CS.snoc codeseq node'')
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
	  (fun child -> rename' blk_arr child)
	  blk_n.idomchild; (* The right children?  *)
	(* Pop variables originally defined in block off the stack.  *)
	CS.iter
	  (function
	    C.Set (C.SSAReg _, C.Phi _) -> ()
	  | C.Set (C.SSAReg (rd, _) as c, _) ->
	      begin try
	        let rdnum = Hashtbl.find rnum_htab rd in
		stack.(rdnum) <- List.tl stack.(rdnum)
	      with Not_found ->
		Log.printf 3 "Ignoring SSA reg %s (already converted)\n"
		  (C.string_of_code c);
		()
	      end
	  | _ -> ())
	  blk_n.code in
      (* Perform renaming.  *)
      rename' blk_arr entry_pt_idx

    (* Eliminate phi nodes by inserting set instructions at the end of
       predecessor blocks.  *)
    let eliminate blk_arr =
      Array.iter
        (fun blk ->
	  let code' = CS.fold_left
	    (fun code insn ->
	      match insn with
	        C.Set (dst, C.Phi phi_args) ->
		  Log.printf 3 "eliminating phi '%s'\n"
		    (C.string_of_code insn);
		  Array.iteri
		    (fun i arg ->
		      let pred_idx
		        = (List.nth blk.Block.predecessors i).Block.dfnum in
		      let pred_blk = blk_arr.(pred_idx) in
		      let pred_code = pred_blk.Block.code in
		      let copy = C.Set (dst, arg) in
		      let pred_code'
		        = C.insert_before_control pred_code copy in
		      pred_blk.Block.code <- pred_code')
		    phi_args;
		  code
	      | x -> CS.snoc code x)
	    CS.empty
	    blk.Block.code in
	  blk.Block.code <- code')
	blk_arr
  
  end
