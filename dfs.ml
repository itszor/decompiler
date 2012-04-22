(* Find predecessors/successors, and perform depth-first search.  *)

module Dfs (CT : Code.CODETYPES) (CS : Code.CODESEQ) (BS : Code.BLOCKSEQ) =
  struct
    module C = Code.Code (CT) (CS) (BS)
    open Block

    (* Calculate predecessors and successors.  *)
    let pred_succ ~whole_program blks reftable =
      let link fromblk dstref =
        let toblk = BS.lookup_ref blks reftable dstref in
        fromblk.successors <- toblk :: fromblk.successors;
        toblk.predecessors <- fromblk :: toblk.predecessors in
      let rec scan lst retstk =
        if not (BS.is_empty lst) then
          let hd = BS.head lst in
          let ctl = C.get_control hd.Block.code in
          match ctl with
            C.Jump dst ->
              link hd dst;
              scan (BS.tail lst) retstk
          | C.Call (call, _, ret, _) ->
              if whole_program then begin
                link hd call;
                scan (BS.tail lst) (ret::retstk)
              end else begin
                link hd ret;
                scan (BS.tail lst) retstk
              end
          | C.Branch (_, tru, fals) ->
              link hd tru;
              link hd fals;
              scan (BS.tail lst) retstk
          | C.Return _ ->
              if whole_program then begin
                match retstk with
                  [] -> failwith "Empty return stack"
                | ret::rest ->
                    link hd ret;
                    scan (BS.tail lst) rest
              end else
                (* ??? *)
                scan (BS.tail lst) retstk
          | C.CompJump (_, dests) ->
              List.iter (fun dst -> link hd dst) dests;
              scan (BS.tail lst) retstk
          (* FIXME: Several control types not implemented here.  *)
          | _ -> scan (BS.tail lst) retstk
      in
        scan blks []

    (* Enumerate blocks depth-first.  *)
    let dfs blks reftable entry_pt =
      let rec scan ?parent ~dfcount node =
        (*Printf.printf "giving node %d dfnum %d\n" node.self_index dfcount;*)
        node.dfnum <- dfcount;
        node.parent <- parent;
	List.fold_left
	  (fun dfcount w ->
	    if w.dfnum == -1 then
              scan ~parent:node ~dfcount:(succ dfcount) w
	    else
	      dfcount)
	  dfcount
	  node.successors
      in
        ignore (scan ~dfcount:0 (BS.lookup_ref blks reftable entry_pt))

    let blockseq_to_dfs_array blks =
      let len = BS.length blks in
      let arr = Array.init len (fun n -> BS.lookup blks n) in
      Array.sort (fun a b -> compare a.dfnum b.dfnum) arr;
      arr

    (* If we're using functional-style update on the block sequence data
       structure, the mutable bits can get out-of-date and point to old
       versions of the data.  Call this to point to the current structure
       instead.  This is pretty ugly, but that's what you get for mixing
       mutable and immutable data structures.  FIXME: Don't do that?  *)
    (*let refresh blks reftable =
      let refresh_list = List.map (fun ptr -> BS.lookup blks ptr.self_index)
      and refresh_option = function
        None -> None
      | Some o -> Some (BS.lookup blks o.self_index) in
      BS.iter
        (fun blk ->
	  blk.predecessors <- refresh_list blk.predecessors;
	  blk.successors <- refresh_list blk.successors;
	  blk.parent <- refresh_option blk.parent)
	blks*)
  end
