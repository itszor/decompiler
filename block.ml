type ('idtype, 'code) block =
  {
    mutable code : 'code;
    id : 'idtype;
    mutable predecessors : ('idtype, 'code) block list;
    mutable successors : ('idtype, 'code) block list;
    mutable parent : ('idtype, 'code) block option;
    mutable dfnum : int;
    mutable ancestor : int option;
    mutable semi : int option;
    mutable idom : int option;
    mutable idomchild : int list;
    mutable samedom : int option;
    mutable bucket : int list;
    mutable domfront : int list;
    mutable visited : bool;
    mutable live_in : Boolset.t;
    mutable live_out : Boolset.t;
    mutable start_sp_offset : int option;
    mutable end_sp_offset : int option
  }

let make_block id code =
  {
    code = code;
    id = id;
    predecessors = [];
    successors = [];
    parent = None;
    dfnum = -1;
    ancestor = None;
    semi = None;
    idom = None;
    idomchild = [];
    samedom = None;
    bucket = [];
    domfront = [];
    visited = false;
    live_in = Boolset.empty;
    live_out = Boolset.empty;
    start_sp_offset = None;
    end_sp_offset = None
  }

let clear_visited blk_arr =
  Array.iter (fun blk -> blk.visited <- false) blk_arr

let map_code fn blkarr =
  let new_blkarr = Array.map
    (fun blk ->
      let code' = fn blk.code in
      { blk with code = code'; predecessors = []; successors = [];
	parent = None })
    blkarr in
  (* Fix up predecessor/successor/parent links (ew).  *)
  Array.iteri
    (fun this_idx blk ->
      assert (this_idx = blk.dfnum);
      new_blkarr.(this_idx).predecessors
        <- List.map (fun blk -> new_blkarr.(blk.dfnum)) blk.predecessors;
      new_blkarr.(this_idx).successors
        <- List.map (fun blk -> new_blkarr.(blk.dfnum)) blk.successors;
      match blk.parent with
        None -> new_blkarr.(this_idx).parent <- None
      | Some p -> new_blkarr.(this_idx).parent <- Some new_blkarr.(p.dfnum))
    blkarr;
  new_blkarr
