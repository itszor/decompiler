type 'code block =
  {
    mutable code : 'code;
    id : string;
    mutable predecessors : 'code block list;
    mutable successors : 'code block list;
    mutable parent : 'code block option;
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
    mutable live_out : Boolset.t
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
    live_out = Boolset.empty
  }

