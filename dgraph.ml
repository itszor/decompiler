(* Mutable directed graph.  *)

type 'a t =
{
  nodes : ('a, int) Hashtbl.t;
  mutable edges : BatISet.t BatIMap.t;
  mutable node_ctr : int
}

let make () =
  {
    nodes = Hashtbl.create 10;
    edges = BatIMap.empty ~eq:(=);
    node_ctr = 0
  }

let add_node a graph =
  if not (Hashtbl.mem graph.nodes a) then begin
    Hashtbl.add graph.nodes a graph.node_ctr;
    graph.edges <- BatIMap.add graph.node_ctr BatISet.empty graph.edges;
    graph.node_ctr <- succ graph.node_ctr
  end

let add_edge a b graph =
  add_node a graph;
  add_node b graph;
  let na = Hashtbl.find graph.nodes a
  and nb = Hashtbl.find graph.nodes b in
  if BatIMap.mem na graph.edges then
    let prevset = BatIMap.find na graph.edges in
    graph.edges <- BatIMap.add na (BatISet.add nb prevset) graph.edges
  else
    graph.edges <- BatIMap.add na (BatISet.singleton nb) graph.edges

let has_node a graph =
  try
    let na = Hashtbl.find graph.nodes a in
    BatIMap.mem na graph.edges
  with Not_found -> false

let has_edge a b graph =
  try
    let na = Hashtbl.find graph.nodes a
    and nb = Hashtbl.find graph.nodes b in
    let set = BatIMap.find na graph.edges in
    BatISet.mem nb set
  with Not_found -> false

let remove_node a graph =
  let na = Hashtbl.find graph.nodes a in
  graph.edges <- BatIMap.remove na graph.edges

let remove_edge a b graph =
  let na = Hashtbl.find graph.nodes a
  and nb = Hashtbl.find graph.nodes b in
  let set = BatIMap.find na graph.edges in
  let remove_b = BatISet.remove nb set in
  graph.edges <- BatIMap.add na remove_b graph.edges

(* The number of edges coming out of a given node A.  Build a graph with
   "reversed" edges if the number of incoming nodes is required.  *)

let num_edges a graph =
  let na = Hashtbl.find graph.nodes a in
  if BatIMap.mem na graph.edges then
    BatISet.cardinal (BatIMap.find na graph.edges)
  else
    0

type mark = Unmarked | Temporary | Permanent

exception Not_DAG

(* Assuming GRAPH is a DAG, build a topologically-sorted dependency list, such
   that items earlier in the list are not dependent on those later in the
   list.  An edge is a dependency if FROM depends on TO in the following:
   
     add_edge from to graph
   
   The exception Not_DAG is raised if the graph contains cycles.  *)

let tsort graph =
  let iht = Hashtbl.create 20 in
  (* Build an inverse hash table from node numbers to nodes.  Only put actual
     nodes in it (not things we might have removed).  *)
  Hashtbl.iter
    (fun k v -> if BatIMap.mem v graph.edges then Hashtbl.add iht v k)
    graph.nodes;
  let marks = Array.make graph.node_ctr Unmarked in
  let rec visit node_num outlist =
    match marks.(node_num) with
      Temporary -> raise Not_DAG
    | Unmarked ->
        marks.(node_num) <- Temporary;
	let set = BatIMap.find node_num graph.edges in
	let outlist =
	  BatISet.fold (fun to_node outlist -> visit to_node outlist) set
		       outlist in
	marks.(node_num) <- Permanent;
	node_num :: outlist
    | Permanent -> outlist in
  let rec iter outlist =
    let vs, ol = Hashtbl.fold
      (fun num _ (visited, outlist) ->
        match marks.(num) with
	  Unmarked -> true, visit num outlist
	| _ -> visited, outlist)
      iht
      (false, outlist) in
    if vs then
      iter ol
    else
      ol in
  List.rev_map (fun nn -> Hashtbl.find iht nn) (iter [])
