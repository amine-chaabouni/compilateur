type arcs = { mutable prefs: Register.set; mutable intfs: Register.set }

type igraph = arcs Register.map

let make (info_map:Ertltree.live_info Label.M.t) = 
  let ltl_graph = ref Register.M.empty in
  (* First loop to add preference arcs *)
  let find_arc register = 
    try 
      Register.M.find register !ltl_graph
    with Not_found -> begin
      let node = {prefs = Register.S.empty; intfs = Register.S.empty}
      in ltl_graph := Register.M.add register node !ltl_graph;
      node
    end
  in
  let find_mov_instr = function
    | Ertltree.Embinop (Ops.Mmov, rs, rd, _) -> if rs <> rd then begin
      let arc_rs = find_arc rs in arc_rs.prefs <- Register.S.add rd arc_rs.prefs;
      let arc_rd = find_arc rd in arc_rd.prefs <- Register.S.add rs arc_rd.prefs;
    end
    | _ -> ()
  in
  Label.M.iter (fun label (info:Ertltree.live_info) -> find_mov_instr info.instr) info_map;
  
  (* Second loop to add interference arcs *)
  let add_intfs register interfering = 
    let arc = find_arc register in
    let add_interference r =
      arc.intfs <- Register.S.add r arc.intfs;
      let other_arc = find_arc r in
      other_arc.intfs <- Register.S.add register other_arc.intfs
    in 
    Register.S.iter add_interference interfering
  in
  let fill_intfs (info:Ertltree.live_info) = 
    match info.instr with
    | Ertltree.Embinop (Ops.Mmov, rs, rd, _) -> begin
      let to_remove = Register.S.of_list [rs ; rd] in
      add_intfs rd (Register.S.diff info.outs to_remove)
    end
    | _ -> Register.S.iter (function d -> add_intfs d (Register.S.remove d info.outs) ) info.defs 
  in
  Label.M.iter (fun label info -> fill_intfs info) info_map;
  
  (* Remove the prefs that exist in intfs *)
  let clean_prefs r arc =
    arc.prefs <- Register.S.filter (fun r -> not(Register.S.mem r arc.intfs)) arc.prefs;
  in
  
  Register.M.iter clean_prefs !ltl_graph;
  !ltl_graph;;
  

(* Function to print igraph *)
let print_ig ig =
  Register.M.iter (fun r arcs ->
    Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
      Register.print_set arcs.prefs Register.print_set arcs.intfs) ig
  