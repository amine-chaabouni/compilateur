exception Error of string

let raise_error  error =
  raise (Error error);;

type arcs = { mutable prefs: Register.set; mutable intfs: Register.set }

type igraph = arcs Register.map

let make info_map = 
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
  Label.M.iter (fun label info -> find_mov_instr info.instr) info_map;

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
  let fill_intfs info = 
    match info.instr with
    | Ertltree.Embinop (Ops.Mmov, rs, rd, _) -> begin
      let to_remove = Register.S.of_list [rs ; rd] in
      add_intfs rs (Register.S.diff info.outs to_remove)
    end
    | _ -> Register.S.iter (function d -> add_intfs d (Register.S.remove d info.outs) ) info.defs 
  in
  Label.M.iter (fun label info -> fill_intfs info) info_map;
  !ltl_graph;;




type color = Ltltree.operand
type coloring = color Register.map


exception Reg_Is_Colorable of Register.t
let find_colorable_register todo potentiels =
  let process_reg r =
    let potential_colors = Register.M.find r potentiels in
    if not (Register.S.is_empty potential_colors) then
      raise (Reg_Is_Colorable r)
    else
      ()
  in
  Register.S.iter process_reg todo

let colorize ig =
  let pseudo_registers = Seq.filter_map (function (r, _) -> if Register.is_pseudo r then Some r else None) (Register.M.to_seq ig) in 
  let todo = ref (Register.S.of_seq pseudo_registers) in
  let potentiels = ref Register.M.empty in
  let add__reg_to_potentiels r =
    let potential_colors = Register.S.diff Register.allocatable (Register.M.find r ig).intfs in
    potentiels := Register.M.add r potential_colors !potentiels
  in
  Register.S.iter add__reg_to_potentiels !todo;
  while not (Register.S.is_empty !todo) do
    try find_colorable_register !todo !potentiels with
    | Reg_Is_Colorable r -> 
      
    

(* Function to print igraph *)
let print ig =
  Register.M.iter (fun r arcs ->
    Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
      Register.print_set arcs.prefs Register.print_set arcs.intfs) ig