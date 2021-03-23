exception Error of string

let raise_error  error =
  raise (Error error);;


type live_info = {
  instr: Ertltree.instr;
  succ: Label.t list;             (* successeurs *)
  mutable pred: Label.set;        (* prédécesseurs *)
  defs: Register.set;             (* définitions *)
  uses: Register.set;             (* utilisations *)
  mutable  ins: Register.set;     (* variables vivantes en entrée *)
  mutable outs: Register.set;     (* variables vivantes en sortie *)
}




let liveness cfg =
  let info_map = ref Label.M.empty in

  (* Remplir le tableau à partir du graphe de flot de contrôle *)
  let convert_instr_info instr =
    let defs, uses = Ertltree.def_use instr in
    {
      instr = instr;
      succ = Ertltree.succ instr;
      pred = Label.S.empty;
      defs = Register.S.of_list defs;
      uses = Register.S.of_list uses;
      ins = Register.S.empty;
      outs = Register.S.empty;
    } in
  Label.M.iter (fun label instr -> info_map := Label.M.add label (convert_instr_info instr) !info_map) cfg;


  (* Parcourir le tableau pour remplir pred *)
  let fill_pred label info =
    (* To this one successor, tell that info is a predecessor *)
    let from_succ_to_pred successor = 
      let succ_info = try
        Label.M.find successor !info_map
      with Not_found -> raise_error "Not_found in filling preds. Should not happen."
      in succ_info.pred <- Label.S.add label succ_info.pred;
    in
    List.iter from_succ_to_pred info.succ in
  Label.M.iter fill_pred !info_map;

  (* Kildall's Algorithm *)
  (* Keep a list of labels to work on *)
  let list_labels = ref Label.S.empty in
  Label.M.iter (fun label info -> list_labels := Label.S.add label !list_labels;) !info_map;
  
  (* Update ins and outs *)
  let update label = 
    (* Making the union of this successor's ins and previous ins *)
    let gather_succ_ins union_ins successor = 
      let succ_info = try
        Label.M.find successor !info_map
      with Not_found -> raise_error "Not found in gathering ins. Should not happen."
      in
      Register.S.union union_ins succ_info.ins
    in

    (* Putting the predecessors in the list *)
    let add_preds_to_list predecessors = 
      Label.S.iter (fun label -> list_labels := Label.S.add label !list_labels;) predecessors
    in

    (* Get the info of the label and update ins and outs *)
    let info = try
      Label.M.find label !info_map
    with Not_found -> raise_error "Not found in updating ins/outs. Should not happen."
    in
    let old_in = info.ins in
    info.outs <- List.fold_left gather_succ_ins Register.S.empty info.succ;
    info.ins <- Register.S.union info.uses (Register.S.diff info.outs info.defs);
    if not (Register.S.equal old_in info.ins) then
      add_preds_to_list info.pred;

  in


  (* Iterate on the list of labels to update *)
  let rec iterator() = 
    (*print_string "iterator \n";*)
    if(not(Label.S.is_empty !list_labels)) then
      begin
        let label = Label.S.min_elt !list_labels in
        list_labels := Label.S.remove label !list_labels;
        update label;
        iterator();
      end
    else ();
  in

  
  iterator();
    

  !info_map;;


(* Fonction de d'impression pour debugger *)
open Format
open Pp

let print_set = Register.print_set

let print_label_set = Label.print_set

let print_label_list = Label.print_list

let print_live_info fmt li =
  fprintf fmt "%a@ d={%a}@ u={%a}@ i={%a}@ o={%a}"(*@ pred={%a}@ succ={%a}*)
    Ertltree.print_instr li.instr print_set li.defs print_set li.uses print_set li.ins print_set li.outs (*print_label_set li.pred print_label_list li.succ *)



(* Functions used to print an ERTL code's liveness for debugging *)
let visit f g entry =
  let visited = Hashtbl.create 97 in
  let rec visit l =
    if not (Hashtbl.mem visited l) then begin
      Hashtbl.add visited l ();
      let i = Label.M.find l g in
      f l i;
      List.iter visit (Ertltree.succ i.instr)
    end
  in
  visit entry;;

let print_liveness fmt l info = 
  fprintf fmt "%a: %a@\n" Label.print l print_live_info info
  
let print_graph fmt = 
  visit (print_liveness fmt)

let program (p:Ertltree.file) =
  List.iter (fun (f:Ertltree.deffun) -> let info = liveness f.fun_body in (print_graph std_formatter) info f.fun_entry) p.funs