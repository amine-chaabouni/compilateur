
(** {2 Explicit Register Transfer Language (ERTL)} *)

open Ops

type ident = string
  (** uniquement pour les fonctions *)

type register = Register.t

type label = Label.t

(** Les différentes instructions ERTL *)
type instr =
  (** les mêmes que dans RTL *)
  | Econst of int32 * register * label
  | Eload of register * int * register * label
  | Estore of register * register * int * label
  | Emunop of munop * register * label
  | Embinop of mbinop * register * register * label
  | Emubranch of mubranch * register * label * label
  | Embbranch of mbbranch * register * register * label * label
  | Egoto of label
  | Ecall of ident * int * label
      (** l'entier est le nombre de paramètres passés dans des registres *)
  | Ealloc_frame of label
  | Edelete_frame of label
  | Eget_param of int * register * label
      (** [r <- ofs(rbp)] *)
  | Epush_param of register * label
  | Ereturn

type cfg = instr Label.map
  (** Un graphe de flot de contrôle est un dictionnaire associant à des
      étiquettes des instructions ERTL. *)

(** Une fonction ERTL. *)
type deffun = {
  fun_name : ident;
  fun_formals : int; (* nb total d'arguments *)
  fun_locals : Register.set;
  fun_entry : label;
  fun_body : cfg;
}

(** Un programme ERTL. *)
type file = {
  funs : deffun list;
}

(** {2 Calcul des définitions et utilisations de chaque instruction} *)

let rec prefix i = function
  | _ when i = 0 -> []
  | [] -> assert false
  | x :: r -> x :: prefix (i-1) r

let def_use = function
  | Econst (_,r,_)
  | Eget_param (_,r,_) ->
      [r], []
  | Emubranch (_,r,_,_)
  | Epush_param (r,_) ->
      [], [r]
  | Emunop (_,rd,_) ->
      [rd], [rd]
  | Embinop (Ops.Mmov,rs,rd,_)
  | Eload (rs,_,rd,_) ->
      [rd], [rs]
  | Embinop (Ops.Mdiv,rs,rd,_) ->
      assert (rd = Register.rax);
      [Register.rax; Register.rdx], [Register.rax; Register.rdx; rs]
  | Embinop (_,rs,rd,_) ->
      [rd], [rs; rd]
  | Estore (r1,r2,_,_)
  | Embbranch (_,r1,r2,_,_) ->
      [], [r1; r2]
  | Ecall (_,n,_) ->
      Register.caller_saved, prefix n Register.parameters
  | Egoto _
  | Ealloc_frame _
  | Edelete_frame _ ->
      [], []
  | Ereturn ->
      [], Register.rax :: Register.callee_saved

(** {2 Fonctions d'impression, pour debugger} *)

open Format
open Pp

let print_instr fmt = function
  | Econst (n, r, l) ->
      fprintf fmt "mov $%ld %a  --> %a" n Register.print r Label.print l
  | Eload (r1, n, r2, l) ->
      fprintf fmt "mov %d(%a) %a  --> %a"
        n Register.print r1 Register.print r2 Label.print l;
  | Estore (r1, r2, n, l) ->
      fprintf fmt "mov %a %d(%a)  --> %a"
        Register.print r1 n Register.print r2 Label.print l
  | Emunop (op, r1, l) ->
      fprintf fmt "%a %a  --> %a"
        print_munop op Register.print r1 Label.print l
  | Embinop (Mmov, r1, r2, l) ->
      fprintf fmt "mov %a %a  --> %a"
        Register.print r1 Register.print r2 Label.print l
  | Embinop (op, r1, r2, l) ->
      fprintf fmt "%a %a %a  --> %a"
	print_mbinop op Register.print r1 Register.print r2 Label.print l
  | Emubranch (op, r, l1, l2) ->
      fprintf fmt "%a %a  --> %a, %a"
	print_mubranch op Register.print r Label.print l1 Label.print l2
  | Embbranch (op, r1, r2, l1, l2) ->
      fprintf fmt "%a %a %a  --> %a, %a"
	print_mbbranch op Register.print r1 Register.print r2
        Label.print l1 Label.print l2
  | Egoto l ->
      fprintf fmt "goto %a" Label.print l
  | Ecall (x, n, l) ->
      fprintf fmt "call %s(%d)  --> %a" x n Label.print l
  | Ealloc_frame l ->
      fprintf fmt "alloc_frame  --> %a" Label.print l
  | Edelete_frame l ->
      fprintf fmt "delete_frame  --> %a" Label.print l
  | Eget_param (n, r, l) ->
      fprintf fmt "mov stackp(%d) %a --> %a" n Register.print r Label.print l
  | Epush_param (r, l) ->
      fprintf fmt "push %a  --> %a" Register.print r Label.print l
  | Ereturn ->
      fprintf fmt "return"

let succ = function
  | Econst (_,_,l)
  | Eload (_,_,_,l)
  | Estore (_,_,_,l)
  | Emunop (_,_,l)
  | Embinop (_,_,_,l)
  | Ecall (_,_,l)
  | Egoto l
  | Ealloc_frame l
  | Edelete_frame l
  | Eget_param (_,_,l)
  | Epush_param (_,l) ->
      [l]
  | Emubranch (_,_,l1,l2)
  | Embbranch (_,_,_,l1,l2) ->
      [l1; l2]
  | Ereturn ->
      []


exception Error of string

let raise_error  error =
  raise (Error error);;


type live_info = {
  instr: instr;
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
    let defs, uses = def_use instr in
    {
      instr = instr;
      succ = succ instr;
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


let print_set = Register.print_set

let print_label_set = Label.print_set

let print_label_list = Label.print_list




let print_live_info fmt li =
  fprintf fmt "d={%a}@ u={%a}@ i={%a}@ o={%a}"(* pred={%a} succ={%a}*)
    print_set li.defs print_set li.uses print_set li.ins print_set li.outs (*print_label_set li.pred print_label_list li.succ *)

let visit life_cycle f g entry =
  let map_info = liveness g in
  (*let ig = make map_info in
  let cm,i = colorize ig in*)
  let visited = Hashtbl.create 97 in
  let rec visit l =
    if not (Hashtbl.mem visited l) then begin
      Hashtbl.add visited l ();
      let i = Label.M.find l g in
      let info = Label.M.find l map_info in
      f l i info life_cycle;
      List.iter visit (succ i)
    end
  in
  visit entry;;
  (*
  print_ig ig;
  print_cm cm;;
  *)

let printed fmt l i info life_cycle = 
  if life_cycle then
    fprintf fmt "%a: %a %a@\n" Label.print l print_instr i print_live_info info
  else
    fprintf fmt "%a: %a@\n" Label.print l print_instr i


let print_graph fmt life_cycle=
  visit life_cycle (printed fmt)

let print_deffun fmt life_cycle f =
  fprintf fmt "%s(%d)@\n" f.fun_name f.fun_formals;
  fprintf fmt "  @[";
  fprintf fmt "entry : %a@\n" Label.print f.fun_entry;
  fprintf fmt "locals: @[%a@]@\n" Register.print_set f.fun_locals;
  print_graph fmt life_cycle f.fun_body f.fun_entry ;
  fprintf fmt "@]@."

let print_file fmt p life_cycle=
  fprintf fmt "=== ERTL =================================================@\n";
  List.iter (print_deffun fmt life_cycle) p.funs
