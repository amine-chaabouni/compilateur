
open Ertltree

exception Error of string

let raise_error  error =
  raise (Error error);;

let ertl_graph = ref Label.M.empty

let generate i =
  let l = Label.fresh () in
  ertl_graph := Label.M.add l i !ertl_graph;
  l

let associate l i =
  ertl_graph := Label.M.add l i !ertl_graph;;

let rec convert_instr label (rtl_instr:Rtltree.instr) =
  let ertl_instr = match rtl_instr with
  | Econst (n, r, l) -> Econst(n, r, l)
  | Eload (r1, n, r2, l) -> Eload (r1, n, r2, l)
  | Estore (n, r1, r2, l) -> Estore (n, r1, r2, l)
  | Emunop (munop, r, l) -> Emunop (munop, r, l)
  | Embinop (binop, r1, r2, l) -> begin
    match binop with 
    | Ops.Mdiv -> treat_div r1 r2 l
    | _ -> Embinop (binop, r1, r2, l)
  end;
  | Emubranch (mubranch, r, l1, l2) -> Emubranch (mubranch, r, l1, l2)
  | Embbranch (mbbranch, r1, r2, l1, l2) -> Embbranch (mbbranch, r1, r2, l1, l2)
  | Egoto l -> Egoto l
  | Ecall (r, id, r_list, l) -> treat_call r id r_list l
  in
  associate label ertl_instr

and treat_div r1 r2 l =
  let instruction_mov_rax_r2 = Embinop(Ops.Mmov, Register.rax, r2, l) in
  let label_mov_rax_r2 = generate instruction_mov_rax_r2 in
  let instruction_div = Embinop(Ops.Mdiv, r1, Register.rax, label_mov_rax_r2) in
  let label_div = generate instruction_div in
  let instruction_mov_r2_rax = Embinop(Ops.Mmov, r2, Register.rax, label_div) in
  instruction_mov_r2_rax

and treat_call r id r_list l =

  let nb_args = List.length r_list in
  let index_param = ref (-1) in
  let k = if(nb_args > 6) then 6 else nb_args in

  let unfold_params label register =
    index_param := !index_param+1;
    if(!index_param < k) then
      label
    else 
      let position = (!index_param - k)*8 in (*octets refering to the position of the arguments*)
      generate (Eget_param(position, Register.rsp, label)) in

  let label_unfold = List.fold_left unfold_params l r_list in
  
  let label_result = generate (Embinop(Ops.Mmov, Register.result, r, label_unfold)) in

  let instruction_call = Ecall(id, k, label_result) in

  (* Can do the same with labels and return a Goto instruction *)
  let fold_params instr register =
    if(!index_param < k) then
      let label = generate instr in
      let instruction_fold = Embinop(Ops.Mmov, register, List.nth Register.parameters !index_param, label)
      in index_param := !index_param+1;
      instruction_fold
    else let label = generate instr in Epush_param(register, label) in
  index_param := 0;
  let instruction_fold = List.fold_left fold_params instruction_call r_list in
  instruction_fold;;



let convert_graph rtl_graph =
  Label.M.iter convert_instr rtl_graph;;


let convert_rtl (fun_def:Rtltree.deffun) =
  convert_graph fun_def.fun_body;
  associate fun_def.fun_exit Ereturn;
  {
    fun_name = fun_def.fun_name;
    fun_formals = List.length fun_def.fun_formals;
    fun_locals = fun_def.fun_locals;
    fun_entry = fun_def.fun_entry;
    fun_body = !ertl_graph;
  };;

let program (p:Rtltree.file) =
  let deffun = List.map convert_rtl p.funs in
  {funs = deffun};;