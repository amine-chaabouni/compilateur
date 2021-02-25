
open Ertltree

let word_size = 8


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
  | Eload (r1, n, r2, l) -> assert(n mod word_size ==0); Eload (r1, n, r2, l)
  | Estore (r1, r2, n, l) -> assert(n mod word_size ==0); Estore (r1, r2, n, l)
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
  let k = min nb_args 6 in

  (* Deplier les arguments mis sur la pile *)
  let unfold_params label register =
    index_param := !index_param+1;
    if(!index_param < k) then
      label
    else 
      let position = (!index_param - k)*word_size in (*octets refering to the position of the arguments*)
      let register = Register.fresh() in
      generate (Eload(Register.rsp, position, register, label)) in

  let label_unfold = List.fold_left unfold_params l r_list in
  assert(!index_param = nb_args-1);
  
  (* Copy the result in rax *)
  let label_result = generate (Embinop(Ops.Mmov, Register.result, r, label_unfold)) in

  (* Function call *)
  let instruction_call = Ecall(id, k, label_result) in

  (* Put the formals inside Register.parameters or on the stack if too many *)
  (* Can do the same with labels and return a Goto instruction *)
  index_param := -1;
  let fold_params instr register =
    index_param := !index_param+1;
    if(!index_param < k) then
      let label = generate instr in
      let instruction_fold = Embinop(Ops.Mmov, register, List.nth Register.parameters !index_param, label)
      in
      instruction_fold
    else begin
      let label = generate instr in Epush_param(register, label) end; 
  in
  let instruction_fold = List.fold_left fold_params instruction_call r_list in
  assert(!index_param = nb_args-1);
  instruction_fold;;

let allocate_activation_table local_registers new_regs nb_args entry_label =
  (* Retrieve function arguments from Register.parameters and from the stack *)
  let k = min nb_args 6 in

  let label_retrieve = ref entry_label in

  for i = 1 to k do
    label_retrieve := generate (Embinop(Ops.Mmov, List.nth Register.parameters (i-1), List.nth local_registers (i-1), !label_retrieve));
  done;

  if(nb_args > k) then
    (* if nb_args = 7, then do it once. from 6 to (7-1)=6 *)
    for i = k to nb_args-1 do
      (* rbp contains the ancient rsp so the index can't be 0
      8(%rbp) is the return adress
      And thus, we should start looking at 16(%rbp) so we add 2 to our index*)
      label_retrieve := generate (Eget_param((i-k+2)*word_size, List.nth local_registers i, !label_retrieve))
    done;
    

  (* Save callee-saved registers in fresh pseudo_registers*)
  let save_register label register =
    let pseudo_register = Register.fresh() in
    Hashtbl.add new_regs pseudo_register register;
    generate(Embinop(Ops.Mmov, register, pseudo_register, label)) in
  let label_save_register = List.fold_left save_register !label_retrieve Register.callee_saved
  in
  (* Allocate activation table *)
  let label_alloc = generate (Ealloc_frame(label_save_register)) in
  label_alloc;;

let delete_activation_table new_regs register_result = 
  (* Add a return instruction *)
  let label_return = generate (Ereturn) in
  (* Delete activation table *)
  let label_delete = generate (Edelete_frame(label_return)) in


  (* Restore saved registers *)
  let label_restore_saved_registers = Hashtbl.fold 
    (fun pseudo register label -> generate(Embinop(Ops.Mmov, pseudo, register, label)))
    new_regs label_delete in

  (* Copy result in Register.result *)
  let label_copy_result = generate(Embinop(Ops.Mmov, register_result, Register.result, label_restore_saved_registers))
  in label_copy_result;;

  

(* Creation of the ertl graph and returns the new entry label *)
let convert_graph rtl_graph nb_args local_registers register_result entry_label =
  Label.M.iter convert_instr rtl_graph;
  let new_regs = Hashtbl.create 16 in
  let label_allocate = allocate_activation_table local_registers new_regs nb_args entry_label in
  let label_delete = delete_activation_table new_regs register_result in
  label_allocate, label_delete;;



let convert_rtl (fun_def:Rtltree.deffun) =
  let nb_args = List.length fun_def.fun_formals in
  (*let local_variables = Register.S.elements fun_def.fun_locals in*)
  let label_entry, label_delete = convert_graph fun_def.fun_body nb_args fun_def.fun_formals fun_def.fun_result fun_def.fun_entry in
  associate fun_def.fun_exit (Egoto label_delete);
  {
    fun_name = fun_def.fun_name;
    fun_formals = nb_args;
    fun_locals = fun_def.fun_locals;
    fun_entry = label_entry;
    fun_body = !ertl_graph;
  };;

let program (p:Rtltree.file) =
  let deffun = List.map convert_rtl p.funs in
  {funs = deffun};;