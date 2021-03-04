open Ltltree

exception Error of string
let ltl_graph = ref Label.M.empty;;

let generate i =
  let l = Label.fresh () in
  ltl_graph := Label.M.add l i !ltl_graph;
  l

let associate l i =
  ltl_graph := Label.M.add l i !ltl_graph;;
  

let lookup c r =
  if Register.is_hw r then Reg r else Register.M.find r c


let convert_instr colorization m label instr = 
  let converted_instruction = match instr with
  (* Unchanged instructions *)
  | Ertltree.Eload(register1, integer, register2, label) -> begin
    let op1 = lookup colorization register1 and op2 = lookup colorization register2 in
    if(op1 = op2 && integer = 0) then Ltltree.Egoto label
    else match op1, op2 with
    | Ltltree.Reg r1, Ltltree.Reg r2 -> 
      Ltltree.Eload(r1, integer, r2, label)
    | _ -> Ltltree.Eload(register1, integer, register2, label)
  end
  | Ertltree.Estore(register1, register2, integer, label) -> begin
    let op1 = lookup colorization register1 and op2 = lookup colorization register2 in
    if(op1 = op2 && integer = 0) then Ltltree.Egoto label
    else match op1, op2 with
    | Ltltree.Reg r1, Ltltree.Reg r2 -> 
      Ltltree.Estore(r1, r2, integer, label)
    | _ -> Ltltree.Estore(register1, register2, integer, label)
  end
  | Ertltree.Egoto label -> Ltltree.Egoto label
  | Ertltree.Ereturn -> Ltltree.Ereturn
  (* Change register with operand *)
  | Ertltree.Econst (integer, register, label) -> Ltltree.Econst(integer, lookup colorization register, label)
  | Ertltree.Emunop (munop, register, label) -> Ltltree.Emunop(munop, lookup colorization register, label)
  | Ertltree.Embinop (binop, register1, register2, label) -> begin 
    (* In case the instruction is mov %rax %rax, just ignore it and go to the next instruction *)
    let operand1 = lookup colorization register1 and operand2 = lookup colorization register2 in
    if(binop = Ops.Mmov && operand1 = operand2) then Ltltree.Egoto label
    else Ltltree.Embinop(binop, operand1, operand2, label)
  end
  | Ertltree.Emubranch (mubranch, register, label1, label2) -> Ltltree.Emubranch(mubranch, lookup colorization register, label1, label2)
  | Ertltree.Embbranch (mbbranch, register1, register2, label1, label2) -> Ltltree.Embbranch(mbbranch, lookup colorization register1, lookup colorization register2, label1, label2)
  | Ertltree.Epush_param (register, label) -> Ltltree.Epush(lookup colorization register, label)
  (* Call instruction *)
  | Ertltree.Ecall(ident, integer, label) -> Ltltree.Ecall(ident, label)
  (* Alloc and delete frame *)
  | Ertltree.Ealloc_frame label -> begin
    let label_add = if m<>0 then
      generate (Ltltree.Emunop(Ops.Maddi (Int32.of_int(-8*m)), Ltltree.Reg Register.rsp, label))
    else label
    in
    let label_mov = generate (Ltltree.Embinop(Ops.Mmov, Ltltree.Reg Register.rsp, Ltltree.Reg Register.rbp, label_add)) in
    let instruction_push = Ltltree.Epush(Ltltree.Reg Register.rbp, label_mov) in
    instruction_push
  end
  | Ertltree.Edelete_frame label -> begin
    let label_pop = generate(Ltltree.Epop(Register.rbp, label)) in
    let instruction_mov = Ltltree.Embinop(Ops.Mmov, Ltltree.Reg Register.rbp, Ltltree.Reg Register.rsp, label_pop) in
    instruction_mov
  end
  (* Get param*)
  | Ertltree.Eget_param(integer, register, label) -> begin
    let op = lookup colorization register in
    match op with
    | Ltltree.Reg r -> Ltltree.Eload(Register.rbp, integer, r, label)
    | _ -> Ltltree.Eload(Register.rbp, integer, register, label)
  end
  in associate label converted_instruction;;

let convert_graph ertl_graph m =
  let map_info = Ertltree.liveness ertl_graph in
  let igraph = Interference.make map_info in
  let colorization, nb_spilled = Colorize.colorize igraph in
  Label.M.iter (convert_instr colorization m) ertl_graph;;



let convert_ertl (fun_def:Ertltree.deffun) =
  convert_graph fun_def.fun_body (Register.S.cardinal fun_def.fun_locals);

  {
    fun_name = fun_def.fun_name;
    fun_entry = fun_def.fun_entry;
    fun_body = !ltl_graph;
  };;


let program (p:Ertltree.file) =
  let deffun = List.map convert_ertl p.funs in
  {funs = deffun};;