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
    match op1, op2 with
    | Ltltree.Reg r1, Ltltree.Reg r2 -> Ltltree.Eload(r1, integer, r2, label)

    | Ltltree.Reg r1, Ltltree.Spilled s2 ->
      let label_mov_tmp_to_reg = generate(Ltltree.Embinop(Ops.Mmov, Ltltree.Reg Register.tmp1, Ltltree.Spilled (s2), label)) in
      Ltltree.Eload(r1, integer, Register.tmp1, label_mov_tmp_to_reg)
    
    | Ltltree.Spilled s1, Ltltree.Reg r2 ->
      let label_load_tmp_to_reg = generate(Ltltree.Eload(Register.tmp1, integer, r2, label)) in
      Ltltree.Embinop(Ops.Mmov, Ltltree.Spilled (s1), Ltltree.Reg Register.tmp1, label_load_tmp_to_reg)
    
    | Ltltree.Spilled s1, Ltltree.Spilled s2 ->
      let label_mov_tmp2_to_reg2 = generate(Ltltree.Embinop(Ops.Mmov, Ltltree.Reg Register.tmp2, Ltltree.Spilled (s2), label)) in
      let label_load_tmp1_in_tmp2 = generate(Ltltree.Eload(Register.tmp1, integer, Register.tmp2, label_mov_tmp2_to_reg2)) in
      Ltltree.Embinop(Ops.Mmov, Ltltree.Spilled (s1), Ltltree.Reg Register.tmp1, label_load_tmp1_in_tmp2)
  end

  | Ertltree.Estore(register1, register2, integer, label) -> begin
    let op1 = lookup colorization register1 and op2 = lookup colorization register2 in
    if(op1 = op2 && integer = 0) then Ltltree.Egoto label
    else match op1, op2 with
    | Ltltree.Reg r1, Ltltree.Reg r2 -> Ltltree.Estore(r1, r2, integer, label)
    
    | Ltltree.Reg r1, Ltltree.Spilled s2 ->
      let label_store_in_tmp = generate(Ltltree.Estore(r1, Register.tmp1, integer, label)) in
      Ltltree.Embinop(Ops.Mmov, Ltltree.Spilled (s2), Ltltree.Reg Register.tmp1, label_store_in_tmp)
    
    | Ltltree.Spilled s1, Ltltree.Reg r2 ->
      let label_store_from_tmp = generate(Ltltree.Estore(Register.tmp1, r2, integer, label)) in
      Ltltree.Embinop(Ops.Mmov, Ltltree.Spilled (s1), Ltltree.Reg Register.tmp1, label_store_from_tmp)
    
    | Ltltree.Spilled s1, Ltltree.Spilled s2 ->
      let label_store = generate(Ltltree.Estore(Register.tmp1, Register.tmp2, integer, label)) in
      let label_mov_s2 = generate(Ltltree.Embinop(Ops.Mmov, Ltltree.Spilled (s2), Ltltree.Reg Register.tmp2, label_store)) in
      Ltltree.Embinop(Ops.Mmov, Ltltree.Spilled (s1), Ltltree.Reg Register.tmp1, label_mov_s2)
  end
  | Ertltree.Egoto label -> Ltltree.Egoto label
  | Ertltree.Ereturn -> Ltltree.Ereturn
  (* Change register with operand *)
  | Ertltree.Econst (integer, register, label) -> Ltltree.Econst(integer, lookup colorization register, label)
  | Ertltree.Emunop (munop, register, label) -> Ltltree.Emunop(munop, lookup colorization register, label)
  | Ertltree.Embinop (binop, register1, register2, label) -> begin 
    let operand1 = lookup colorization register1 and operand2 = lookup colorization register2 in
    (* In case the instruction is mov %rax %rax, just ignore it and go to the next instruction *)
    if(binop = Ops.Mmov && operand1 = operand2) then Ltltree.Egoto label
    else
    match binop with
    | Ops.Mmul -> begin
      match operand2 with
      | Ltltree.Reg r2 -> Ltltree.Embinop(Ops.Mmul, operand1, Ltltree.Reg r2, label)
      | Ltltree.Spilled s2 -> begin
        let label_mov_back = generate(Ltltree.Embinop(Ops.Mmov, Ltltree.Reg Register.tmp1, Ltltree.Spilled s2, label)) in
        let label_mul = generate(Ltltree.Embinop(Ops.Mmul, operand1, Ltltree.Reg Register.tmp1, label_mov_back)) in
        Ltltree.Embinop(Ops.Mmov, Ltltree.Spilled s2, Ltltree.Reg Register.tmp1, label_mul);
      end
    end
    | _ ->
      match operand1, operand2 with
      (* Binop instruction can't have both operands on stack *)
      | Ltltree.Spilled s1, Ltltree.Spilled s2 -> begin
        let label_binop = generate(Ltltree.Embinop(binop, Ltltree.Reg Register.tmp1, Ltltree.Spilled s2, label)) in
        Ltltree.Embinop(Ops.Mmov, Ltltree.Spilled s1, Ltltree.Reg Register.tmp1, label_binop);
      end
      | _ -> Ltltree.Embinop(binop, operand1, operand2, label)
  end
  | Ertltree.Emubranch (mubranch, register, label1, label2) -> Ltltree.Emubranch(mubranch, lookup colorization register, label1, label2)
  | Ertltree.Embbranch (mbbranch, register1, register2, label1, label2) -> Ltltree.Embbranch(mbbranch, lookup colorization register1, lookup colorization register2, label1, label2)
  | Ertltree.Epush_param (register, label) -> Ltltree.Epush(lookup colorization register, label)
  (* Call instruction *)
  | Ertltree.Ecall(ident, integer, label) -> Ltltree.Ecall(ident, label)
  (* Alloc and delete frame *)
  | Ertltree.Ealloc_frame label -> begin
    let label_add = if m<>0 then
      generate (Ltltree.Emunop(Ops.Maddi (Int32.of_int (m)), Ltltree.Reg Register.rsp, label))
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
    | Ltltree.Spilled s-> begin
      let label_mov_tmp_to_stack = generate(Ltltree.Embinop(Ops.Mmov, Ltltree.Reg Register.tmp1, Ltltree.Spilled s, label)) in
      Ltltree.Eload(Register.rbp, integer, Register.tmp1, label_mov_tmp_to_stack)
    end
  end
  in associate label converted_instruction;;

let convert_graph ertl_graph =
  let map_info = Ertltree.liveness ertl_graph in
  let igraph = Interference.make map_info in
  let colorization, m = Colorize.colorize igraph in
  Label.M.iter (convert_instr colorization m) ertl_graph;;



let convert_ertl (fun_def:Ertltree.deffun) =
  convert_graph fun_def.fun_body;

  {
    fun_name = fun_def.fun_name;
    fun_entry = fun_def.fun_entry;
    fun_body = !ltl_graph;
  };;


let program (p:Ertltree.file) =
  let deffun = List.map convert_ertl p.funs in
  {funs = deffun};;