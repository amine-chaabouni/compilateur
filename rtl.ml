
open Rtltree

let zero_i32 = Int32.of_int 0;;
let one_i32 = Int32.of_int 1;;

exception Error of string

let raise_error  error =
  raise (Error error);;

let graph = ref Label.M.empty

let functions = (Hashtbl.create 16 : (string, string list) Hashtbl.t);;

let var_to_reg = (Hashtbl.create 16 : (string, Register.t) Hashtbl.t);;


let generate i =
  let l = Label.fresh () in
  graph := Label.M.add l i !graph;
  l

let print_vars ht =
  Hashtbl.iter (fun x y -> Printf.printf "%s\n" x) ht

let rec treat_params local_reg = function
  | [], [] -> [];
  | [], _ -> raise_error "too many arguments";
  | _, [] -> raise_error "not enough arguments";
  | hd::tl, e_hd::e_tl ->(
    let register = Register.fresh() in
    register::treat_params local_reg (tl,e_tl));;

(*e est l'expression à traduire,
  destr le registre de destination de la valeur de cette expression
  destl l'étiquette où il faut transférer ensuite le contrôle*)
let rec expr e destr destl local_reg = match e with
  | Ttree.Econst cst -> Rtltree.Econst(cst, destr, destl)
  | Ttree.Eunop (unop, e) -> treat_unop local_reg e destr destl unop
  | Ttree.Ebinop (binop, e1, e2) -> treat_binop local_reg e1 e2 destr destl binop
  | Ttree.Eassign_local (id, e) -> begin
    print_string ("assigning to " ^ id ^ "\n");
    (* Find the register associated to the variable.
    If the register doesn't exist already, create a fresh one
    Add the association to the table and add the register to the locals*)
    let register = try
      Hashtbl.find var_to_reg id
    with Not_found -> Register.fresh() in
    Hashtbl.replace var_to_reg id register;
    local_reg := Register.S.add register !local_reg;
    (*let reg_e = Register.fresh() in
    let instruction_local_assign = Rtltree.Embinop(Ops.Mmov, reg_e, register, destl) in
    let label_local_assign = generate instruction_local_assign in*)
    let instruction_right = expr e.expr_node register destl local_reg in
    instruction_right;
  end;
  | Ttree.Eaccess_local id -> begin
    print_string ("accessing " ^ id ^ "\n");
    (* Find the register associated to the variable.
    If the register doesn't exist already, create a fresh one
    Add the association to the table and add the register to the locals*)
    let register = try
      Hashtbl.find var_to_reg id
    with Not_found -> Register.fresh() in
    Hashtbl.replace var_to_reg id register;
    local_reg := Register.S.add register !local_reg;
    Rtltree.Embinop(Ops.Mmov, register, destr, destl);
  end;
  | Ttree.Ecall (id, expr_list) -> begin
    let id_param = try 
      Hashtbl.find functions id;
    with Not_found -> raise_error "No such function" in
    let reg_list = treat_params local_reg (id_param,expr_list) in
    Rtltree.Ecall(destr, id, reg_list, destl);
  end;

  | _ -> raise_error "expression not yet implemented";


and treat_unop local_reg e destr destl = function
  | Ptree.Uminus -> begin
    (*  put 0 in a register
        put our value in a register
        do the difference between the two registers*)
    let reg_e = Register.fresh() in
    let instruction_binop = Embinop(Ops.Msub, reg_e, destr, destl) in
    let label_binop = generate instruction_binop in
    let instruction_put_e = expr e.expr_node reg_e label_binop local_reg in
    let label_put_e = generate instruction_put_e in
    let instruction_put_zero = expr (Ttree.Econst zero_i32) destr label_put_e local_reg in
    instruction_put_zero
  end;
  | Ptree.Unot -> begin
    (*  put our value in a register
        see if zero*)
    let instruction_setei = Emunop(Ops.Msetei zero_i32, destr, destl) in
    let label_setei = generate instruction_setei in
    let instruction_put_e = expr e.expr_node destr label_setei local_reg in
    instruction_put_e
  end;

and treat_binop local_reg e1 e2 destr destl binop = 
  (*Place each expression in a register
  If we are comparing, use Msub to compare with zero and then use the appropriate operation
  Else, use the appropriate operation (add, sub, div, mul)*)
  print_string "binop\n";
  let reg_e2 = Register.fresh() in
  let label_next = ref destl in
  let operation = match binop with
  | Ptree.Beq -> 
    boolean_op Ops.Msete destr destl label_next local_reg;
    Ops.Msub;
  | Ptree.Bneq-> 
    boolean_op Ops.Msetne destr destl label_next local_reg;
    Ops.Msub;
  | Ptree.Blt ->  
    boolean_op Ops.Msetl destr destl label_next local_reg;
    Ops.Msub;
  | Ptree.Ble ->
    boolean_op Ops.Msetle destr destl label_next local_reg;
    Ops.Msub;
  | Ptree.Bgt ->
    boolean_op Ops.Msetg destr destl label_next local_reg;
    Ops.Msub;
  | Ptree.Bge ->
    boolean_op Ops.Msetge destr destl label_next local_reg;
    Ops.Msub;
  | Ptree.Badd -> Ops.Madd
  | Ptree.Bsub -> Ops.Msub
  | Ptree.Bmul -> Ops.Mmul
  | Ptree.Bdiv -> Ops.Mdiv
  | _ -> raise_error "and/or operation not yet implemented" in

  let instruction_binop =  Embinop(operation, reg_e2, destr, !label_next) in
  let label_binop = generate instruction_binop in
  let instruction_put_e2 = expr e2.expr_node reg_e2 label_binop local_reg in
  let label_put_e2 = generate instruction_put_e2 in
  let instruction_put_e1 = expr e1.expr_node destr label_put_e2 local_reg in
  instruction_put_e1

and boolean_op op destr destl label_next local_reg =
  let reg_zero = Register.fresh() in
  let instruction_sete = Embinop(op, reg_zero, destr, destl) in
  label_next := generate instruction_sete;
  let instruction_put_zero = expr (Ttree.Econst zero_i32) reg_zero !label_next local_reg in
  label_next := generate instruction_put_zero

let condition_boolean_op binop (e1: Ttree.expr) (e2: Ttree.expr) truel falsel local_reg =
  let reg_e1 = Register.fresh() and reg_e2 = Register.fresh() in
  let r1 = ref reg_e1 and r2 = ref reg_e2 in
  let op = match binop with
  | Ptree.Blt -> Ops.Mjl;
  | Ptree.Ble -> Ops.Mjle
  | Ptree.Bgt -> r1 := reg_e2; r2 := reg_e1; Ops.Mjl
  | Ptree.Bge -> r1 := reg_e2; r2 := reg_e1; Ops.Mjle
  | _ -> raise_error "ha" in
  let instruction_branch = Embbranch(op, !r2, !r1, truel, falsel) in
  let label_binop = generate instruction_branch in
  let instruction_put_e2 = expr e2.expr_node reg_e2 label_binop local_reg in
  let label_put_e2 = generate instruction_put_e2 in
  let instruction_put_e1 = expr e1.expr_node reg_e1 label_put_e2 local_reg in
  instruction_put_e1;;

let rec condition e truel falsel local_reg = match e with
  |Ttree.Ebinop (binop, e1, e2) -> (match binop with
    | Blt | Ble | Bgt | Bge ->
      (*This is treated as x <= y or x < y*)
      condition_boolean_op binop e1 e2 truel falsel local_reg;
    | Band ->
      (*Put as truel for the first expression the label of the second expression*)
      let instruction_put_e2 = condition e2.expr_node truel falsel local_reg in
      let label_convert_e2 = generate instruction_put_e2 in
      let instruction_put_e1 = condition e1.expr_node label_convert_e2 falsel local_reg in
      instruction_put_e1
    | Bor ->
      (*Put as falsel for the first expression the label of the second expression*)
      let instruction_put_e2 = condition e2.expr_node truel falsel local_reg in
      let label_convert_e2 = generate instruction_put_e2 in
      let instruction_put_e1 = condition e1.expr_node  truel label_convert_e2 local_reg in
      instruction_put_e1
    | _ -> begin (*add, sub, mul div*)
      let register = Register.fresh() in
      let instruction_branch = Rtltree.Emubranch(Ops.Mjz, register, falsel, truel) in
      let label_branch = generate instruction_branch in
      expr e register label_branch local_reg
    end;)
  | _ -> begin
    let register = Register.fresh() in
    let instruction_branch = Rtltree.Emubranch(Ops.Mjz, register, falsel, truel) in
    let label_branch = generate instruction_branch in
    expr e register label_branch local_reg;
  end;;

let rec stmt s destl retr exitl local_reg = match s with
  | Ttree.Sreturn e -> let converted_e = expr e.expr_node retr exitl local_reg in generate converted_e;
  | Ttree.Sblock b  -> begin 
      let decl_list, stmt_list = b in 
      let rec treat_block l = function
        | hd_s::tl -> let label = stmt hd_s l retr exitl local_reg in treat_block label tl; 
        | [] -> l;
      in treat_block destl (List.rev stmt_list);
    end
  | Ttree.Sexpr e -> let converted_e = expr e.expr_node retr destl local_reg in generate converted_e;
  | Ttree.Sif (e, s1, s2) -> begin
      let truel = stmt s1 destl retr exitl local_reg
      and falsel = stmt s2 destl retr exitl local_reg in
      let instruction_branching = condition e.expr_node truel falsel local_reg in
      generate instruction_branching
    end; 
  | Ttree.Swhile (e, s) -> begin
    let label_expression = Label.fresh() in
    let go_to_label = generate (Egoto label_expression) in
    let loop_label = stmt s go_to_label retr exitl local_reg in
    let instruction_expression = condition e.expr_node loop_label destl local_reg in
    graph := Label.M.add label_expression instruction_expression !graph;
    label_expression
  end;
  | Ttree.Sskip ->  destl;;


let rec treat_formals = function
  | hd::tl -> let _, param = hd in param::(treat_formals tl)
  | [] -> [];;


let deffun (fun_definition:Ttree.decl_fun) = 
  let name = fun_definition.fun_name in
  let id_params = treat_formals fun_definition.fun_formals in
  Hashtbl.add functions name id_params;
  graph := Label.M.empty;
  let retr = Register.fresh() 
  and exitl = Label.fresh()
  and local_reg = ref Register.S.empty in
  let entryl = stmt (Ttree.Sblock fun_definition.fun_body) exitl retr exitl local_reg
  in
  (*if Register.S.is_empty !local_reg then print_string "empty :o \n" else print_string "ok\n";*)
  {
    fun_name = name;
    fun_formals = [];
    fun_result = retr;
    fun_locals = !local_reg;
    fun_entry  = entryl;
    fun_exit   = exitl;
    fun_body   = !graph;
  };;


let program (p:Ttree.file) =
  let rec aux = function
    | hd::tl -> let converted_func = deffun hd in converted_func::aux tl;
    | [] -> []
  in {funs = aux p.funs};;