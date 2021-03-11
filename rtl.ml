open Format
open Pp
open Rtltree

let zero_i32 = Int32.of_int 0;;
let one_i32 = Int32.of_int 1;;

let word_size = 8;;

exception Error of string

let raise_error  error =
  raise (Error error);;


let functions = (Hashtbl.create 16 : (string, string list) Hashtbl.t);;
Hashtbl.add functions "putchar" ("c"::[]);;
Hashtbl.add functions "sbrk" ("n"::[]);;

let var_to_reg = Stack.create();;

exception Register_Found of Register.t
let associate_register id =
  let find_in_block block_hashtbl = try
    raise (Register_Found (Hashtbl.find block_hashtbl id))
  with Not_found -> ()
  in try
    Stack.iter find_in_block var_to_reg;
    raise_error ("Undeclared variable " ^ id);
  with Register_Found x -> x;;

(* RTL graph*)
let graph = ref Label.M.empty

let generate i =
  let l = Label.fresh () in
  graph := Label.M.add l i !graph;
  l

(* See the variables inside a certain hashtable *)
let print_vars ht =
  Hashtbl.iter (fun x y -> Printf.printf "%s\n" x) ht



(*e is the expression to be converted,
destr is the register of destinition to the expression's value
destl is the label where the control should be transfered after the conversion*)
  
(* An implementation can is proposed for a certain feature :
let's say we have this function : 
1 int f(){
2   int x = 65;
3   { int x = x + 1; putchar(x); }
4   putchar(x);
5   return 0;
6 }
In C, we have written an undefined behaviour. the result will be @A where @ can be anything.
This is what has been implemented.
However, we can change the compiler to have line 3 use the previously declared x before declaring
a new x inside the new block. The result would be BA.
In order to do that, we uncomment the last argument (last_id) of the function expr
last_id is used to treat the instuction [int x = x], for exemple, using different x*)
let rec expr e destr destl (*last_id*) = match e with
  | Ttree.Econst cst -> generate (Rtltree.Econst(cst, destr, destl))
  | Ttree.Eunop (unop, e) -> treat_unop e destr destl unop
  | Ttree.Ebinop (binop, e1, e2) -> begin
    match binop with
    (* Treat && and || as a branch *)
    | Ptree.Band | Ptree.Bor -> 
      let truel = Label.fresh() and falsel = Label.fresh() in
      let label = condition e truel falsel in
      graph := Label.M.add falsel (Rtltree.Econst(zero_i32, destr, destl)) !graph;
      graph := Label.M.add truel (Rtltree.Econst(one_i32, destr, destl)) !graph;
      label;
    | Ptree.Beq  -> treat_immediate e1 e2 destr destl Ops.Msete (*last_id*)
    | Ptree.Bneq  -> treat_immediate e1 e2 destr destl Ops.Msetne (*last_id*)
    | Ptree.Badd -> treat_immediate e1 e2 destr destl Ops.Madd (*last_id*)
    (* For the rest, treat it normally *)
    | _ -> treat_binop e1 e2 destr destl binop (*last_id*)
  end;
  | Ttree.Eassign_local (id, e) -> begin
    (*let actual_block =  if (id = last_id) then 
      try
        Stack.pop var_to_reg
      with Stack.Empty -> raise_error("Empty here access local")
    else Hashtbl.create 1 in*)

    (* Find the register associated to the variable *)
    let register = associate_register id in
    
    let instruction_assign = Rtltree.Embinop(Ops.Mmov, destr, register, destl) in
    let label_assign = generate instruction_assign in
    let label_expression = expr e.expr_node destr label_assign (*""*) in

    (*if(id = last_id) then Stack.push actual_block var_to_reg;*)
    label_expression;
  end;
  | Ttree.Eaccess_local id -> begin
    (*let actual_block =  if (id = last_id) then 
      try
        Stack.pop var_to_reg
      with Stack.Empty -> raise_error("Empty here access local")
    else Hashtbl.create 1 in*)

    (* Find the register associated to the variable *)
    let register = associate_register id in
    (*if(id = last_id) then Stack.push actual_block var_to_reg;*)
    generate (Rtltree.Embinop(Ops.Mmov, register, destr, destl));
  end;
  | Ttree.Einit_local (decl_list, exp) -> begin
    (*Get the hashtable of the block*)
    let block_var_to_reg = try
      Stack.top var_to_reg;
    with Stack.Empty -> raise_error ("Taking an empty stack's top") in

    let initializer_register = ref Register.M.empty in

    let init_var label (t,id) = 
      (* Find the register associated to the new variable *)
      let register = associate_register id in
      initializer_register:= Register.M.add register id !initializer_register;
      let instruction_assign = Rtltree.Embinop(Ops.Mmov, destr, register, label) in
      let label_assign = generate instruction_assign in
      (*let label_expression = expr exp.expr_node destr label_assign id in
      label_expression*)
      label_assign
    in
      
    let label_first_init = List.fold_left init_var destl decl_list in
    (* Convert the expression *)
    let label_expression = expr exp.expr_node destr label_first_init in

    (* Remove the mapping from the hashtable.
    Higher expressions (before the declaration of the new variable)
    will use variables declared in higher scopes. *)
    let remove reg id =
      Hashtbl.remove block_var_to_reg id;
    in
    Register.M.iter remove !initializer_register;
    label_expression;
  end;
  | Ttree.Ecall (id, expr_list) -> begin
    (* Find the function *)
    let id_param = try 
      Hashtbl.find functions id;
    with Not_found -> raise_error "No such function" in
    let call_label = Label.fresh() in
    let reg_list = ref [] in
    (* Treat the arguments of the function *)
    let treat_args id (exp : Ttree.expr) destl =
      let register = Register.fresh() in
      let instr_label = expr exp.expr_node register destl (*""*) in
      reg_list := register::!reg_list;
      instr_label
    in
    let label_first_param = List.fold_right2 treat_args id_param expr_list call_label in
    let call_instr = Rtltree.Ecall(destr, id, !reg_list, destl) in
    (* Associate the label to the instruction *)
    graph := Label.M.add call_label call_instr !graph;
    label_first_param
  end;
  | Ttree.Eaccess_field (e,f)-> begin
    let register_var = Register.fresh() in
    let label_field = generate (Rtltree.Eload(register_var, f.field_pos * word_size, destr, destl)) in
    let label_expression = if(e.expr_typ = Ttree.Ttypenull) then generate(Rtltree.Econst(zero_i32, register_var, label_field))
    else expr e.expr_node register_var label_field (*""*) in
    label_expression;
  end;
  | Ttree.Eassign_field (expl,f,e)-> begin
    let register_left = Register.fresh() in
    let label_field = generate (Rtltree.Estore(destr, register_left, f.field_pos * word_size, destl)) in
    let label_left = expr expl.expr_node register_left label_field (*""*) in
    let label_expression = expr e.expr_node destr label_left (*""*) in
    label_expression;
  end;
  | Ttree.Esizeof str -> begin
    generate (Rtltree.Econst(Int32.of_int (str.str_size*word_size), destr, destl))
  end;


and treat_unop e destr destl unop = match unop with
  | Ptree.Uminus -> begin
    (*  put 0 in a register
        put our value in a register
        do the difference between the two registers*)
    let reg_e = Register.fresh() in
    let instruction_binop = Embinop(Ops.Msub, reg_e, destr, destl) in
    let label_binop = generate instruction_binop in
    let label_put_e = expr e.expr_node reg_e label_binop (*""*) in
    let label_put_zero = expr (Ttree.Econst zero_i32) destr label_put_e (*""*) in
    label_put_zero
  end;
  | Ptree.Unot -> begin
    (*  put our value in a register
        see if zero*)
    let instruction_setei = Emunop(Ops.Msetei zero_i32, destr, destl) in
    let label_setei = generate instruction_setei in
    let label_put_e = expr e.expr_node destr label_setei (*""*) in
    label_put_e
  end;

and treat_binop e1 e2 destr destl binop (*last_id*) = 
  (*Place each expression in a register
  If we are comparing, use Msub to compare with zero and then use the appropriate operation
  Else, use the appropriate operation (add, sub, div, mul)*)
  let reg_e2 = Register.fresh() in
  let label_next = ref destl in
  let operation = match binop with
  | Ptree.Beq -> 
    boolean_op Ops.Msete destr destl label_next;  Ops.Msub;
  | Ptree.Bneq-> 
    boolean_op Ops.Msetne destr destl label_next; Ops.Msub;
  | Ptree.Blt ->  
    boolean_op Ops.Msetl destr destl label_next;  Ops.Msub;
  | Ptree.Ble ->
    boolean_op Ops.Msetle destr destl label_next; Ops.Msub;
  | Ptree.Bgt ->
    boolean_op Ops.Msetg destr destl label_next;  Ops.Msub;
  | Ptree.Bge ->
    boolean_op Ops.Msetge destr destl label_next; Ops.Msub;
  | Ptree.Bsub -> Ops.Msub
  | Ptree.Bmul -> Ops.Mmul
  | Ptree.Bdiv -> begin
    Ops.Mdiv
  end;
  | _ -> raise_error "Should not come to this case (Badd/Band/Bor)" in

  let instruction_binop =  Embinop(operation, reg_e2, destr, !label_next) in
  let label_binop = generate instruction_binop in
  let label_put_e2 = if(e2.expr_typ = Ttree.Ttypenull) then generate (Rtltree.Econst(zero_i32, reg_e2, label_binop))
  else expr e2.expr_node reg_e2 label_binop (*last_id*) in
  let label_put_e1 = expr e1.expr_node destr label_put_e2 (*last_id*) in
  label_put_e1

and treat_immediate e1 e2 destr destl binop (*last_id*) =
  let immediate_op c = match binop with
  | Ops.Msete -> Ops.Msetei c
  | Ops.Msetne-> Ops.Msetnei c
  | Ops.Madd  -> Ops.Maddi c
  | _ -> raise_error "Treat_immediate : case should not exist"
  in
  match e1.expr_node, e2.expr_node with
  | (_, Ttree.Econst c) -> begin
    let instruction_addi =  Emunop(immediate_op c, destr, destl) in
    let label_addi = generate instruction_addi in
    let label_put_e1 = expr e1.expr_node destr label_addi (*last_id*) in
    label_put_e1
  end
  | (Ttree.Econst c, _) -> begin
    let instruction_addi =  Emunop(immediate_op c, destr, destl) in
    let label_addi = generate instruction_addi in
    let label_put_e2 = expr e2.expr_node destr label_addi (*last_id*) in
    label_put_e2
  end
  | _ -> begin
    let reg_e2 = Register.fresh() in
    let instruction_binop =  Embinop(binop, reg_e2, destr, destl) in
    let label_binop = generate instruction_binop in
    let label_put_e2 = expr e2.expr_node reg_e2 label_binop (*last_id*) in
    let label_put_e1 = expr e1.expr_node destr label_put_e2 (*last_id*) in
    label_put_e1
  end


and boolean_op op destr destl label_next =
  let reg_zero = Register.fresh() in
  let instruction_sete = Embinop(op, reg_zero, destr, destl) in
  label_next := generate instruction_sete;
  label_next := expr (Ttree.Econst zero_i32) reg_zero !label_next (*""*)

and condition_boolean_op binop (e1: Ttree.expr) (e2: Ttree.expr) truel falsel =
  let reg_e1 = Register.fresh() and reg_e2 = Register.fresh() in
  let r1 = ref reg_e1 and r2 = ref reg_e2 in
  let op = match binop with
  | Ptree.Blt -> Ops.Mjl;
  | Ptree.Ble -> Ops.Mjle
  | Ptree.Bgt -> r1 := reg_e2; r2 := reg_e1; Ops.Mjl
  | Ptree.Bge -> r1 := reg_e2; r2 := reg_e1; Ops.Mjle
  | _ -> raise_error "ha" in
  (*let instruction_branch = Embbranch(op, !r2, !r1, truel, falsel) in
  let label_branch = generate instruction_branch in
  let label_put_e2 = expr e2.expr_node reg_e2 label_branch (*""*) in
  let label_put_e1 = expr e1.expr_node reg_e1 label_put_e2 (*""*) in
  label_put_e1*)
  match e1.expr_node, e2.expr_node, binop with
  | (Ttree.Econst c1, Ttree.Econst c2, _) -> begin
    let id, im_op = match binop with
      | Ptree.Bgt -> 1, Ops.Mjgi c2;
      | Ptree.Ble -> 1, Ops.Mjlei c2;
      | Ptree.Blt -> 2, Ops.Mjgi c1;
      | Ptree.Bge -> 2, Ops.Mjlei c1;
      | _ -> raise_error "ha"
    in
    if(id = 1) then begin
      let instruction_branch = Emubranch(im_op, reg_e1, truel, falsel) in
      let label_branch = generate instruction_branch in
      let label_put_e1 = expr e1.expr_node reg_e1 label_branch (*""*) in
      label_put_e1
    end
    else begin
      let instruction_branch = Emubranch(im_op, reg_e2, truel, falsel) in
      let label_branch = generate instruction_branch in
      let label_put_e2 = expr e2.expr_node reg_e2 label_branch (*""*) in
      label_put_e2
    end
  end
  | (_, Ttree.Econst c, Ptree.Ble) -> begin
    let instruction_branch =  Emubranch(Ops.Mjlei c, reg_e1, truel, falsel) in
    let label_branch = generate instruction_branch in
    let label_put_e1 = expr e1.expr_node reg_e1 label_branch in
    label_put_e1
  end
  | (Ttree.Econst c, _, Ptree.Blt) -> begin
    let instruction_branch =  Emubranch(Ops.Mjgi c, reg_e2, truel, falsel) in
    let label_branch = generate instruction_branch in
    let label_put_e2 = expr e2.expr_node reg_e2 label_branch in
    label_put_e2
  end
  | _ -> begin
    let instruction_branch = Embbranch(op, !r2, !r1, truel, falsel) in
    let label_branch = generate instruction_branch in
    let label_put_e2 = expr e2.expr_node reg_e2 label_branch in
    let label_put_e1 = expr e1.expr_node reg_e1 label_put_e2 in
    label_put_e1
  end

and condition e truel falsel = match e with
  |Ttree.Ebinop (binop, e1, e2) -> (match binop with
    | Blt | Ble | Bgt | Bge ->
      (*This is treated as x <= y or x < y*)
      condition_boolean_op binop e1 e2 truel falsel;
    | Band ->
      (*Put as truel for the first expression the label of the second expression*)
      let label_convert_e2 = condition e2.expr_node truel falsel in
      let label_convert_e1 = condition e1.expr_node label_convert_e2 falsel in
      label_convert_e1
    | Bor ->
      (*Put as falsel for the first expression the label of the second expression*)
      let label_convert_e2 = condition e2.expr_node truel falsel in
      let label_convert_e1 = condition e1.expr_node  truel label_convert_e2 in
      label_convert_e1
    | _ -> begin (*add, sub, mul div*)
      let register = Register.fresh() in
      let instruction_branch = Rtltree.Emubranch(Ops.Mjz, register, falsel, truel) in
      let label_branch = generate instruction_branch in
      expr e register label_branch (*""*)
    end;)
  | _ -> begin
    let register = Register.fresh() in
    let instruction_branch = Rtltree.Emubranch(Ops.Mjz, register, falsel, truel) in
    let label_branch = generate instruction_branch in
    expr e register label_branch (*""*);
  end;;

let rec stmt s destl retr exitl local_reg = match s with
  | Ttree.Sreturn e -> let converted_e = expr e.expr_node retr exitl (*""*) in converted_e;
  | Ttree.Sblock b  -> begin
      let block_var_to_reg = Hashtbl.create 16 in
      Stack.push block_var_to_reg var_to_reg;
      let decl_list, stmt_list = b in
      (*print_string "Block \n";
      List.iter (fun (t,x) -> print_string (x ^ "\n")) decl_list ;*)
      (* Add the local vars declared here to the scope *)
      List.iter (function t, s -> let register = Register.fresh()
        in local_reg := Register.S.add register !local_reg;
        Hashtbl.add block_var_to_reg s register)
        decl_list;
      let result = List.fold_right (fun s label -> stmt s label retr exitl (ref Register.S.empty)) stmt_list destl in
      let _ = (try 
        Stack.pop var_to_reg
      with Stack.Empty -> raise_error "Trying to pop from empty stack in treating block statement") in
      result;
    end
  | Ttree.Sexpr e -> let converted_e = expr e.expr_node retr destl (*""*) in converted_e;
  | Ttree.Sif (e, s1, s2) -> begin
      let truel = stmt s1 destl retr exitl local_reg
      and falsel = stmt s2 destl retr exitl local_reg in
      let label_branching = condition e.expr_node truel falsel in
      label_branching
    end; 
  | Ttree.Swhile (e, s) -> begin
    let go_to_label = Label.fresh() in
    let loop_label = stmt s go_to_label retr exitl local_reg in
    let label_expression = condition e.expr_node loop_label destl in
    graph := Label.M.add go_to_label (Egoto label_expression) !graph;
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
  let local_var_to_reg = Hashtbl.create 16 in
  let fun_formals = List.map  (function x -> let register = Register.fresh()
    in Hashtbl.add local_var_to_reg x register;
    register) (* TODO : Formals are a step higher than the declarations of the body?
                        Should maybe see this *)
    id_params
  in
  Stack.push local_var_to_reg var_to_reg;
  let entryl = stmt (Ttree.Sblock fun_definition.fun_body) exitl retr exitl local_reg in
  let _  = (try 
    Stack.pop var_to_reg
  with Stack.Empty -> raise_error "Trying to pop from an empty stack. In deffun") in
  {
    fun_name = name;
    fun_formals = fun_formals;
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