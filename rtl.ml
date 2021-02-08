
open Rtltree

let zero_i32 = Int32.of_int 0;

exception Error of string

let raise_error  error =
  raise (Error error);;

let graph = ref Label.M.empty


let generate i =
  let l = Label.fresh () in
  graph := Label.M.add l i !graph;
  l




let rec expr e destr destl = match e with
  | Ttree.Econst cst -> Rtltree.Econst(cst, destr, destl)
  | Ttree.Eunop (unop, e) -> treat_unop e destr destl unop
  | _ -> raise_error "Not yet implemented";


and treat_unop e destr destl = function
  | Ptree.Uminus -> begin
    let reg_e = Register.fresh() in
    let instruction_binop = Embinop(Ops.Msub, reg_e, destr, destl) in
    let label_binop = generate instruction_binop in
    let instuction_e = expr e.expr_node reg_e label_binop in
    let label_put_e = generate instuction_e in
    let instruction_put_zero = expr (Ttree.Econst zero_i32) destr label_put_e in
    instruction_put_zero
  end;
  | Ptree.Unot -> raise_error "Unot not yet implemented";;



let rec stmt s destl retr exitl = match s with
  | Ttree.Sreturn e -> let converted_e = expr e.expr_node retr exitl in generate converted_e;
  | Ttree.Sblock b  -> begin 
      let decl_list, stmt_list = b in 
      let rec treat_block l = function
        | hd_s::tl -> let label = stmt hd_s l retr exitl in treat_block label tl; 
        | [] -> l;
      in treat_block destl (List.rev stmt_list);
    end
  | _ -> raise_error "Not yet implemented"


let deffun (fun_definition:Ttree.decl_fun) = 
  graph := Label.M.empty;
  let retr = Register.fresh() 
  and exitl = Label.fresh() in
  let entryl = stmt (Ttree.Sblock fun_definition.fun_body) exitl retr exitl
  in
  {
    fun_name = fun_definition.fun_name;
    fun_formals = [];
    fun_result = retr;
    fun_locals = Register.S.empty;
    fun_entry  = entryl;
    fun_exit   = exitl;
    fun_body   = !graph;
  };;


let program (p:Ttree.file) =
  let rec aux = function
    | hd::tl -> let converted_func = deffun hd in converted_func::aux tl;
    | [] -> []
  in {funs = aux p.funs};;