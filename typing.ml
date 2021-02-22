
open Ttree
open Int32

(* TODO : change types in convert stmt *)

(* utiliser cette exception pour signaler une erreur de typage *)
exception Error of string


let structures = (Hashtbl.create 16 : (string, structure) Hashtbl.t);;
let functions = (Hashtbl.create 16 : (string, (Ttree.typ * (Ttree.typ*string) list)) Hashtbl.t);;

(* Add two predefined functions : int putchar(int c) and void *sbrk(int n) *)
Hashtbl.add functions "putchar" (Tint, (Tint, "c")::[]);;
Hashtbl.add functions "sbrk" (Tvoidstar, (Tint, "n")::[]);;

let string_of_expr_node = function
  | Econst cst -> "cst"
  | Eaccess_local id -> "access_local"
  | Eaccess_field (e,f) -> "access_field"
  | Eassign_local (id,e) -> "assign_local"
  | Eassign_field (e, f, e1) -> "assign_field"
  | _ -> "other";;

let string_of_type = function
  | Tint       -> "int"
  | Tstructp x -> "struct " ^ x.str_name ^ " *"
  | Tvoidstar  -> "void*"
  | Ttypenull  -> "typenull"

let type_of_string x = match x with
  | "int"       -> Tint
  | "void*"  -> Tvoidstar
  | "typenull"  -> Ttypenull
  | _ -> try
    Tstructp (Hashtbl.find structures x);
  with Not_found -> raise (Error "No types found");;

let raise_error (loc:Ptree.loc) error =
  let line,column = loc in
  raise (
    Error (" at line: " ^ string_of_int(line.pos_lnum)
    ^ "      " ^ error)
  );;

let raise_undeclared_variable (x:Ptree.ident) =
  let error = "undeclared variable " ^ x.id in
  raise_error x.id_loc error;;

let raise_undeclared_function (x:Ptree.ident) =
  let error = "undeclared function " ^ x.id in
  raise_error x.id_loc error;;

let raise_undeclared_structure (x:Ptree.ident) = 
  let error = "undeclared structure " ^ x.id in
  raise_error x.id_loc error;;

let raise_undeclared_field (x:Ptree.ident) = 
  let error = "undeclared field " ^ x.id in
  raise_error x.id_loc error;;


let raise_unconsistant loc type_one type_two =
  let error = "type " ^ string_of_type type_one ^ " and type " ^ string_of_type type_two
  ^ " are unconsistant" in
  raise_error loc error;;

let raise_other loc err typ =
  let error = err ^ string_of_type typ in
  raise_error loc error;;


let rec remove_variables variable_list = function
  | hd::tl ->  Hashtbl.remove variable_list hd; remove_variables variable_list tl;
  | [] -> ();;

let compare_typ type_one type_two = match (type_one, type_two) with
  | Tint, Tint | Tvoidstar, Tvoidstar | Ttypenull, Ttypenull -> true;
  | Tint, Ttypenull | Ttypenull, Tint -> true
  | Ttypenull, Tstructp str | Tstructp str, Ttypenull -> true
  | Tvoidstar, Tstructp str | Tstructp str, Tvoidstar -> true
  | Tstructp str1, Tstructp str2 -> string_of_type type_one = string_of_type type_two
  | _ -> false;;

let convert_type =  function
  | Ptree.Tint -> Tint;
  | Ptree.Tstructp ident -> let structtyp = try 
    Hashtbl.find structures ("struct " ^ ident.id ^ " *")
  with Not_found -> raise_undeclared_structure ident in Tstructp structtyp;;
;;

(* Creates structures and saves them in a hashtable *)
let struct_aux ((identifier, list_of_members):Ptree.decl_struct) =
  let str_identifier = "struct " ^ identifier.id ^ " *" in
  if(Hashtbl.mem structures str_identifier) then
    raise (Error (str_identifier ^ " previously declared. Can't declare it twice."))
  else
    let new_struc = {str_name = identifier.id; str_fields = Hashtbl.create(List.length list_of_members); str_size = List.length list_of_members} in 
    Hashtbl.add structures str_identifier new_struc;
    let rec fill (declaration_var:Ptree.decl_var list) position = match declaration_var with
    | hd::tl -> 
      let hd_typ, hd_ident = hd in
      if(Hashtbl.mem new_struc.str_fields hd_ident.id) then
        raise (Error (str_identifier ^ "already possesses " ^ hd_ident.id ^ ". Can't declare field twice in a single structre."))
      else
      (
        let new_field = {field_name = hd_ident.id; field_typ = convert_type hd_typ; field_pos = position} in
        Hashtbl.add new_struc.str_fields hd_ident.id new_field; fill tl (position+1);)
    | [] -> (); in
    fill list_of_members 0;
  ;;
;;



let rec convert_decl_var_list variable_list local_declarations (decl_list:Ptree.decl_var list) = 
  match decl_list with
  | hd::tl -> (begin 
      let hd_typ, hd_ident = hd in
      if(List.mem hd_ident.id local_declarations) then 
        raise (Error ("Variable " ^ hd_ident.id ^ " already declared."))
      else(
        let local_declarations = hd_ident.id::local_declarations in
        let converted_type = convert_type hd_typ in
        Hashtbl.add variable_list hd_ident.id (converted_type, hd_ident.id);
        let _, rest = convert_decl_var_list variable_list local_declarations tl in
        local_declarations, (converted_type, hd_ident.id)::rest;
      )
    end)
  | [] -> [],[];;
;;

let rec get_var_name = function
  | Ptree.Eright value -> (match value with
    | Ptree.Lident e -> e.id
    | Ptree.Larrow (e,id) -> id.id;)
  | _ -> raise (Error "not a variable");;

let rec convert_expr_node variable_list = function
  | Ptree.Econst cst -> if(cst = zero) then Ttypenull, Ttree.Econst cst else Tint, Ttree.Econst cst;
  (* Treat the case of calling a variable as a right member*)
  | Ptree.Eright rval -> (match rval with
    | Ptree.Lident lid-> begin 
        let saved_typ , saved_ident = try
          Hashtbl.find variable_list lid.id
        with Not_found -> raise (Error "here")
          (*raise_undeclared_variable lid*) in
        
        saved_typ, Ttree.Eaccess_local lid.id;
      end
    | Ptree.Larrow (lar,field) -> begin
        let lar_typ, lar_node = convert_expr_node variable_list lar.expr_node in
        (* Take care of the case 0->field / typenull->field *)
        if(lar_typ = Ttree.Ttypenull) then 
        lar_typ, Ttree.Eaccess_field({expr_node=lar_node; expr_typ=lar_typ}, {field_name = field.id; field_typ = lar_typ; field_pos = 0})
      else
        let variable_name = get_var_name lar.expr_node in
        (*raise (Error ("var name " ^ variable_name ^ " field " ^ field.id ^ " : type of node lar is " ^ (string_of_expr_node lar_node)));*)
        
        let var_typ, var_name = (match lar_node with
          | Eaccess_field (e,f) -> lar_typ, variable_name
          | Eaccess_local id -> begin 
              try
                Hashtbl.find variable_list variable_name
              with Not_found ->  raise_undeclared_variable {id=variable_name; id_loc=lar.expr_loc}
            end
          | _ -> raise (Error "Some other type of access that is not yet implemented. Should not exist.")
        ) in
        
        let str_typ = string_of_type var_typ in

        let str_fields = try 
          (Hashtbl.find structures str_typ).str_fields
        with Not_found -> raise_undeclared_structure {id=str_typ; id_loc=lar.expr_loc} in
        
        let called_field = try
          Hashtbl.find str_fields field.id 
        with Not_found -> raise_undeclared_field field in

        called_field.field_typ, Ttree.Eaccess_field({expr_node=lar_node; expr_typ=lar_typ}, called_field)
      end)

  (* Treat the case of assigning to the variable *)
  | Ptree.Eassign (lval,e) -> (match lval with
    | Ptree.Lident lid-> begin 
      let saved_typ , saved_ident = try
        Hashtbl.find variable_list lid.id
      with Not_found -> raise_undeclared_variable lid in

      let e_typ, e_node = convert_expr_node variable_list e.expr_node in
      if(compare_typ saved_typ e_typ) then( (*Make sure the types are consistant*)
        (*print_string ("Typing : " ^ lid.id ^ " was : " ^ (string_of_type saved_typ) ^ " \n");*)
        if(e_typ = Ttypenull) then
          begin
            Hashtbl.replace variable_list lid.id (e_typ, lid.id);
            (*print_string ("Typing : " ^ lid.id ^ " is : " ^ (string_of_type e_typ) ^ " \n");*)
          end;
        saved_typ, Ttree.Eassign_local (lid.id,{expr_node = e_node; expr_typ = e_typ})
      )
      else raise_unconsistant lid.id_loc saved_typ e_typ;
    end
    | Ptree.Larrow (lar,field) -> begin
      let lar_typ, lar_node = convert_expr_node variable_list lar.expr_node in
      let variable_name = get_var_name lar.expr_node in

      let var_typ, var_name = (match lar_node with
          | Eaccess_field (e,f) -> lar_typ, variable_name
          | Eaccess_local id -> begin 
              try
                Hashtbl.find variable_list variable_name
              with Not_found ->  raise_undeclared_variable {id=variable_name; id_loc=lar.expr_loc}
            end
          | _ -> raise (Error "Some other type of access that is not yet implemented. Should not exist.")
        ) in
      
      let str_typ = string_of_type var_typ in

      let str_fields = try 
        (Hashtbl.find structures str_typ).str_fields
      with Not_found -> raise_undeclared_structure {id=str_typ; id_loc=lar.expr_loc} in
      
      let called_field = try
        Hashtbl.find str_fields field.id 
      with Not_found -> raise_undeclared_field field in

      let e_typ, e_node = convert_expr_node variable_list e.expr_node in
      if(compare_typ called_field.field_typ e_typ) then (*Make sure the types are consistant*)
        called_field.field_typ, Ttree.Eassign_field({expr_node=lar_node; expr_typ=lar_typ}, called_field, {expr_node = e_node; expr_typ = e_typ})
      else raise_unconsistant lar.expr_loc lar_typ e_typ;
    end)

  | Ptree.Eunop (nop, e) -> (match nop with
    (* nop is ! , then if e is well typed, !e is of type int*)
    | Unot -> begin
        let e_typ, e_node = convert_expr_node variable_list e.expr_node in
        Tint, Ttree.Eunop (nop,{expr_node= e_node; expr_typ= Tint});
      end
    (* nop is - , then if e is of type int, the expression is well typed *)
    | Uminus -> begin
        let e_typ, e_node = convert_expr_node variable_list e.expr_node in
        if(compare_typ e_typ Tint) then
          Tint, Ttree.Eunop (nop,{expr_node= e_node; expr_typ= Tint})
        else raise_other  e.expr_loc "Can't apply - operator to type " e_typ
      end
  )
  
  (* Treat operations between two expressions *)
  | Ptree.Ebinop (binop, e1, e2) -> treat_binop variable_list binop e1 e2;

  (* Treat function calls *)
  | Ptree.Ecall (f, e_list) -> treat_call variable_list f e_list;
  
  | Ptree.Esizeof str -> (begin
      let structure_identifier = "struct " ^ str.id ^ " *" in
      let called_structure = try
        Hashtbl.find structures structure_identifier
      with Not_found -> raise_undeclared_structure str in
      Tint, Ttree.Esizeof called_structure;
    end)
  
and treat_binop variable_list binop e1 e2 = match binop with
  | Beq | Bneq | Blt | Ble | Bgt | Bge -> begin
      let e1_typ, e1_node = convert_expr_node variable_list e1.expr_node and e2_typ, e2_node = convert_expr_node variable_list e2.expr_node in
      if (compare_typ e1_typ e2_typ) then
        Tint, Ttree.Ebinop (binop, {expr_node= e1_node; expr_typ= e1_typ}, {expr_node= e2_node; expr_typ= e2_typ})
      else raise_unconsistant e1.expr_loc e1_typ e2_typ
    end
  
  | Badd | Bsub | Bmul | Bdiv -> begin
    let e1_typ, e1_node = convert_expr_node variable_list e1.expr_node and e2_typ, e2_node = convert_expr_node variable_list e2.expr_node in
    if (compare_typ e1_typ Tint && compare_typ e2_typ Tint) then
      Tint, Ttree.Ebinop (binop, {expr_node= e1_node; expr_typ= e1_typ}, {expr_node= e2_node; expr_typ= e2_typ})
    else raise_unconsistant e1.expr_loc e1_typ e2_typ
  end

  | Band | Bor -> begin
      let e1_typ, e1_node = convert_expr_node variable_list e1.expr_node and e2_typ, e2_node = convert_expr_node variable_list e2.expr_node in
      Tint, Ttree.Ebinop (binop, {expr_node= e1_node; expr_typ= e1_typ}, {expr_node= e2_node; expr_typ= e2_typ})
    end

and treat_call variable_list f e_list =
  let return_typ, args   = try 
    Hashtbl.find functions f.id
  with Not_found -> raise_undeclared_function f in

  let rec compare_args args (e_list:Ptree.expr list) = 
    match (args, e_list) with
    | [], [] -> [];
    | [], _ -> raise (Error "too many arguments");
    | _, [] -> raise (Error "not enough arguments");
    | hd::tl, e_hd::e_tl -> begin
      let e_typ, e_node = convert_expr_node variable_list e_hd.expr_node
      and arg_typ, arg_id = hd in
      if(compare_typ arg_typ e_typ) then
        {expr_node=e_node; expr_typ=e_typ}::(compare_args tl e_tl)
      else
        raise_unconsistant e_hd.expr_loc e_typ arg_typ;
    end
  in (return_typ, Ttree.Ecall(f.id, compare_args args e_list));;




let rec convert_stmt_list variable_list return_typ (stmt_list:Ptree.stmt list) = match stmt_list with
  | hd::tl -> let node = convert_stmt variable_list return_typ hd in node::(convert_stmt_list variable_list return_typ tl)
  | [] -> [];
  
and convert_stmt variable_list return_typ (s:Ptree.stmt) = 
  convert_stmt_node variable_list return_typ s.stmt_node

  
and convert_stmt_node variable_list return_typ = function 
(* return value : the return type and the statement *)
  | Ptree.Sskip -> Ttree.Sskip
  | Ptree.Sexpr e -> begin
      let e_typ, e_node = convert_expr_node variable_list e.expr_node in
      Ttree.Sexpr {expr_node = e_node; expr_typ = e_typ};
    end
  | Ptree.Sif (e, s1, s2) -> begin
      let e_typ, e_node = convert_expr_node variable_list e.expr_node in
      let converted_s1 = convert_stmt variable_list return_typ s1 in
      let converted_s2 = convert_stmt variable_list return_typ s2 in
      Ttree.Sif({expr_node=e_node; expr_typ=e_typ}, converted_s1, converted_s2)
    end
  | Ptree.Swhile (e, s) -> begin
      let e_typ, e_node = convert_expr_node variable_list e.expr_node in
      let converted_s = convert_stmt variable_list return_typ s in
      Ttree.Swhile({expr_node=e_node; expr_typ=e_typ}, converted_s);
    end
  | Ptree.Sblock b -> begin
      let converted_block = convert_block variable_list return_typ b in
      Ttree.Sblock converted_block;
    end

  | Ptree.Sreturn e -> begin
    let e_typ, e_node = convert_expr_node variable_list e.expr_node in
    if(compare_typ e_typ return_typ) then
      Ttree.Sreturn {expr_node = e_node; expr_typ = e_typ}
    else  raise_unconsistant e.expr_loc e_typ return_typ;
  end



and convert_block variable_list return_typ (decl_list,stmt_list) = 
  let local_declarations = [] in
  let local_declarations, converted_var = convert_decl_var_list variable_list local_declarations decl_list
  and converted_stmt = convert_stmt_list variable_list return_typ stmt_list in
  (*Hashtbl.iter (fun key (t,n) -> print_string ("variable " ^ key ^" of type " ^ (string_of_type t) ^ "\n")) variable_list;*)
  remove_variables variable_list local_declarations;
  (converted_var,converted_stmt);;



let treat_body variable_list fun_body converted_typ name args =
  {
    fun_typ    = converted_typ;
    fun_name   = name;
    fun_formals= args;
    fun_body   = convert_block variable_list converted_typ fun_body
  } ;;

let fun_aux  (fn:Ptree.decl_fun) =

  (* A table to store the variables declared inside a block *)
  let variable_list = (Hashtbl.create 10 : (string, Ttree.decl_var) Hashtbl.t) in
  let local_declarations = [] in

  let converted_typ = convert_type fn.fun_typ and name = fn.fun_name.id
  and _, args = convert_decl_var_list variable_list local_declarations fn.fun_formals in

  if(Hashtbl.mem functions name) then
    raise (Error ("Function " ^ name ^ " already declared"))
  else
    Hashtbl.add functions name (converted_typ,args);
  (*raise (Error ("adding function " ^ name));*)
  (* The definition of the functions start from bottom to top. This is weird. *)

  treat_body variable_list fn.fun_body converted_typ name args;;





let program p =

  (* The list of declarations go from bottom to top,
  since the program is reading from top to bottom and appending the declarations
  So, we first need to inverse the list and then treat the elements *)

  (* Here, we treat the elements of the list depending on the type of declaration they are *)
  let rec aux = function
    | (Ptree.Dstruct st)::tl -> struct_aux st; aux tl
    | (Ptree.Dfun fn)::tl -> let def_fun = fun_aux fn in def_fun :: aux tl
    | [] -> ( 
          let fun_typ, fun_args = try
            Hashtbl.find functions "main"
          with Not_found -> raise (Error "function main not declared in the file") in
          if(fun_typ <> Tint) then
            raise (Error "function main with wrong return type")
          else
            if(fun_args <> []) then 
              raise (Error "function main with wrong arguments")
            else
              [];
        )
  in
  {funs = aux p};;




