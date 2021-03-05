open Format

let visited = Hashtbl.create 17;;

exception Error of string

let raise_error error = raise (Error error);;

type instr = 
  | Code of X86_64.text
  | Label of Label.t
let code = ref []
let emit l i = 
  code := Code i :: Label l :: !code
let emit_wl i = 
  code := Code i :: !code
let labels = Hashtbl.create 17
let need_label l = Hashtbl.add labels l ()
let function_label = Hashtbl.create 17
let map_label_to_function (l:Label.t) (id:string) = Hashtbl.add function_label l id


let operand = function
  | Ltltree.Reg reg -> X86_64.reg (X86_64.register64 reg)
  | Ltltree.Spilled n -> X86_64.ind ~ofs:n X86_64.rbp;;

let find_label l= 
  (*Label.print std_formatter l;*)
  let fun_name = try
    Hashtbl.find function_label l
  with Not_found -> (l:>string) in
  X86_64.label fun_name;;


let rec lin g l =
  if not (Hashtbl.mem visited l) then begin
    Hashtbl.add visited l ();
    produce_code g l (Label.M.find l g)
  end else begin
    (*print_string "already visited label ";
    Label.print std_formatter l;
    print_string "\n";*)
    need_label l;
    emit_wl (X86_64.jmp (l :> string))
  end

  and produce_code g l = function
  | Ltltree.Econst (n, r, label) ->
    emit l (X86_64.movq (X86_64.imm32 n) (operand r));
    lin g label
  | Ltltree.Emunop(munop, r, label) -> 
    begin
      match munop with
      | Ops.Maddi n   -> begin emit l (X86_64.addq  (X86_64.imm32 n) (operand r)); lin g label; end;
      | Ops.Msetei n  -> begin
        emit l (X86_64.cmpq  (X86_64.imm32 n) (operand r));
        emit_wl (X86_64.sete (X86_64.reg X86_64.r15b));
        emit_wl (X86_64.movzbq (X86_64.reg X86_64.r15b) (X86_64.r15));
        emit_wl (X86_64.movq (X86_64.reg X86_64.r15) (operand r));
        lin g label;
      end;
      | Ops.Msetnei n -> begin
        emit l (X86_64.cmpq  (X86_64.imm32 n) (operand r));
        emit_wl (X86_64.setne (X86_64.reg X86_64.r15b));
        emit_wl (X86_64.movzbq (X86_64.reg X86_64.r15b) (X86_64.r15));
        emit_wl (X86_64.movq (X86_64.reg X86_64.r15) (operand r));
        lin g label;
      end;
      
    end
  | Ltltree.Embinop(binop, r1, r2, label) ->
    begin
      match binop with
      | Ops.Mmov -> begin emit l (X86_64.movq (operand r1) (operand r2)); lin g label; end;
      | Ops.Madd -> begin emit l (X86_64.addq  (operand r1) (operand r2)); lin g label;end;
      | Ops.Msub -> begin emit l (X86_64.subq  (operand r1) (operand r2)); lin g label;end;
      | Ops.Mmul -> begin emit l (X86_64.imulq  (operand r1) (operand r2)); lin g label;end;
      | Ops.Mdiv -> begin emit l (X86_64.cqto); emit_wl (X86_64.idivq (operand r1)); lin g label; end;
      | _ -> treat_set binop r1 r2 l; lin g label;
    end
  | Ltltree.Emubranch(mubranch, r, label2, label3) -> treat_mubranch mubranch r label2 label3 g l
  | Ltltree.Embbranch(mbbranch, r1, r2, label2, label3) -> treat_mbbranch mbbranch r1 r2 label2 label3 g l
  | Ltltree.Epush (r, label) ->
    emit l (X86_64.pushq (operand r));
    lin g label;
  | Ltltree.Epop (r, label) -> 
    emit l (X86_64.popq (X86_64.register64 r));
    lin g label;
  | Ltltree.Ecall(id, label) -> 
    emit l (X86_64.call id);
    lin g label;
  | Ltltree.Egoto label -> begin
    if (Hashtbl.mem visited label) then
      lin g label
    else
      code := Label l :: !code;
      lin g label;
  end

  | Ltltree.Eload (r1, n, r2, label) -> begin
    emit l (X86_64.movq (X86_64.ind ~ofs:n (X86_64.register64 r1)) (operand (Ltltree.Reg r2)));
    lin g label;
  end

  | Ltltree.Estore (r1, r2, n, label) -> begin
    emit l (X86_64.movq (operand (Ltltree.Reg r1)) (X86_64.ind ~ofs:n (X86_64.register64 r2)));
    lin g label;
  end
  
  | Ltltree.Ereturn -> begin
    emit l (X86_64.ret);
  end

  and treat_set binop r1 r2 l = 
    let inst = function
    | Ops.Msete -> X86_64.sete
    | Ops.Msetne -> X86_64.setne
    | Ops.Msetl -> X86_64.setl
    | Ops.Msetle -> X86_64.setle
    | Ops.Msetg -> X86_64.setg
    | Ops.Msetge -> X86_64.setle
    | _ -> raise_error "should not be here !"
    in
    let instruction = inst binop in
    emit l (X86_64.cmpq  (operand r1) (operand r2));
    emit_wl (instruction (X86_64.reg X86_64.r15b));
    emit_wl (X86_64.movzbq (X86_64.reg X86_64.r15b) (X86_64.r15));
    emit_wl (X86_64.movq (X86_64.reg X86_64.r15) (operand r2));


  and treat_mubranch mubranch r label2 label3 g l=
    let first_instruction = function
      | Ops.Mjz | Ops.Mjnz -> emit l (X86_64.testq (operand r) (operand r));
      | Ops.Mjlei n | Ops.Mjgi n-> emit l (X86_64.cmpq (X86_64.imm32 n) (operand r));
    in

    let opposite = function
    | Ops.Mjz     -> Ops.Mjnz
    | Ops.Mjnz    -> Ops.Mjz
    | Ops.Mjlei n -> Ops.Mjgi n
    | Ops.Mjgi n  -> Ops.Mjlei n
    in
    let instruction = function
    | Ops.Mjz     -> X86_64.jz
    | Ops.Mjnz    -> X86_64.jnz
    | Ops.Mjlei n -> X86_64.jle
    | Ops.Mjgi n  -> X86_64.jg
    in

    first_instruction mubranch;

    let asm_inst = instruction mubranch and asm_opp = instruction (opposite mubranch) in

    if(not(Hashtbl.mem visited label3)) then begin
      (*print_string "didn't see the negatif, the positif is :";
      Label.print std_formatter label2;
      print_string "\n";*)
      emit_wl (asm_inst (label2:> string));
      need_label label2;
      lin g label3;
      lin g label2;
    end else if(not(Hashtbl.mem visited label2)) then begin
      (*print_string "saw the negatif but didn't see the positif\n";*)
      emit_wl (asm_opp (label3:> string));
      need_label label3;
      lin g label2;
      lin g label3;
    end else begin
      (*print_string "saw the negatif : ";
      Label.print std_formatter label3;
      print_string " and the positif :";
      Label.print std_formatter label2;
      print_string "\n";*)
      emit_wl (asm_inst (label2:> string));
      need_label label2;
      lin g label3; (* this will produce the jmp label3 instruction *)
    end;

  and treat_mbbranch mbbranch r1 r2 label2 label3 g l =
    emit l (X86_64.cmpq (operand r1) (operand r2));
    let opposite_instruction = function
    | Ops.Mjl     -> X86_64.jge
    | Ops.Mjle    -> X86_64.jg
    in
    let instruction = function
    | Ops.Mjl     -> X86_64.jl
    | Ops.Mjle    -> X86_64.jle
    in
    let asm_inst = instruction mbbranch and asm_opp = opposite_instruction mbbranch in
    if(not(Hashtbl.mem visited label3)) then begin
      (*print_string "didn't see the negatif ";
      Label.print std_formatter label3;
      print_string "\n";*)
      emit_wl (asm_inst (label2 :> string));
      need_label label2;
      lin g label3;
      lin g label2;
    end else if(not(Hashtbl.mem visited label2)) then begin
      (*print_string "saw the negatif but didn't see the positif\n";*)
      emit_wl (asm_opp (label3:> string));
      need_label label3;
      lin g label2;
      lin g label3;
    end else begin
      (*print_string "saw the negatif and the positif\n";*)
      emit_wl (asm_inst (label2:> string));
      need_label label2;
      lin g label3; (* this will produce the jmp label3 instruction *)
    end;;


let generate_code final_code (fun_def:Ltltree.deffun)  = 
  code := [];
  let first_label = fun_def.fun_entry in
  let function_id = fun_def.fun_name in
  map_label_to_function first_label function_id;
  need_label first_label;
  lin fun_def.fun_body first_label;
  (*Hashtbl.iter (fun l _ -> Label.print std_formatter l; print_string " ") labels;
  print_string "\n";*)
  let clean = function
    | Label l -> (*Label.print std_formatter l;*) Hashtbl.mem labels l
    | Code i -> true
  in
  code := List.filter clean !code;
  let concatenate x y =
    match y with
    | Label l -> X86_64.(++) x (find_label l)
    | Code i -> X86_64.(++) x i;
  in
  let asm_code = List.fold_left concatenate (X86_64.globl function_id) (List.rev !code)  in
  final_code := asm_code::!final_code;;


let program (p:Ltltree.file) =
  let final_code = ref [] in
  List.iter (generate_code final_code) p.funs;
  let asm_code = List.fold_right (fun x y -> X86_64.(++) x y) (List.rev !final_code) (X86_64.nop) in
  let asm_program:X86_64.program = {text = asm_code; data = X86_64.nop} in
  asm_program