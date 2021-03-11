open Format
exception Error of string

let word_size = 8;;

let raise_error  error =
  raise (Error error);;

type color = Ltltree.operand
type coloring = color Register.map



exception Reg_Is_Colorable of (Register.t*Register.t)
exception No_Colorization of Register.t
let find_colorable_register (ig:Interference.igraph) todo colorization =

  (* Gets a subset of colorization satisfying only one possible color *)
  let only_one_color  = 
    Register.M.filter (fun reg set -> Register.S.mem reg todo && Register.S.cardinal set = 1) colorization
  in
  (* If there is at least one register with only one possible color :*)
  if(not (Register.M.is_empty only_one_color)) then begin
    (* See if there is a register with one preference edge to that color *)
    let find_preference_color register color_set = 
      let color = Register.S.min_elt color_set in (* color_set have exactly one element *)
      let reg_prefs = (Register.M.find register ig).prefs in
      if(Register.S.mem color reg_prefs) then raise (Reg_Is_Colorable (register, color))
    in
    Register.M.iter find_preference_color only_one_color;
    (* If no prefered color is found, return one arbitrary register from only_one_color *)
    let register,color_set = Register.M.min_binding only_one_color in
    raise (Reg_Is_Colorable (register, Register.S.min_elt color_set))
  end
  else begin
    (* Find a register with known colorized preference edge
      Loop over the preference sets see if already colorized *)
    let process_reg register =
      let possible_colors = Register.M.find register colorization in
      let prefs = (Register.M.find register ig).prefs in


      let check_if_allocatable r =
        if (Register.S.mem r Register.allocatable) then
              if(Register.S.mem r possible_colors) then (*Make sure it is okay to choose this color*)
                raise (Reg_Is_Colorable(register, r))
      in
      Register.S.iter check_if_allocatable prefs;

      let check_if_colorized r =
        (* Check if register is not allocatable -already did that case- and that it has already been treated *)
        if(not (Register.S.mem r Register.allocatable) && not (Register.S.mem r todo)) then 
          begin
            let color_set = try 
              Register.M.find r colorization
            with Not_found -> raise_error ((r:>string) ^ " not found") in
            if(Register.S.cardinal color_set = 1) then
              let color =  Register.S.min_elt color_set in
              if(Register.S.mem color possible_colors) then (*Make sure it is okay to choose this color*)
                raise (Reg_Is_Colorable(register, color))
          end
      in
      Register.S.iter check_if_colorized prefs
    in
    Register.S.iter process_reg todo;

    (* No such registers found, so choose a random one*)
    let random_colorizable_register register =
      let potential_colors = Register.M.find register colorization in
      if not (Register.S.is_empty potential_colors) then
        raise (Reg_Is_Colorable (register, Register.S.min_elt potential_colors))
    in
    Register.S.iter random_colorizable_register todo;

    (* No possible colorization *)
    raise (No_Colorization (Register.S.min_elt todo));
  end

let colorize (ig:Interference.igraph) =
  let counter = ref 0 in
  let pseudo_registers = Seq.filter_map (function (r, _) -> if Register.is_pseudo r then Some r else None) (Register.M.to_seq ig) in 
  let todo = ref (Register.S.of_seq pseudo_registers) in
  let colorization = ref Register.M.empty in
  let add_reg_to_colorization r =
    let potential_colors = Register.S.diff Register.allocatable (Register.M.find r ig).intfs in
    colorization := Register.M.add r potential_colors !colorization
  in
  Register.S.iter add_reg_to_colorization !todo;

  let colorized : coloring ref = ref Register.M.empty in

  while not (Register.S.is_empty !todo) do
    try (find_colorable_register ig) !todo !colorization with
    | Reg_Is_Colorable (register, color) -> begin
      (* Remember the colorization *)
      colorized := Register.M.add register (Ltltree.Reg color) !colorized;
      (* Remove other possible colors of register *)
      colorization := Register.M.remove register !colorization;
      colorization := Register.M.add register (Register.S.singleton color) !colorization;
      (* Remove the register from todo *)
      todo := Register.S.remove register !todo;
      (* Remove the color from all intereferences still in todo *)
      let intfs = (Register.M.find register ig).intfs in
      let remove_color_from_interference key color_set = 
        if(Register.S.mem key !todo && Register.S.mem key intfs) then Register.S.remove color color_set else color_set
      in
      colorization := Register.M.mapi remove_color_from_interference !colorization;
    end
    | No_Colorization register -> begin
      (* Spill register *)
      counter := (!counter) - word_size;
      colorized := Register.M.add register (Ltltree.Spilled !counter) !colorized;
      (* Remove register from todo *)
      todo := Register.S.remove register !todo;
    end
  done;

  !colorized, (!counter);;




open Format
(* Function to print color *)
let print_color fmt = function
| Ltltree.Reg hr    -> fprintf fmt "%a" Register.print hr
| Ltltree.Spilled n -> fprintf fmt "stack %d" n
let print_cm cm =
Register.M.iter
  (fun r cr -> printf "%a -> %a@\n" Register.print r print_color cr) cm
