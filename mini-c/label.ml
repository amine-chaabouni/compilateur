
type t = string

let r = ref 0
let fresh () = incr r; "L" ^ string_of_int !r

module M = Map.Make(String)

type 'a map = 'a M.t

module S = Set.Make(String)

type set = S.t

let print = Format.pp_print_string

let print_set fmt s =
  Pp.print_list Pp.comma Format.pp_print_string fmt (S.elements s)

let print_list fmt s =
  Pp.print_list Pp.comma Format.pp_print_string fmt s

let of_string l = l
