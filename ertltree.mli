
(** {2 Explicit Register Transfer Language (ERTL)} *)

open Ops

type ident = string
  (** uniquement pour les fonctions *)

type register = Register.t

type label = Label.t

(** Les différentes instructions ERTL *)
type instr =
  (** les mêmes que dans RTL *)
  | Econst of int32 * register * label
  | Eload of register * int * register * label
  | Estore of register * register * int * label
  | Emunop of munop * register * label
  | Embinop of mbinop * register * register * label
  | Emubranch of mubranch * register * label * label
  | Embbranch of mbbranch * register * register * label * label
  | Egoto of label
      (** l'entier est le nombre de paramètres passés dans des registres *)
  | Ecall of ident * int * label
  | Ealloc_frame of label
  | Edelete_frame of label
      (** [r <- ofs(rbp)] *)
  | Eget_param of int * register * label
  | Epush_param of register * label
  | Ereturn

type cfg = instr Label.map
  (** Un graphe de flot de contrôle est un dictionnaire associant à des
      étiquettes des instructions ERTL. *)

(** Une fonction ERTL. *)
type deffun = {
  fun_name : ident;
  fun_formals : int; (* nb total d'arguments *)
  fun_locals : Register.set;
  fun_entry : label;
  fun_body : cfg;
}

type live_info = {
  instr: instr;
  succ: Label.t list;             (* successeurs *)
  mutable pred: Label.set;        (* prédécesseurs *)
  defs: Register.set;             (* définitions *)
  uses: Register.set;             (* utilisations *)
  mutable  ins: Register.set;     (* variables vivantes en entrée *)
  mutable outs: Register.set;     (* variables vivantes en sortie *)
}

(** Un programme ERTL. *)
type file = {
  funs : deffun list;
}

(** {2 Quelques fonctions qui seront utiles pour la phase suivante} *)

val succ: instr -> label list
  (** successeurs dans le graphe *)

val def_use: instr -> register list * register list
  (** calcul des définitions et utilisations de chaque instruction *)

val visit: bool -> (label -> instr -> live_info -> bool -> unit) -> cfg -> label -> unit
  (** visite le graphe de flot de contrôle à partir d'une étiquette donnée *)

(** {2 Fonctions d'impression, pour debugger} *)

val print_instr: Format.formatter -> instr -> unit

val print_graph: Format.formatter -> bool -> cfg -> label -> unit

val print_deffun: Format.formatter -> bool -> deffun -> unit

val print_file: Format.formatter -> file -> bool -> unit
