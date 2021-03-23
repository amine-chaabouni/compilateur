
(** {2 Opérations x86-64} *)

(** opérations unaires *)
type munop =
  | Maddi   of int32
  | Msetei  of int32
  | Msetnei of int32

(** opérations binaires *)
type mbinop =
  | Mmov
  | Madd
  | Msub
  | Mmul
  | Mdiv
  | Msete
  | Msetne
  | Msetl
  | Msetle
  | Msetg
  | Msetge

(** opérations de branchement unaires *)
type mubranch =
  | Mjz
  | Mjnz
  | Mjlei of int32
  | Mjgi  of int32

(** opérations de branchement binaires *)
type mbbranch =
  | Mjl
  | Mjle

(** {2 Fonctions d'impression} *)

val print_munop: Format.formatter -> munop -> unit

val print_mbinop: Format.formatter -> mbinop -> unit

val print_mubranch: Format.formatter -> mubranch -> unit

val print_mbbranch: Format.formatter -> mbbranch -> unit

