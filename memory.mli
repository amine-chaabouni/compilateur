
(** {2 Un modèle mémoire minimal pour les interprètes Interp et RTL}

    Cf [Machine] pour un modèle plus bas niveau, utilisé pour les interprètes
    ERTL et LTL. *)

type t
(** le type abstrait d'une mémoire *)

type value = int64
type ptr = int64
(** ici toutes les valeurs sont des entiers 64 bits *)

val word_size: int
(** vaut ici 8, i.e., 64 bits *)

val zero: value
val one: value

exception Error of string
(** cette exception est levée en cas d'accès illégal à la mémoire *)

val create: unit -> t
(** renvoie une mémoire fraîche *)

val malloc: t -> int -> ptr
(** [malloc t n] alloue [n] octets *)

val get: t -> ptr -> ofs:int -> value
(** lit en mémoire ; [ofs] doit être un multiple de [word_size] *)

val set: t -> ptr -> ofs:int -> value -> unit
(** écrit en mémoire ; [ofs] doit être un multiple de [word_size] *)

