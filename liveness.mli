type live_info = {
  instr: Ertltree.instr;
  succ: Label.t list;             (* successeurs *)
  mutable pred: Label.set;        (* prédécesseurs *)
  defs: Register.set;             (* définitions *)
  uses: Register.set;             (* utilisations *)
  mutable  ins: Register.set;     (* variables vivantes en entrée *)
  mutable outs: Register.set;     (* variables vivantes en sortie *)
}

(** Liveness **)
val liveness: Ertltree.instr Label.M.t -> live_info Label.M.t

val program : Ertltree.file -> unit