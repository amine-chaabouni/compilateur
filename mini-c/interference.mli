type arcs = { mutable prefs: Register.set; mutable intfs: Register.set }

type igraph = arcs Register.map

val make : Liveness.live_info Label.M.t -> igraph

val print_ig : igraph -> unit

val program : Ertltree.file -> unit