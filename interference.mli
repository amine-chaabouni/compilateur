type arcs = { mutable prefs: Register.set; mutable intfs: Register.set }

type igraph = arcs Register.map

val make : Ertltree.live_info Label.M.t -> igraph

val print_ig : igraph -> unit