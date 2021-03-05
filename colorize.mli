type color = Ltltree.operand
type coloring = color Register.map

val colorize : Interference.igraph -> coloring*int

val print_cm : coloring -> unit