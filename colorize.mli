type color = Ltltree.operand
type coloring = color Register.map

val colorize : Interference.igraph -> coloring*int