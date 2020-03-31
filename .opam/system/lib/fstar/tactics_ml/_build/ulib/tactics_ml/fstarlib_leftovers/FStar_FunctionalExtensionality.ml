open Prims
type ('Aa,'Ab) arrow = 'Aa -> 'Ab
type ('Aa,'Ab) efun = 'Aa -> 'Ab
type ('Aa,'Ab,'Af,'Ag) feq = unit
let on_domain : 'Aa 'Ab . ('Aa -> 'Ab) -> 'Aa -> 'Ab = fun f  -> f 


type ('Aa,'Ab,'Af) is_restricted = unit
type ('Aa,'Ab) restricted_t = 'Aa -> 'Ab
type ('Aa,'Ab) op_Hat_Subtraction_Greater = ('Aa,'Ab) restricted_t
let on_dom : 'Aa 'Ab . ('Aa -> 'Ab) -> ('Aa,'Ab) restricted_t = fun f  -> f 
let on : 'Aa 'Ab . ('Aa -> 'Ab) -> ('Aa,'Ab) restricted_t = fun f  -> f 

type ('Aa,'Ab) arrow_g = unit
type ('Aa,'Ab) efun_g = unit
type ('Aa,'Ab,'Af,'Ag) feq_g = unit



type ('Aa,'Ab,'Af) is_restricted_g = unit
type ('Aa,'Ab) restricted_g_t = unit
type ('Aa,'Ab) op_Hat_Subtraction_Greater_Greater = unit


