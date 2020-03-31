type uint64 = Stdint.Uint64.t
type t = uint64
           
let (%) x y = if x < 0 then (x mod y) + y else x mod y

let v (x:uint64) : Prims.int = Prims.parse_int (Stdint.Uint64.to_string x)

let zero = Stdint.Uint64.zero
let one = Stdint.Uint64.one
let ones = Stdint.Uint64.pred Stdint.Uint64.zero

let add (a:uint64) (b:uint64) : uint64 = Stdint.Uint64.add a b
let add_underspec a b = add a b
let add_mod a b = add a b

let sub (a:uint64) (b:uint64) : uint64 = Stdint.Uint64.sub a b
let sub_underspec a b = sub a b
let sub_mod a b = sub a b

let mul (a:uint64) (b:uint64) : uint64 = Stdint.Uint64.mul a b
let mul_underspec a b = mul a b
let mul_mod a b = mul a b

let div (a:uint64) (b:uint64) : uint64 = Stdint.Uint64.div a b

let rem (a:uint64) (b:uint64) : uint64 = Stdint.Uint64.rem a b

let logand (a:uint64) (b:uint64) : uint64 = Stdint.Uint64.logand a b
let logxor (a:uint64) (b:uint64) : uint64 = Stdint.Uint64.logxor a b
let logor  (a:uint64) (b:uint64) : uint64 = Stdint.Uint64.logor a b
let lognot (a:uint64) : uint64 = Stdint.Uint64.lognot a
                                              
let int_to_uint64 (x:Prims.int) : uint64= Stdint.Uint64.of_string (Prims.to_string x)

let shift_right (a:uint64) (b:int64) : uint64 = Stdint.Uint64.shift_right a (Int64.to_int b)
let shift_left  (a:uint64) (b:int64) : uint64 = Stdint.Uint64.shift_left a (Int64.to_int b)

(* Comparison operators *)
let eq (a:uint64) (b:uint64) : bool = a = b
let gt (a:uint64) (b:uint64) : bool = a > b
let gte (a:uint64) (b:uint64) : bool = a >= b
let lt (a:uint64) (b:uint64) : bool = a < b
let lte (a:uint64) (b:uint64) : bool =  a <= b

(* Constant time operator (TODO!) *)
let eq_mask (a:uint64) (b:uint64) : uint64 = if a = b then Stdint.Uint64.pred Stdint.Uint64.zero
                                             else Stdint.Uint64.zero
let gte_mask (a:uint64) (b:uint64) : uint64 = if a >= b then Stdint.Uint64.pred Stdint.Uint64.zero
                                             else Stdint.Uint64.zero
                                               
(* Infix notations *)
let op_Plus_Hat = add
let op_Plus_Question_Hat = add_underspec
let op_Plus_Percent_Hat = add_mod
let op_Subtraction_Hat = sub
let op_Subtraction_Question_Hat = sub_underspec
let op_Subtraction_Percent_Hat = sub_mod
let op_Star_Hat = mul
let op_Star_Question_Hat = mul_underspec
let op_Star_Percent_Hat = mul_mod
let op_Slash_Hat = div
let op_Percent_Hat = rem
let op_Hat_Hat = logxor  
let op_Amp_Hat = logand
let op_Bar_Hat = logor
let op_Less_Less_Hat = shift_left
let op_Greater_Greater_Hat = shift_right
let op_Equals_Hat = eq
let op_Greater_Hat = gt
let op_Greater_Equals_Hat = gte
let op_Less_Hat = lt
let op_Less_Equals_Hat = lte

let to_string s = Stdint.Uint64.to_string s
let of_string s = Stdint.Uint64.of_string s

let uint_to_t s = Stdint.Uint64.of_string (Z.to_string s)
