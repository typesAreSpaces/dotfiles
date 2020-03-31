open Prims
let (n : Prims.int) = (Prims.of_int (31)) 
type t =
  | Mk of unit FStar_UInt.uint_t 
let (uu___is_Mk : t -> Prims.bool) = fun projectee  -> true 
let (__proj__Mk__item__v : t -> unit FStar_UInt.uint_t) =
  fun projectee  -> match projectee with | Mk v1 -> v1 
let (v : t -> unit FStar_UInt.uint_t) = fun x  -> __proj__Mk__item__v x 
let (uint_to_t : unit FStar_UInt.uint_t -> t) = fun x  -> Mk x 



let (add : t -> t -> t) =
  fun a  -> fun b  -> Mk (FStar_UInt.add (Prims.of_int (31)) (v a) (v b)) 
let (add_underspec : t -> t -> t) =
  fun a  ->
    fun b  -> Mk (FStar_UInt.add_underspec (Prims.of_int (31)) (v a) (v b))
  
let (add_mod : t -> t -> t) =
  fun a  -> fun b  -> Mk (FStar_UInt.add_mod (Prims.of_int (31)) (v a) (v b)) 
let (sub : t -> t -> t) =
  fun a  -> fun b  -> Mk (FStar_UInt.sub (Prims.of_int (31)) (v a) (v b)) 
let (sub_underspec : t -> t -> t) =
  fun a  ->
    fun b  -> Mk (FStar_UInt.sub_underspec (Prims.of_int (31)) (v a) (v b))
  
let (sub_mod : t -> t -> t) =
  fun a  -> fun b  -> Mk (FStar_UInt.sub_mod (Prims.of_int (31)) (v a) (v b)) 
let (mul : t -> t -> t) =
  fun a  -> fun b  -> Mk (FStar_UInt.mul (Prims.of_int (31)) (v a) (v b)) 
let (mul_underspec : t -> t -> t) =
  fun a  ->
    fun b  -> Mk (FStar_UInt.mul_underspec (Prims.of_int (31)) (v a) (v b))
  
let (mul_mod : t -> t -> t) =
  fun a  -> fun b  -> Mk (FStar_UInt.mul_mod (Prims.of_int (31)) (v a) (v b)) 
let (mul_div : t -> t -> t) =
  fun a  -> fun b  -> Mk (FStar_UInt.mul_div (Prims.of_int (31)) (v a) (v b)) 
let (div : t -> t -> t) =
  fun a  -> fun b  -> Mk (FStar_UInt.div (Prims.of_int (31)) (v a) (v b)) 
let (rem : t -> t -> t) =
  fun a  -> fun b  -> Mk (FStar_UInt.mod_ (Prims.of_int (31)) (v a) (v b)) 
let (logand : t -> t -> t) =
  fun x  -> fun y  -> Mk (FStar_UInt.logand (Prims.of_int (31)) (v x) (v y)) 
let (logxor : t -> t -> t) =
  fun x  -> fun y  -> Mk (FStar_UInt.logxor (Prims.of_int (31)) (v x) (v y)) 
let (logor : t -> t -> t) =
  fun x  -> fun y  -> Mk (FStar_UInt.logor (Prims.of_int (31)) (v x) (v y)) 
let (lognot : t -> t) =
  fun x  -> Mk (FStar_UInt.lognot (Prims.of_int (31)) (v x)) 
let (shift_right : t -> FStar_UInt32.t -> t) =
  fun a  ->
    fun s  ->
      Mk
        (FStar_UInt.shift_right (Prims.of_int (31)) (v a) (FStar_UInt32.v s))
  
let (shift_left : t -> FStar_UInt32.t -> t) =
  fun a  ->
    fun s  ->
      Mk (FStar_UInt.shift_left (Prims.of_int (31)) (v a) (FStar_UInt32.v s))
  
let (eq : t -> t -> Prims.bool) =
  fun a  -> fun b  -> FStar_UInt.eq (Prims.of_int (31)) (v a) (v b) 
let (gt : t -> t -> Prims.bool) =
  fun a  -> fun b  -> FStar_UInt.gt (Prims.of_int (31)) (v a) (v b) 
let (gte : t -> t -> Prims.bool) =
  fun a  -> fun b  -> FStar_UInt.gte (Prims.of_int (31)) (v a) (v b) 
let (lt : t -> t -> Prims.bool) =
  fun a  -> fun b  -> FStar_UInt.lt (Prims.of_int (31)) (v a) (v b) 
let (lte : t -> t -> Prims.bool) =
  fun a  -> fun b  -> FStar_UInt.lte (Prims.of_int (31)) (v a) (v b) 
let (minus : t -> t) = fun a  -> add_mod (lognot a) (uint_to_t Prims.int_one) 
let (n_minus_one : FStar_UInt32.t) =
  FStar_UInt32.uint_to_t (Prims.of_int (30)) 
let (eq_mask : t -> t -> t) =
  fun a  ->
    fun b  ->
      let x = logxor a b  in
      let minus_x = add_mod (lognot x) (uint_to_t Prims.int_one)  in
      let x_or_minus_x = logor x minus_x  in
      let xnx =
        shift_right x_or_minus_x (FStar_UInt32.uint_to_t (Prims.of_int (30)))
         in
      let c = sub_mod xnx (uint_to_t Prims.int_one)  in c
  

let (gte_mask : t -> t -> t) =
  fun a  ->
    fun b  ->
      let x = a  in
      let y = b  in
      let x_xor_y = logxor x y  in
      let x_sub_y = sub_mod x y  in
      let x_sub_y_xor_y = logxor x_sub_y y  in
      let q = logor x_xor_y x_sub_y_xor_y  in
      let x_xor_q = logxor x q  in
      let x_xor_q_ =
        shift_right x_xor_q (FStar_UInt32.uint_to_t (Prims.of_int (30)))  in
      let c = sub_mod x_xor_q_ (uint_to_t Prims.int_one)  in c
  
let (op_Plus_Hat : t -> t -> t) = add 
let (op_Plus_Question_Hat : t -> t -> t) = add_underspec 
let (op_Plus_Percent_Hat : t -> t -> t) = add_mod 
let (op_Subtraction_Hat : t -> t -> t) = sub 
let (op_Subtraction_Question_Hat : t -> t -> t) = sub_underspec 
let (op_Subtraction_Percent_Hat : t -> t -> t) = sub_mod 
let (op_Star_Hat : t -> t -> t) = mul 
let (op_Star_Question_Hat : t -> t -> t) = mul_underspec 
let (op_Star_Percent_Hat : t -> t -> t) = mul_mod 
let (op_Star_Slash_Hat : t -> t -> t) = mul_div 
let (op_Slash_Hat : t -> t -> t) = div 
let (op_Percent_Hat : t -> t -> t) = rem 
let (op_Hat_Hat : t -> t -> t) = logxor 
let (op_Amp_Hat : t -> t -> t) = logand 
let (op_Bar_Hat : t -> t -> t) = logor 
let (op_Less_Less_Hat : t -> FStar_UInt32.t -> t) = shift_left 
let (op_Greater_Greater_Hat : t -> FStar_UInt32.t -> t) = shift_right 
let (op_Equals_Hat : t -> t -> Prims.bool) = eq 
let (op_Greater_Hat : t -> t -> Prims.bool) = gt 
let (op_Greater_Equals_Hat : t -> t -> Prims.bool) = gte 
let (op_Less_Hat : t -> t -> Prims.bool) = lt 
let (op_Less_Equals_Hat : t -> t -> Prims.bool) = lte 
let (to_string : t -> Prims.string) =
  fun uu____716  -> failwith "Not yet implemented:to_string" 
let (of_string : Prims.string -> t) =
  fun uu____728  -> failwith "Not yet implemented:of_string" 
let (__uint_to_t : Prims.int -> t) = fun x  -> uint_to_t x 