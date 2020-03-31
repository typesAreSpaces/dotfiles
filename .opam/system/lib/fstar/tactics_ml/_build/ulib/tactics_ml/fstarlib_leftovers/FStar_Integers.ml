open Prims

let norm : 'Aa . 'Aa -> 'Aa = fun x  -> x 
type width =
  | W8 
  | W16 
  | W31 
  | W32 
  | W63 
  | W64 
  | W128 
  | Winfinite 
let (uu___is_W8 : width -> Prims.bool) =
  fun projectee  -> match projectee with | W8  -> true | uu____23 -> false 
let (uu___is_W16 : width -> Prims.bool) =
  fun projectee  -> match projectee with | W16  -> true | uu____35 -> false 
let (uu___is_W31 : width -> Prims.bool) =
  fun projectee  -> match projectee with | W31  -> true | uu____47 -> false 
let (uu___is_W32 : width -> Prims.bool) =
  fun projectee  -> match projectee with | W32  -> true | uu____59 -> false 
let (uu___is_W63 : width -> Prims.bool) =
  fun projectee  -> match projectee with | W63  -> true | uu____71 -> false 
let (uu___is_W64 : width -> Prims.bool) =
  fun projectee  -> match projectee with | W64  -> true | uu____83 -> false 
let (uu___is_W128 : width -> Prims.bool) =
  fun projectee  -> match projectee with | W128  -> true | uu____95 -> false 
let (uu___is_Winfinite : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Winfinite  -> true | uu____107 -> false
  
let (nat_of_width : width -> Prims.int FStar_Pervasives_Native.option) =
  fun uu___0_118  ->
    match uu___0_118 with
    | W8  -> FStar_Pervasives_Native.Some (Prims.of_int (8))
    | W16  -> FStar_Pervasives_Native.Some (Prims.of_int (16))
    | W31  -> FStar_Pervasives_Native.Some (Prims.of_int (31))
    | W32  -> FStar_Pervasives_Native.Some (Prims.of_int (32))
    | W63  -> FStar_Pervasives_Native.Some (Prims.of_int (63))
    | W64  -> FStar_Pervasives_Native.Some (Prims.of_int (64))
    | W128  -> FStar_Pervasives_Native.Some (Prims.of_int (128))
    | Winfinite  -> FStar_Pervasives_Native.None
  
type fixed_width = width
let (nat_of_fixed_width : fixed_width -> Prims.int) =
  fun w  -> match nat_of_width w with | FStar_Pervasives_Native.Some v1 -> v1 
type signed_width =
  | Signed of width 
  | Unsigned of fixed_width 
let (uu___is_Signed : signed_width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Signed _0 -> true | uu____170 -> false
  
let (__proj__Signed__item___0 : signed_width -> width) =
  fun projectee  -> match projectee with | Signed _0 -> _0 
let (uu___is_Unsigned : signed_width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unsigned _0 -> true | uu____193 -> false
  
let (__proj__Unsigned__item___0 : signed_width -> fixed_width) =
  fun projectee  -> match projectee with | Unsigned _0 -> _0 
let (width_of_sw : signed_width -> width) =
  fun uu___1_212  -> match uu___1_212 with | Signed w -> w | Unsigned w -> w 
type 'Asw int_t = Obj.t
type ('Asw,'Ax) within_bounds' = Obj.t
type ('Asw,'Ax) within_bounds = Obj.t
let (v : signed_width -> Obj.t -> Prims.int) =
  fun a1  ->
    fun a2  ->
      (fun sw  ->
         fun x  ->
           match sw with
           | Unsigned w ->
               Obj.magic
                 (Obj.repr
                    (match w with
                     | W8  -> FStar_UInt8.v (Obj.magic x)
                     | W16  -> FStar_UInt16.v (Obj.magic x)
                     | W31  -> FStar_UInt31.v (Obj.magic x)
                     | W32  -> FStar_UInt32.v (Obj.magic x)
                     | W63  -> FStar_UInt63.v (Obj.magic x)
                     | W64  -> FStar_UInt64.v (Obj.magic x)
                     | W128  -> FStar_UInt128.v (Obj.magic x)))
           | Signed w ->
               Obj.magic
                 (Obj.repr
                    (match w with
                     | Winfinite  -> Obj.repr x
                     | W8  -> Obj.repr (FStar_Int8.v (Obj.magic x))
                     | W16  -> Obj.repr (FStar_Int16.v (Obj.magic x))
                     | W31  -> Obj.repr (FStar_Int31.v (Obj.magic x))
                     | W32  -> Obj.repr (FStar_Int32.v (Obj.magic x))
                     | W63  -> Obj.repr (FStar_Int63.v (Obj.magic x))
                     | W64  -> Obj.repr (FStar_Int64.v (Obj.magic x))
                     | W128  -> Obj.repr (FStar_Int128.v (Obj.magic x))))) a1
        a2
  
let (u : signed_width -> Prims.int -> Obj.t) =
  fun sw  ->
    fun x  ->
      match sw with
      | Unsigned w ->
          (match w with
           | W8  -> Obj.repr (FStar_UInt8.uint_to_t x)
           | W16  -> Obj.repr (FStar_UInt16.uint_to_t x)
           | W31  -> Obj.repr (FStar_UInt31.uint_to_t x)
           | W32  -> Obj.repr (FStar_UInt32.uint_to_t x)
           | W63  -> Obj.repr (FStar_UInt63.uint_to_t x)
           | W64  -> Obj.repr (FStar_UInt64.uint_to_t x)
           | W128  -> Obj.repr (FStar_UInt128.uint_to_t x))
      | Signed w ->
          (match w with
           | Winfinite  -> Obj.repr x
           | W8  -> Obj.repr (FStar_Int8.int_to_t x)
           | W16  -> Obj.repr (FStar_Int16.int_to_t x)
           | W31  -> Obj.repr (FStar_Int31.int_to_t x)
           | W32  -> Obj.repr (FStar_Int32.int_to_t x)
           | W63  -> Obj.repr (FStar_Int63.int_to_t x)
           | W64  -> Obj.repr (FStar_Int64.int_to_t x)
           | W128  -> Obj.repr (FStar_Int128.int_to_t x))
  
let (cast : signed_width -> signed_width -> Obj.t -> Obj.t) =
  fun sw  -> fun sw'  -> fun from  -> u sw' (v sw from) 
type ('Afrom,'Ato_311,'Ax) cast_ok = Obj.t
let (op_Plus : signed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Signed (Winfinite ) -> Obj.repr ((Obj.magic x) + (Obj.magic y))
        | Unsigned (W8 ) ->
            Obj.repr (FStar_UInt8.add (Obj.magic x) (Obj.magic y))
        | Unsigned (W16 ) ->
            Obj.repr (FStar_UInt16.add (Obj.magic x) (Obj.magic y))
        | Unsigned (W31 ) ->
            Obj.repr (FStar_UInt31.add (Obj.magic x) (Obj.magic y))
        | Unsigned (W32 ) ->
            Obj.repr (FStar_UInt32.add (Obj.magic x) (Obj.magic y))
        | Unsigned (W63 ) ->
            Obj.repr (FStar_UInt63.add (Obj.magic x) (Obj.magic y))
        | Unsigned (W64 ) ->
            Obj.repr (FStar_UInt64.add (Obj.magic x) (Obj.magic y))
        | Unsigned (W128 ) ->
            Obj.repr (FStar_UInt128.add (Obj.magic x) (Obj.magic y))
        | Signed (W8 ) ->
            Obj.repr (FStar_Int8.add (Obj.magic x) (Obj.magic y))
        | Signed (W16 ) ->
            Obj.repr (FStar_Int16.add (Obj.magic x) (Obj.magic y))
        | Signed (W31 ) ->
            Obj.repr (FStar_Int31.add (Obj.magic x) (Obj.magic y))
        | Signed (W32 ) ->
            Obj.repr (FStar_Int32.add (Obj.magic x) (Obj.magic y))
        | Signed (W63 ) ->
            Obj.repr (FStar_Int63.add (Obj.magic x) (Obj.magic y))
        | Signed (W64 ) ->
            Obj.repr (FStar_Int64.add (Obj.magic x) (Obj.magic y))
        | Signed (W128 ) ->
            Obj.repr (FStar_Int128.add (Obj.magic x) (Obj.magic y))
  
let (op_Plus_Question : fixed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun w  ->
    fun x  ->
      fun y  ->
        match w with
        | W8  ->
            Obj.repr (FStar_UInt8.add_underspec (Obj.magic x) (Obj.magic y))
        | W16  ->
            Obj.repr (FStar_UInt16.add_underspec (Obj.magic x) (Obj.magic y))
        | W31  ->
            Obj.repr (FStar_UInt31.add_underspec (Obj.magic x) (Obj.magic y))
        | W32  ->
            Obj.repr (FStar_UInt32.add_underspec (Obj.magic x) (Obj.magic y))
        | W63  ->
            Obj.repr (FStar_UInt63.add_underspec (Obj.magic x) (Obj.magic y))
        | W64  ->
            Obj.repr (FStar_UInt64.add_underspec (Obj.magic x) (Obj.magic y))
        | W128  ->
            Obj.repr
              (FStar_UInt128.add_underspec (Obj.magic x) (Obj.magic y))
  
let (modulo : signed_width -> Prims.int -> Prims.pos -> Prims.int) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Unsigned uu____378 -> x mod y
        | uu____379 -> FStar_Int.op_At_Percent x y
  
let (op_Plus_Percent : signed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        let uu____401 = sw  in
        match uu____401 with
        | Unsigned w ->
            (match w with
             | W8  ->
                 Obj.repr (FStar_UInt8.add_mod (Obj.magic x) (Obj.magic y))
             | W16  ->
                 Obj.repr (FStar_UInt16.add_mod (Obj.magic x) (Obj.magic y))
             | W31  ->
                 Obj.repr (FStar_UInt31.add_mod (Obj.magic x) (Obj.magic y))
             | W32  ->
                 Obj.repr (FStar_UInt32.add_mod (Obj.magic x) (Obj.magic y))
             | W63  ->
                 Obj.repr (FStar_UInt63.add_mod (Obj.magic x) (Obj.magic y))
             | W64  ->
                 Obj.repr (FStar_UInt64.add_mod (Obj.magic x) (Obj.magic y))
             | W128  ->
                 Obj.repr (FStar_UInt128.add_mod (Obj.magic x) (Obj.magic y)))
  
let (op_Subtraction : signed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Signed (Winfinite ) -> Obj.repr ((Obj.magic x) - (Obj.magic y))
        | Unsigned (W8 ) ->
            Obj.repr (FStar_UInt8.sub (Obj.magic x) (Obj.magic y))
        | Unsigned (W16 ) ->
            Obj.repr (FStar_UInt16.sub (Obj.magic x) (Obj.magic y))
        | Unsigned (W31 ) ->
            Obj.repr (FStar_UInt31.sub (Obj.magic x) (Obj.magic y))
        | Unsigned (W32 ) ->
            Obj.repr (FStar_UInt32.sub (Obj.magic x) (Obj.magic y))
        | Unsigned (W63 ) ->
            Obj.repr (FStar_UInt63.sub (Obj.magic x) (Obj.magic y))
        | Unsigned (W64 ) ->
            Obj.repr (FStar_UInt64.sub (Obj.magic x) (Obj.magic y))
        | Unsigned (W128 ) ->
            Obj.repr (FStar_UInt128.sub (Obj.magic x) (Obj.magic y))
        | Signed (W8 ) ->
            Obj.repr (FStar_Int8.sub (Obj.magic x) (Obj.magic y))
        | Signed (W16 ) ->
            Obj.repr (FStar_Int16.sub (Obj.magic x) (Obj.magic y))
        | Signed (W31 ) ->
            Obj.repr (FStar_Int31.sub (Obj.magic x) (Obj.magic y))
        | Signed (W32 ) ->
            Obj.repr (FStar_Int32.sub (Obj.magic x) (Obj.magic y))
        | Signed (W63 ) ->
            Obj.repr (FStar_Int63.sub (Obj.magic x) (Obj.magic y))
        | Signed (W64 ) ->
            Obj.repr (FStar_Int64.sub (Obj.magic x) (Obj.magic y))
        | Signed (W128 ) ->
            Obj.repr (FStar_Int128.sub (Obj.magic x) (Obj.magic y))
  
let (op_Subtraction_Question : signed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        let uu____443 = sw  in
        match uu____443 with
        | Unsigned w ->
            (match w with
             | W8  ->
                 Obj.repr
                   (FStar_UInt8.sub_underspec (Obj.magic x) (Obj.magic y))
             | W16  ->
                 Obj.repr
                   (FStar_UInt16.sub_underspec (Obj.magic x) (Obj.magic y))
             | W31  ->
                 Obj.repr
                   (FStar_UInt31.sub_underspec (Obj.magic x) (Obj.magic y))
             | W32  ->
                 Obj.repr
                   (FStar_UInt32.sub_underspec (Obj.magic x) (Obj.magic y))
             | W63  ->
                 Obj.repr
                   (FStar_UInt63.sub_underspec (Obj.magic x) (Obj.magic y))
             | W64  ->
                 Obj.repr
                   (FStar_UInt64.sub_underspec (Obj.magic x) (Obj.magic y))
             | W128  ->
                 Obj.repr
                   (FStar_UInt128.sub_underspec (Obj.magic x) (Obj.magic y)))
  
let (op_Subtraction_Percent : signed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        let uu____466 = sw  in
        match uu____466 with
        | Unsigned w ->
            (match w with
             | W8  ->
                 Obj.repr (FStar_UInt8.sub_mod (Obj.magic x) (Obj.magic y))
             | W16  ->
                 Obj.repr (FStar_UInt16.sub_mod (Obj.magic x) (Obj.magic y))
             | W31  ->
                 Obj.repr (FStar_UInt31.sub_mod (Obj.magic x) (Obj.magic y))
             | W32  ->
                 Obj.repr (FStar_UInt32.sub_mod (Obj.magic x) (Obj.magic y))
             | W63  ->
                 Obj.repr (FStar_UInt63.sub_mod (Obj.magic x) (Obj.magic y))
             | W64  ->
                 Obj.repr (FStar_UInt64.sub_mod (Obj.magic x) (Obj.magic y))
             | W128  ->
                 Obj.repr (FStar_UInt128.sub_mod (Obj.magic x) (Obj.magic y)))
  
let (op_Minus : signed_width -> Obj.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      let uu____483 = sw  in
      match uu____483 with
      | Signed w ->
          (match w with
           | Winfinite  ->
               Obj.repr (op_Subtraction sw (Obj.magic Prims.int_zero) x)
           | W8  ->
               Obj.repr
                 (FStar_Int8.sub (FStar_Int8.int_to_t Prims.int_zero)
                    (Obj.magic x))
           | W16  ->
               Obj.repr
                 (FStar_Int16.sub (FStar_Int16.int_to_t Prims.int_zero)
                    (Obj.magic x))
           | W31  ->
               Obj.repr
                 (FStar_Int31.sub (FStar_Int31.int_to_t Prims.int_zero)
                    (Obj.magic x))
           | W32  ->
               Obj.repr
                 (FStar_Int32.sub (FStar_Int32.int_to_t Prims.int_zero)
                    (Obj.magic x))
           | W63  ->
               Obj.repr
                 (FStar_Int63.sub (FStar_Int63.int_to_t Prims.int_zero)
                    (Obj.magic x))
           | W64  ->
               Obj.repr
                 (FStar_Int64.sub (FStar_Int64.int_to_t Prims.int_zero)
                    (Obj.magic x))
           | W128  ->
               Obj.repr
                 (FStar_Int128.sub (FStar_Int128.int_to_t Prims.int_zero)
                    (Obj.magic x)))
  
let (op_Star : signed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Signed (Winfinite ) -> Obj.repr ((Obj.magic x) * (Obj.magic y))
        | Unsigned (W8 ) ->
            Obj.repr (FStar_UInt8.mul (Obj.magic x) (Obj.magic y))
        | Unsigned (W16 ) ->
            Obj.repr (FStar_UInt16.mul (Obj.magic x) (Obj.magic y))
        | Unsigned (W31 ) ->
            Obj.repr (FStar_UInt31.mul (Obj.magic x) (Obj.magic y))
        | Unsigned (W32 ) ->
            Obj.repr (FStar_UInt32.mul (Obj.magic x) (Obj.magic y))
        | Unsigned (W63 ) ->
            Obj.repr (FStar_UInt63.mul (Obj.magic x) (Obj.magic y))
        | Unsigned (W64 ) ->
            Obj.repr (FStar_UInt64.mul (Obj.magic x) (Obj.magic y))
        | Signed (W8 ) ->
            Obj.repr (FStar_Int8.mul (Obj.magic x) (Obj.magic y))
        | Signed (W16 ) ->
            Obj.repr (FStar_Int16.mul (Obj.magic x) (Obj.magic y))
        | Signed (W31 ) ->
            Obj.repr (FStar_Int31.mul (Obj.magic x) (Obj.magic y))
        | Signed (W32 ) ->
            Obj.repr (FStar_Int32.mul (Obj.magic x) (Obj.magic y))
        | Signed (W63 ) ->
            Obj.repr (FStar_Int63.mul (Obj.magic x) (Obj.magic y))
        | Signed (W64 ) ->
            Obj.repr (FStar_Int64.mul (Obj.magic x) (Obj.magic y))
        | Signed (W128 ) ->
            Obj.repr (FStar_Int128.mul (Obj.magic x) (Obj.magic y))
  
let (op_Star_Question : signed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        let uu____533 = sw  in
        match uu____533 with
        | Unsigned w ->
            (match w with
             | W8  ->
                 Obj.repr
                   (FStar_UInt8.mul_underspec (Obj.magic x) (Obj.magic y))
             | W16  ->
                 Obj.repr
                   (FStar_UInt16.mul_underspec (Obj.magic x) (Obj.magic y))
             | W31  ->
                 Obj.repr
                   (FStar_UInt31.mul_underspec (Obj.magic x) (Obj.magic y))
             | W32  ->
                 Obj.repr
                   (FStar_UInt32.mul_underspec (Obj.magic x) (Obj.magic y))
             | W63  ->
                 Obj.repr
                   (FStar_UInt63.mul_underspec (Obj.magic x) (Obj.magic y))
             | W64  ->
                 Obj.repr
                   (FStar_UInt64.mul_underspec (Obj.magic x) (Obj.magic y)))
  
let (op_Star_Percent : signed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        let uu____556 = sw  in
        match uu____556 with
        | Unsigned w ->
            (match w with
             | W8  ->
                 Obj.repr (FStar_UInt8.mul_mod (Obj.magic x) (Obj.magic y))
             | W16  ->
                 Obj.repr (FStar_UInt16.mul_mod (Obj.magic x) (Obj.magic y))
             | W31  ->
                 Obj.repr (FStar_UInt31.mul_mod (Obj.magic x) (Obj.magic y))
             | W32  ->
                 Obj.repr (FStar_UInt32.mul_mod (Obj.magic x) (Obj.magic y))
             | W63  ->
                 Obj.repr (FStar_UInt63.mul_mod (Obj.magic x) (Obj.magic y))
             | W64  ->
                 Obj.repr (FStar_UInt64.mul_mod (Obj.magic x) (Obj.magic y)))
  
let (op_Greater : signed_width -> Obj.t -> Obj.t -> Prims.bool) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Signed (Winfinite ) -> (Obj.magic x) > (Obj.magic y)
        | Unsigned (W8 ) -> FStar_UInt8.gt (Obj.magic x) (Obj.magic y)
        | Unsigned (W16 ) -> FStar_UInt16.gt (Obj.magic x) (Obj.magic y)
        | Unsigned (W31 ) -> FStar_UInt31.gt (Obj.magic x) (Obj.magic y)
        | Unsigned (W32 ) -> FStar_UInt32.gt (Obj.magic x) (Obj.magic y)
        | Unsigned (W63 ) -> FStar_UInt63.gt (Obj.magic x) (Obj.magic y)
        | Unsigned (W64 ) -> FStar_UInt64.gt (Obj.magic x) (Obj.magic y)
        | Unsigned (W128 ) -> FStar_UInt128.gt (Obj.magic x) (Obj.magic y)
        | Signed (W8 ) -> FStar_Int8.gt (Obj.magic x) (Obj.magic y)
        | Signed (W16 ) -> FStar_Int16.gt (Obj.magic x) (Obj.magic y)
        | Signed (W31 ) -> FStar_Int31.gt (Obj.magic x) (Obj.magic y)
        | Signed (W32 ) -> FStar_Int32.gt (Obj.magic x) (Obj.magic y)
        | Signed (W63 ) -> FStar_Int63.gt (Obj.magic x) (Obj.magic y)
        | Signed (W64 ) -> FStar_Int64.gt (Obj.magic x) (Obj.magic y)
        | Signed (W128 ) -> FStar_Int128.gt (Obj.magic x) (Obj.magic y)
  
let (op_Greater_Equals : signed_width -> Obj.t -> Obj.t -> Prims.bool) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Signed (Winfinite ) -> (Obj.magic x) >= (Obj.magic y)
        | Unsigned (W8 ) -> FStar_UInt8.gte (Obj.magic x) (Obj.magic y)
        | Unsigned (W16 ) -> FStar_UInt16.gte (Obj.magic x) (Obj.magic y)
        | Unsigned (W31 ) -> FStar_UInt31.gte (Obj.magic x) (Obj.magic y)
        | Unsigned (W32 ) -> FStar_UInt32.gte (Obj.magic x) (Obj.magic y)
        | Unsigned (W63 ) -> FStar_UInt63.gte (Obj.magic x) (Obj.magic y)
        | Unsigned (W64 ) -> FStar_UInt64.gte (Obj.magic x) (Obj.magic y)
        | Unsigned (W128 ) -> FStar_UInt128.gte (Obj.magic x) (Obj.magic y)
        | Signed (W8 ) -> FStar_Int8.gte (Obj.magic x) (Obj.magic y)
        | Signed (W16 ) -> FStar_Int16.gte (Obj.magic x) (Obj.magic y)
        | Signed (W31 ) -> FStar_Int31.gte (Obj.magic x) (Obj.magic y)
        | Signed (W32 ) -> FStar_Int32.gte (Obj.magic x) (Obj.magic y)
        | Signed (W63 ) -> FStar_Int63.gte (Obj.magic x) (Obj.magic y)
        | Signed (W64 ) -> FStar_Int64.gte (Obj.magic x) (Obj.magic y)
        | Signed (W128 ) -> FStar_Int128.gte (Obj.magic x) (Obj.magic y)
  
let (op_Less : signed_width -> Obj.t -> Obj.t -> Prims.bool) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Signed (Winfinite ) -> (Obj.magic x) < (Obj.magic y)
        | Unsigned (W8 ) -> FStar_UInt8.lt (Obj.magic x) (Obj.magic y)
        | Unsigned (W16 ) -> FStar_UInt16.lt (Obj.magic x) (Obj.magic y)
        | Unsigned (W31 ) -> FStar_UInt31.lt (Obj.magic x) (Obj.magic y)
        | Unsigned (W32 ) -> FStar_UInt32.lt (Obj.magic x) (Obj.magic y)
        | Unsigned (W63 ) -> FStar_UInt63.lt (Obj.magic x) (Obj.magic y)
        | Unsigned (W64 ) -> FStar_UInt64.lt (Obj.magic x) (Obj.magic y)
        | Unsigned (W128 ) -> FStar_UInt128.lt (Obj.magic x) (Obj.magic y)
        | Signed (W8 ) -> FStar_Int8.lt (Obj.magic x) (Obj.magic y)
        | Signed (W16 ) -> FStar_Int16.lt (Obj.magic x) (Obj.magic y)
        | Signed (W31 ) -> FStar_Int31.lt (Obj.magic x) (Obj.magic y)
        | Signed (W32 ) -> FStar_Int32.lt (Obj.magic x) (Obj.magic y)
        | Signed (W63 ) -> FStar_Int63.lt (Obj.magic x) (Obj.magic y)
        | Signed (W64 ) -> FStar_Int64.lt (Obj.magic x) (Obj.magic y)
        | Signed (W128 ) -> FStar_Int128.lt (Obj.magic x) (Obj.magic y)
  
let (op_Less_Equals : signed_width -> Obj.t -> Obj.t -> Prims.bool) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Signed (Winfinite ) -> (Obj.magic x) <= (Obj.magic y)
        | Unsigned (W8 ) -> FStar_UInt8.lte (Obj.magic x) (Obj.magic y)
        | Unsigned (W16 ) -> FStar_UInt16.lte (Obj.magic x) (Obj.magic y)
        | Unsigned (W31 ) -> FStar_UInt31.lte (Obj.magic x) (Obj.magic y)
        | Unsigned (W32 ) -> FStar_UInt32.lte (Obj.magic x) (Obj.magic y)
        | Unsigned (W63 ) -> FStar_UInt63.lte (Obj.magic x) (Obj.magic y)
        | Unsigned (W64 ) -> FStar_UInt64.lte (Obj.magic x) (Obj.magic y)
        | Unsigned (W128 ) -> FStar_UInt128.lte (Obj.magic x) (Obj.magic y)
        | Signed (W8 ) -> FStar_Int8.lte (Obj.magic x) (Obj.magic y)
        | Signed (W16 ) -> FStar_Int16.lte (Obj.magic x) (Obj.magic y)
        | Signed (W31 ) -> FStar_Int31.lte (Obj.magic x) (Obj.magic y)
        | Signed (W32 ) -> FStar_Int32.lte (Obj.magic x) (Obj.magic y)
        | Signed (W63 ) -> FStar_Int63.lte (Obj.magic x) (Obj.magic y)
        | Signed (W64 ) -> FStar_Int64.lte (Obj.magic x) (Obj.magic y)
        | Signed (W128 ) -> FStar_Int128.lte (Obj.magic x) (Obj.magic y)
  
let (op_Slash : signed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Signed (Winfinite ) -> Obj.repr ((Obj.magic x) / (Obj.magic y))
        | Unsigned (W8 ) ->
            Obj.repr (FStar_UInt8.div (Obj.magic x) (Obj.magic y))
        | Unsigned (W16 ) ->
            Obj.repr (FStar_UInt16.div (Obj.magic x) (Obj.magic y))
        | Unsigned (W31 ) ->
            Obj.repr (FStar_UInt31.div (Obj.magic x) (Obj.magic y))
        | Unsigned (W32 ) ->
            Obj.repr (FStar_UInt32.div (Obj.magic x) (Obj.magic y))
        | Unsigned (W63 ) ->
            Obj.repr (FStar_UInt63.div (Obj.magic x) (Obj.magic y))
        | Unsigned (W64 ) ->
            Obj.repr (FStar_UInt64.div (Obj.magic x) (Obj.magic y))
        | Signed (W8 ) ->
            Obj.repr (FStar_Int8.div (Obj.magic x) (Obj.magic y))
        | Signed (W16 ) ->
            Obj.repr (FStar_Int16.div (Obj.magic x) (Obj.magic y))
        | Signed (W31 ) ->
            Obj.repr (FStar_Int31.div (Obj.magic x) (Obj.magic y))
        | Signed (W32 ) ->
            Obj.repr (FStar_Int32.div (Obj.magic x) (Obj.magic y))
        | Signed (W63 ) ->
            Obj.repr (FStar_Int63.div (Obj.magic x) (Obj.magic y))
        | Signed (W64 ) ->
            Obj.repr (FStar_Int64.div (Obj.magic x) (Obj.magic y))
        | Signed (W128 ) ->
            Obj.repr (FStar_Int128.div (Obj.magic x) (Obj.magic y))
  
let (op_Percent : signed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Signed (Winfinite ) -> Obj.repr ((Obj.magic x) mod (Obj.magic y))
        | Unsigned (W8 ) ->
            Obj.repr (FStar_UInt8.rem (Obj.magic x) (Obj.magic y))
        | Unsigned (W16 ) ->
            Obj.repr (FStar_UInt16.rem (Obj.magic x) (Obj.magic y))
        | Unsigned (W31 ) ->
            Obj.repr (FStar_UInt31.rem (Obj.magic x) (Obj.magic y))
        | Unsigned (W32 ) ->
            Obj.repr (FStar_UInt32.rem (Obj.magic x) (Obj.magic y))
        | Unsigned (W63 ) ->
            Obj.repr (FStar_UInt63.rem (Obj.magic x) (Obj.magic y))
        | Unsigned (W64 ) ->
            Obj.repr (FStar_UInt64.rem (Obj.magic x) (Obj.magic y))
        | Signed (W8 ) ->
            Obj.repr (FStar_Int8.rem (Obj.magic x) (Obj.magic y))
        | Signed (W16 ) ->
            Obj.repr (FStar_Int16.rem (Obj.magic x) (Obj.magic y))
        | Signed (W31 ) ->
            Obj.repr (FStar_Int31.rem (Obj.magic x) (Obj.magic y))
        | Signed (W32 ) ->
            Obj.repr (FStar_Int32.rem (Obj.magic x) (Obj.magic y))
        | Signed (W63 ) ->
            Obj.repr (FStar_Int63.rem (Obj.magic x) (Obj.magic y))
        | Signed (W64 ) ->
            Obj.repr (FStar_Int64.rem (Obj.magic x) (Obj.magic y))
        | Signed (W128 ) ->
            Obj.repr (FStar_Int128.rem (Obj.magic x) (Obj.magic y))
  
let (op_Hat_Hat : signed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Unsigned (W8 ) ->
            Obj.repr (FStar_UInt8.logxor (Obj.magic x) (Obj.magic y))
        | Unsigned (W16 ) ->
            Obj.repr (FStar_UInt16.logxor (Obj.magic x) (Obj.magic y))
        | Unsigned (W31 ) ->
            Obj.repr (FStar_UInt31.logxor (Obj.magic x) (Obj.magic y))
        | Unsigned (W32 ) ->
            Obj.repr (FStar_UInt32.logxor (Obj.magic x) (Obj.magic y))
        | Unsigned (W63 ) ->
            Obj.repr (FStar_UInt63.logxor (Obj.magic x) (Obj.magic y))
        | Unsigned (W64 ) ->
            Obj.repr (FStar_UInt64.logxor (Obj.magic x) (Obj.magic y))
        | Unsigned (W128 ) ->
            Obj.repr (FStar_UInt128.logxor (Obj.magic x) (Obj.magic y))
        | Signed (W8 ) ->
            Obj.repr (FStar_Int8.logxor (Obj.magic x) (Obj.magic y))
        | Signed (W16 ) ->
            Obj.repr (FStar_Int16.logxor (Obj.magic x) (Obj.magic y))
        | Signed (W31 ) ->
            Obj.repr (FStar_Int31.logxor (Obj.magic x) (Obj.magic y))
        | Signed (W32 ) ->
            Obj.repr (FStar_Int32.logxor (Obj.magic x) (Obj.magic y))
        | Signed (W63 ) ->
            Obj.repr (FStar_Int63.logxor (Obj.magic x) (Obj.magic y))
        | Signed (W64 ) ->
            Obj.repr (FStar_Int64.logxor (Obj.magic x) (Obj.magic y))
        | Signed (W128 ) ->
            Obj.repr (FStar_Int128.logxor (Obj.magic x) (Obj.magic y))
  
let (op_Amp_Hat : signed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Unsigned (W8 ) ->
            Obj.repr (FStar_UInt8.logand (Obj.magic x) (Obj.magic y))
        | Unsigned (W16 ) ->
            Obj.repr (FStar_UInt16.logand (Obj.magic x) (Obj.magic y))
        | Unsigned (W31 ) ->
            Obj.repr (FStar_UInt31.logand (Obj.magic x) (Obj.magic y))
        | Unsigned (W32 ) ->
            Obj.repr (FStar_UInt32.logand (Obj.magic x) (Obj.magic y))
        | Unsigned (W63 ) ->
            Obj.repr (FStar_UInt63.logand (Obj.magic x) (Obj.magic y))
        | Unsigned (W64 ) ->
            Obj.repr (FStar_UInt64.logand (Obj.magic x) (Obj.magic y))
        | Unsigned (W128 ) ->
            Obj.repr (FStar_UInt128.logand (Obj.magic x) (Obj.magic y))
        | Signed (W8 ) ->
            Obj.repr (FStar_Int8.logand (Obj.magic x) (Obj.magic y))
        | Signed (W16 ) ->
            Obj.repr (FStar_Int16.logand (Obj.magic x) (Obj.magic y))
        | Signed (W31 ) ->
            Obj.repr (FStar_Int31.logand (Obj.magic x) (Obj.magic y))
        | Signed (W32 ) ->
            Obj.repr (FStar_Int32.logand (Obj.magic x) (Obj.magic y))
        | Signed (W63 ) ->
            Obj.repr (FStar_Int63.logand (Obj.magic x) (Obj.magic y))
        | Signed (W64 ) ->
            Obj.repr (FStar_Int64.logand (Obj.magic x) (Obj.magic y))
        | Signed (W128 ) ->
            Obj.repr (FStar_Int128.logand (Obj.magic x) (Obj.magic y))
  
let (op_Bar_Hat : signed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Unsigned (W8 ) ->
            Obj.repr (FStar_UInt8.logor (Obj.magic x) (Obj.magic y))
        | Unsigned (W16 ) ->
            Obj.repr (FStar_UInt16.logor (Obj.magic x) (Obj.magic y))
        | Unsigned (W31 ) ->
            Obj.repr (FStar_UInt31.logor (Obj.magic x) (Obj.magic y))
        | Unsigned (W32 ) ->
            Obj.repr (FStar_UInt32.logor (Obj.magic x) (Obj.magic y))
        | Unsigned (W63 ) ->
            Obj.repr (FStar_UInt63.logor (Obj.magic x) (Obj.magic y))
        | Unsigned (W64 ) ->
            Obj.repr (FStar_UInt64.logor (Obj.magic x) (Obj.magic y))
        | Unsigned (W128 ) ->
            Obj.repr (FStar_UInt128.logor (Obj.magic x) (Obj.magic y))
        | Signed (W8 ) ->
            Obj.repr (FStar_Int8.logor (Obj.magic x) (Obj.magic y))
        | Signed (W16 ) ->
            Obj.repr (FStar_Int16.logor (Obj.magic x) (Obj.magic y))
        | Signed (W31 ) ->
            Obj.repr (FStar_Int31.logor (Obj.magic x) (Obj.magic y))
        | Signed (W32 ) ->
            Obj.repr (FStar_Int32.logor (Obj.magic x) (Obj.magic y))
        | Signed (W63 ) ->
            Obj.repr (FStar_Int63.logor (Obj.magic x) (Obj.magic y))
        | Signed (W64 ) ->
            Obj.repr (FStar_Int64.logor (Obj.magic x) (Obj.magic y))
        | Signed (W128 ) ->
            Obj.repr (FStar_Int128.logor (Obj.magic x) (Obj.magic y))
  
let (op_Less_Less_Hat : signed_width -> Obj.t -> FStar_UInt32.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Unsigned (W8 ) -> Obj.repr (FStar_UInt8.shift_left (Obj.magic x) y)
        | Unsigned (W16 ) ->
            Obj.repr (FStar_UInt16.shift_left (Obj.magic x) y)
        | Unsigned (W31 ) ->
            Obj.repr (FStar_UInt31.shift_left (Obj.magic x) y)
        | Unsigned (W32 ) ->
            Obj.repr (FStar_UInt32.shift_left (Obj.magic x) y)
        | Unsigned (W63 ) ->
            Obj.repr (FStar_UInt63.shift_left (Obj.magic x) y)
        | Unsigned (W64 ) ->
            Obj.repr (FStar_UInt64.shift_left (Obj.magic x) y)
        | Unsigned (W128 ) ->
            Obj.repr (FStar_UInt128.shift_left (Obj.magic x) y)
        | Signed (W8 ) -> Obj.repr (FStar_Int8.shift_left (Obj.magic x) y)
        | Signed (W16 ) -> Obj.repr (FStar_Int16.shift_left (Obj.magic x) y)
        | Signed (W31 ) -> Obj.repr (FStar_Int31.shift_left (Obj.magic x) y)
        | Signed (W32 ) -> Obj.repr (FStar_Int32.shift_left (Obj.magic x) y)
        | Signed (W63 ) -> Obj.repr (FStar_Int63.shift_left (Obj.magic x) y)
        | Signed (W64 ) -> Obj.repr (FStar_Int64.shift_left (Obj.magic x) y)
        | Signed (W128 ) ->
            Obj.repr (FStar_Int128.shift_left (Obj.magic x) y)
  
let (op_Greater_Greater_Hat :
  signed_width -> Obj.t -> FStar_UInt32.t -> Obj.t) =
  fun sw  ->
    fun x  ->
      fun y  ->
        match sw with
        | Unsigned (W8 ) ->
            Obj.repr (FStar_UInt8.shift_right (Obj.magic x) y)
        | Unsigned (W16 ) ->
            Obj.repr (FStar_UInt16.shift_right (Obj.magic x) y)
        | Unsigned (W31 ) ->
            Obj.repr (FStar_UInt31.shift_right (Obj.magic x) y)
        | Unsigned (W32 ) ->
            Obj.repr (FStar_UInt32.shift_right (Obj.magic x) y)
        | Unsigned (W63 ) ->
            Obj.repr (FStar_UInt63.shift_right (Obj.magic x) y)
        | Unsigned (W64 ) ->
            Obj.repr (FStar_UInt64.shift_right (Obj.magic x) y)
        | Unsigned (W128 ) ->
            Obj.repr (FStar_UInt128.shift_right (Obj.magic x) y)
        | Signed (W8 ) -> Obj.repr (FStar_Int8.shift_right (Obj.magic x) y)
        | Signed (W16 ) -> Obj.repr (FStar_Int16.shift_right (Obj.magic x) y)
        | Signed (W31 ) -> Obj.repr (FStar_Int31.shift_right (Obj.magic x) y)
        | Signed (W32 ) -> Obj.repr (FStar_Int32.shift_right (Obj.magic x) y)
        | Signed (W63 ) -> Obj.repr (FStar_Int63.shift_right (Obj.magic x) y)
        | Signed (W64 ) -> Obj.repr (FStar_Int64.shift_right (Obj.magic x) y)
        | Signed (W128 ) ->
            Obj.repr (FStar_Int128.shift_right (Obj.magic x) y)
  
type uint_8 = FStar_UInt8.t
type uint_16 = FStar_UInt16.t
type uint_31 = FStar_UInt31.t
type uint_32 = FStar_UInt32.t
type uint_63 = FStar_UInt63.t
type uint_64 = FStar_UInt64.t
type int = Prims.int
type int_8 = FStar_Int8.t
type int_16 = FStar_Int16.t
type int_31 = FStar_Int31.t
type int_32 = FStar_Int32.t
type int_63 = FStar_Int63.t
type int_64 = FStar_Int64.t
type int_128 = FStar_Int128.t
type ('Asw,'Aop,'Ax,'Ay) ok = Obj.t
type nat = Prims.int
type pos = Prims.int
let (f_int : Prims.int -> Prims.int -> Prims.int) = fun x  -> fun y  -> x + y 
let (f_nat : Prims.int -> Prims.int -> Prims.int) = fun x  -> fun y  -> x + y 
let (f_nat_int_pos : Prims.int -> Prims.int -> Prims.int -> Prims.int) =
  fun x  -> fun y  -> fun z  -> (x + y) + z 
let (f_uint_8 : FStar_UInt8.t -> FStar_UInt8.t -> FStar_UInt8.t) =
  fun x  -> fun y  -> FStar_UInt8.add x y 
let (f_int_16 : FStar_Int16.t -> FStar_Int16.t -> FStar_Int16.t) =
  fun x  -> fun y  -> FStar_Int16.add x y 
let (g : FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t) =
  fun x  -> fun y  -> FStar_UInt32.add x (FStar_UInt32.mul y y) 
let (h : Prims.nat -> Prims.nat -> Prims.int) = fun x  -> fun y  -> x + y 
let (i : Prims.nat -> Prims.nat -> Prims.int) = fun x  -> fun y  -> x + y 
let (j : Prims.int -> Prims.nat -> Prims.int) = fun x  -> fun y  -> x - y 
let (k : Prims.int -> Prims.int -> Prims.int) = fun x  -> fun y  -> x * y 