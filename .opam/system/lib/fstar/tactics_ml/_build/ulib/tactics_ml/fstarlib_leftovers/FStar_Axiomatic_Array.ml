open Prims
type 'Auu____4 seq = unit
let index : 'Aa . 'Aa seq -> Prims.int -> 'Aa =
  fun uu____32  -> fun uu____33  -> failwith "Not yet implemented:index" 
let update : 'Aa . 'Aa seq -> Prims.int -> 'Aa -> 'Aa seq =
  fun uu____77  ->
    fun uu____78  -> fun uu____79  -> failwith "Not yet implemented:update"
  
let emp : 'Aa . unit -> 'Aa seq =
  fun uu____95  -> failwith "Not yet implemented:emp" 
let create : 'Aa . Prims.int -> 'Aa -> 'Aa seq =
  fun uu____127  -> fun uu____128  -> failwith "Not yet implemented:create" 
let length : 'Aa . 'Aa seq -> Prims.nat =
  fun uu____151  -> failwith "Not yet implemented:length" 
let slice : 'Aa . 'Aa seq -> Prims.int -> Prims.int -> 'Aa seq =
  fun uu____195  ->
    fun uu____196  -> fun uu____197  -> failwith "Not yet implemented:slice"
  
let append : 'Aa . 'Aa seq -> 'Aa seq -> 'Aa seq =
  fun uu____236  -> fun uu____237  -> failwith "Not yet implemented:append" 
let proj_some : 'Aa . 'Aa FStar_Pervasives_Native.option seq -> 'Aa seq =
  fun uu____267  -> failwith "Not yet implemented:proj_some" 
type ('Aa,'Auu____289,'Auu____290) equal = unit
type 'Aa array = 'Aa seq FStar_Heap.ref
type ('Aa,'As) is_Some_All = unit