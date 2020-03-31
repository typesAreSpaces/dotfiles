open Prims
let comment_gen : 'At . Prims.string -> 'At -> Prims.string -> 'At =
  fun before  -> fun body  -> fun after  -> body 
let (comment : Prims.string -> unit) = fun s  -> () 