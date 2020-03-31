(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.DM4F.Heap.IntStoreFixed

open FStar.Seq

let store_size = 10

abstract type id : eqtype = i:nat{i < store_size}
abstract type heap : eqtype = h:seq int{length h < store_size}

abstract let to_id (n:nat{n < store_size}) : id = n

abstract let index (h:heap) (i:id) : Tot int = index h i
let sel = index
abstract let upd (h:heap) (i:id) (x:int) : Tot heap = let h1 = upd h i x in assert (length h1 = store_size) ; h1

abstract let create (x:int) : Tot heap = create #int store_size x

abstract val lemma_index_upd1: s:heap -> n:id -> v:int -> Lemma
  (requires True)
  (ensures (index (upd s n v) n == v))
  [SMTPat (index (upd s n v) n)]
let lemma_index_upd1 s n v = lemma_index_upd1 #int s n v

abstract val lemma_index_upd2: s:heap -> n:id -> v:int -> i:id{i<>n} -> Lemma
  (requires True)
  (ensures (index (upd s n v) i == index s i))
  [SMTPat (index (upd s n v) i)]
let lemma_index_upd2 s n v i = lemma_index_upd2 #int s n v i


abstract val lemma_index_create: v:int -> i:id -> Lemma
  (requires True)
  (ensures (index (create v) i == v))
  [SMTPat (index (create v) i)]
let lemma_index_create v i = lemma_index_create #int store_size v i
