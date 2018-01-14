module Int =
  struct
    type t = int
    let compare = compare
    let hash = Hashtbl.hash
    let equal = (=)
  end

module IntSet = Set.Make(Int)

module StrSet = Set.Make(String)

module StrHashed =
  struct
    type t = string
    let compare = compare
    let hash = Hashtbl.hash
    let equal = (=)
  end

module LexList = functor (Elt : Map.OrderedType) ->
  struct
    type t = Elt.t list
    let rec compare xs ys =
      match (xs, ys) with
      | [], [] -> 0
      | _ , [] -> 1
      | [], _  -> -1
      | x::xs, y::ys ->
        match Elt.compare x y with
        | 0 -> compare xs ys
        | c -> c
  end

exception Success
exception Unknown
exception Nonterm
exception Unsound of string
exception Internal of string
exception No_support of string

let k_comb x _ = x

let rec int_list m n = if m > n then [] else m :: int_list (m+1) n

let int_array m n = Array.of_list (int_list m n)

let rec list_remove f =
  function
  | []  -> raise Not_found
  | x::xs -> if f x then xs else x :: list_remove f xs

(* string s begins with t *)
let begins s t =
  let n = String.length s in
  let m = String.length t in
  n >= m &&
  let rec sub i =
    i = m ||
    s.[i] = t.[i] &&
    sub (i+1)
  in
  sub 0

(* direct product of lists *)
let map_prod f =
  let rec sub1 zs x =
    function
    | []  -> zs
    | y::ys -> sub1 (f x y::zs) x ys
  in
  let rec sub2 zs xs ys =
    match xs with
    | []  -> zs
    | x::xs -> sub2 (sub1 zs x ys) xs ys
  in
  sub2 []
let list_product lists =
  List.fold_right (map_prod (fun x xs -> x::xs)) lists [[]]

(* length n sublists *)
let rec subsequences xs =
  match xs with
  | [] -> [[]]
  | x::xs -> let yss = subsequences xs in List.map (fun ys -> x::ys) yss @ yss

(* association list *)


class type output =
  object
    method output : out_channel -> unit
  end;;
class type output_xml =
  object
    inherit output
    method output_xml : out_channel -> unit
  end;;

