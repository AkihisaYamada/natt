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
exception Success
exception Unknown
exception Nonterm
exception Unsound of string
exception Internal of string

let rec intlist m n = if m > n then [] else m :: intlist (m+1) n

let iteri f =
	let rec sub n xs =
		match xs with
		| [] -> []
		| x::xs -> f n x; sub (n+1) xs
	in
	sub 0

let hd =
	function
	| [] -> raise (Internal "hd")
	| x::_ -> x
let tl =
	function 
	| [] -> raise (Internal "tl")
	| _::xs -> xs

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
		| []	-> zs
		| y::ys	-> sub1 (f x y::zs) x ys
	in
	let rec sub2 zs xs ys =
		match xs with
		| []	-> zs
		| x::xs	-> sub2 (sub1 zs x ys) xs ys
	in
	sub2 []
let list_product lists =
	List.fold_right (map_prod (fun x xs -> x::xs)) lists [[]]
