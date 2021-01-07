open Util
open Io
open Sym

type 'a term = Node of 'a * 'a term list

type ('a,'b) wterm = WT of 'a * ('a,'b) wterm list * 'b

let root (Node(f,_)) = f
let get_weight (WT(_,_,ws)) = ws
let rec erase (WT(f,ss,_)) = Node(f,List.map erase ss)

let size : 'a term -> int =
  let rec sub1 ret (Node(_,ss)) = sub2 (ret+1) ss
  and sub2 ret ss =
    match ss with
    | [] -> ret
    | s::ss -> sub2 (sub1 ret s) ss
  in
  sub1 0

let var vname = Node((new sym_unmarked Var vname :> sym), [])
let app f args = Node((f:>sym), args)

let rename r (Node(f,ss)) = Node(r f, ss)

let subst a (Node(f,ss)) =
  let Node(g,ts) = a f in
  Node(g,ts@ss)

(* equality *)
let rec term_eq (Node((f:#sym),ss)) (Node(g,ts)) =
  f#equals g && List.for_all2 term_eq ss ts

let rec wterm_eq (WT((f:#sym),ss,sw)) (WT(g,ts,tw)) =
  f#equals g && List.for_all2 wterm_eq ss ts

let rec ac_eq (WT((f:#sym),ss,sw)) (WT(g,ts,tw)) =
  f#equals g &&
  if f#is_commutative then eq_mset ss ts
  else List.for_all2 ac_eq ss ts
and delete_one ts1 s =
  function
  | [] -> None
  | t::ts -> if ac_eq s t then Some(ts1@ts) else delete_one (t::ts1) s ts
and eq_mset ss ts =
  match ss with
  | [] -> ts = []
  | s::ss' ->
    match delete_one [] s ts with
    | None -> false
    | Some ts' -> eq_mset ss' ts'

(* subterm relation *)
let rec strict_subterm (s:#sym term) (Node(_,ts)) =
  List.exists (subterm s) ts
and subterm (s:#sym term) t = term_eq s t || strict_subterm s t

(* embeding relation *)
let rec emb_le (Node((f:#sym),ss) as s) (Node(g,ts) as t) =
  term_eq s t || List.exists (emb_le s) ts || f#equals g && List.for_all2 emb_le ss ts

(* the list of variable occurences in a term *)
let varlist =
  let rec sub (Node((f:#sym),ss)) =
    if f#is_var then f :: sublist ss else sublist ss
  and sublist =
    function
    | []  -> []
    | s::ss -> sub s @ sublist ss
  in
  sub

let dupvarlist =
  let rec sub ret (Node((f:#sym),ts)) =
    if f#is_var then
      let lvars, dupvars = ret in
      try (list_remove f#equals lvars, dupvars)
      with Not_found -> (lvars, f::dupvars)
    else sublist ret ts
  and sublist ret =
    function
    | []  -> ret
    | t::ts -> sublist (sub ret t) ts
  in
  fun l r ->
    let lvars, dupvars = sub (varlist l, []) r in
    dupvars

let duplicating l r = dupvarlist l r <> []

(* the set of variables in a term *)
module VarSet = Set.Make(String)
let varset =
  let rec sub (Node((f:#sym),ts)) =
    if f#is_var then VarSet.add f#name (sublist ts) else sublist ts
  and sublist =
    function
    | []  -> VarSet.empty
    | t::ts -> VarSet.union (sub t) (sublist ts)
  in
  sub

(* flat AC symbols *)
let rec flat =
  let rec sub (f:#sym) ss =
    function
    | [] -> Node(f, List.rev ss)
    | (Node(g,ts) as t)::us ->
      if f#equals g then
        sub f ss (ts@us)
      else
        sub f (flat t :: ss) us
  in
  fun (Node(f,ss)) ->
    match f#ty with
    | Th "AC" -> sub f [] ss
    | _     -> Node(f, List.map flat ss)

(* flat top $f$ from list of functions *)
let local_flat (f:#sym) =
  let rec sub ss =
    function
    | [] -> ss
    | (Node(g,ts) as t)::us ->
      if f#equals g then sub ss (ts @ us) else sub (ss@[t]) us
  in
  sub []

(* unflat *)
let fold f =
  let rec sub ret =
    function
    | [] -> ret
    | s::ss -> sub (Node(f,[ret;s])) ss
  in
  function
  | [] -> failwith "bug"
  | s::ss -> sub s ss

(* top-AC subterms, for KT98 *)
let top_ac_subterms (Node(f,ss) as s) =
  if f#ty = Th "AC" then
    let args = local_flat f ss in
    let subargs = subsequences args in
    List.map (fold f) (List.filter (fun ts -> List.length ts > 1) subargs)
  else [s]

(* printers *)
let rec output_term (pr : #Io.outputter) : (#sym as 'a) term -> unit =
  let rec sub =
    function
    | []  -> pr#putc ')'
    | t::ts -> pr#putc ','; output_term pr t; sub ts
  in
  fun (Node(f,ts)) ->
    f#output pr;
    match ts with
    | []  -> if f#is_fun then pr#puts "()";
    | t::ts -> pr#putc '('; output_term pr t; sub ts

let put_term s pr = output_term pr s

let prerr_term t = output_term Io.cerr t
let prerr_terms ts = List.iter (fun t -> prerr_term t; prerr_string "  ") ts
let prerr_wterm wt = prerr_term (erase wt)
let prerr_wterms wts = List.iter (fun wt -> prerr_wterm wt; prerr_string " ") wts

(* xml printers *)
let rec output_xml_term (pr : #Io.outputter) : (#sym as 'a) term -> unit =
  let rec sub =
    function
    | []  -> MyXML.leave "arg" pr; MyXML.leave "funapp" pr;
    | t::ts -> MyXML.leave "arg" pr; MyXML.enter "arg" pr; output_xml_term pr t; sub ts
  in
  fun (Node(f,ts)) ->
    if f#is_var then begin
      f#output_xml pr;
    end else begin
      MyXML.enter "funapp" pr;
      f#output_xml pr;
      match ts with
      | []  -> if f#is_fun then MyXML.leave "funapp" pr;
      | t::ts -> MyXML.enter "arg" pr; output_xml_term pr t; sub ts
    end

(*** rules ***)
type strength = StrictRule | MediumRule | WeakRule

class rule s (l : sym term) (r : sym term) =
  object (x)
    inherit Io.output
    val strength = s
    method l = l
    method r = r
    method strength = strength
    method size = size l + size r
    method is_strict = strength = StrictRule
    method is_medium = strength = MediumRule
    method is_weak = strength = WeakRule
    method is_duplicating = duplicating l r
    method is_size_increasing = size l < size r || x#is_duplicating
    method has_extra_variable =
      let lvars = varlist l in
      let rvars = varlist r in
      List.exists (fun rvar -> not (List.mem rvar lvars)) rvars

    method output : 'b. (#outputter as 'b) -> unit = fun pr ->
      output_term pr l;
      pr#puts (
        match s with
        | StrictRule -> " -> "
        | WeakRule -> " ->= "
        | _ -> " ->? ");
      output_term pr r
    method output_xml : 'b. (#printer as 'b) -> unit =
      MyXML.enclose "rule" (
        MyXML.enclose "lhs" (fun pr -> output_xml_term pr l) <<
        MyXML.enclose "rhs" (fun pr -> output_xml_term pr r)
      )
  end

let rule l r = new rule StrictRule l r
let weak_rule l r = new rule WeakRule l r
let medium_rule l r = new rule MediumRule l r

let map_rule : ((#sym as 'a) term -> 'a term) -> rule -> rule =
  fun f rule -> new rule rule#strength (f rule#l) (f rule#r)

let extended_rules =
  let x = Node((new sym_fresh Var 1 :> sym), []) in
  let y = Node((new sym_fresh Var 2 :> sym), []) in
  fun (rule:rule) ->
    let l = rule#l in
    let r = rule#r in
    let f = root l in
    match f#ty with
    | Th "AC" -> [ new rule rule#strength (app f [l; x]) (app f [r; x]) ]
    | Th "A" -> [
      new rule rule#strength (app f [l; x]) (app f [r; x]);
      new rule rule#strength (app f [x; l]) (app f [x; r]);
      new rule rule#strength (app f [app f [x; l]; y]) (app f [app f [x; r]; y])
    ]
    | Th "C" -> []
    | Th s -> raise (No_support ("extension for theory: " ^ s))
    | _ -> []



(* Probabilistic rewriting *)
class prule (l : sym term) (d : (int * sym term) list) =
  object (x)
    inherit Io.printable
    val sum = List.fold_left (fun ret p -> ret + fst p) 0 d
    method l = l
    method sum = sum
    method fold_rs : 'b. ('b -> int -> sym term -> 'b) -> 'b -> 'b =
      fun f i ->
        List.fold_left (fun ret p -> f ret (fst p) (snd p)) i d
    method iter_rs f =
      List.iter (function (n,r) -> f n r) d
    method print : 'b. (#printer as 'b) -> unit = fun pr ->
      output_term pr l;
      pr#enter 2;
      let iterer i r =
        pr#endl;
        pr#puts "-> ";
        pr#put_int i;
        pr#putc '/';
        pr#put_int sum;
        pr#puts ": ";
        output_term pr r;
      in
      x#iter_rs iterer;
      pr#leave 2;
    method output_xml : 'b. (#printer as 'b) -> unit =
      MyXML.enclose "rule" (
        MyXML.enclose "lhs" (fun pr -> output_xml_term pr l) <<
        MyXML.enclose "rhs" (fun pr ->
          let iterer i r = output_xml_term pr r in
          x#iter_rs iterer
        )
      )
  end
