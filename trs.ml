open Util
open Sym
open Term
open Subst
open Io

type arity = Unknown | Arity of int

exception ExistsConditionalRule
exception ExistsEquation
exception UnknownTheory
exception UnknownStrategy
exception UnknownProperty
exception SymbolMissmatch;;

module Ths = StrSet
module Syms = StrSet
module Rules = IntSet

class sym_detailed (f : sym) =
  object (x:'a)
    inherit sym f#ty
    method name = f#name
    method output_xml = f#output_xml
    val mutable arity = if f#is_var then Arity 0 else Unknown
    val mutable defined_by = Rules.empty
    val mutable weakly_defined_by = Rules.empty
    val mutable p_defined_by = Rules.empty
    method original = f
    method arity_is_unknown = arity = Unknown
    method set_arity a = arity <- Arity a
    method arity =
      match arity with
      | Arity a -> a
      | _ -> raise (No_support ("arity for " ^ f#name ^ " is unknown"))
    method defined_by = defined_by
    method define_by i = defined_by <- Rules.add i defined_by
    method undefine_by i = defined_by <- Rules.remove i defined_by
    method is_defined = not (Rules.is_empty defined_by)
    method weakly_defined_by = weakly_defined_by
    method weakly_define_by i = weakly_defined_by <- Rules.add i weakly_defined_by
    method weakly_undefine_by i = weakly_defined_by <- Rules.remove i weakly_defined_by
    method is_weakly_defined = x#is_defined || not (Rules.is_empty weakly_defined_by)
    method p_defined_by = p_defined_by
    method p_define_by i = p_defined_by <- Rules.add i p_defined_by
    method p_undefine_by i = p_defined_by <- Rules.remove i p_defined_by
    method is_p_defined = not (Rules.is_empty p_defined_by)
    method is_const = not x#is_weakly_defined && not x#is_p_defined
  end;;

let print_tbl_index (pr : #Io.printer as 'a) prefix (i, (obj: #printable)) =
  pr#puts prefix;
  pr#put_int i;
  pr#puts ": ";
  obj#print pr;
  pr#endl;;

let print_tbl (pr : #Io.printer) prefix ruletbl =
  List.iter (print_tbl_index pr prefix)
  (List.sort (fun (i,_) (j,_) -> i - j) (Hashtbl.fold (fun i obj l -> (i,obj)::l) ruletbl []))

let hashtbl_exists test hashtbl =
  try
    Hashtbl.iter (fun l v -> if test l v then raise Success;) hashtbl;
    false
  with Success -> true

let hashtbl_for_all test hashtbl =
  try
    Hashtbl.iter (fun l v -> if not (test l v) then raise Success;) hashtbl;
    true
  with Success -> false

(* the class for TRSs *)
class trs =
  object (x)
    val sym_table = Hashtbl.create 64(* the symbol table *)
    val rule_table : (int, rule) Hashtbl.t = Hashtbl.create 256
    val prule_table : (int, prule) Hashtbl.t = Hashtbl.create 4
    val mutable fun_cnt = 0
    val mutable rule_cnt = 0
    val mutable strict_rule_cnt = 0
    val mutable prule_cnt = 0
    val mutable ths = Ths.empty(* the set of used built-in theories *)
(* information retrieval *)
    method get_fun_count = fun_cnt
    method get_size = rule_cnt + prule_cnt
    method get_size_strict = strict_rule_cnt + prule_cnt
    method get_ths = ths
    method is_theoried = not (Ths.is_empty ths)
    method is_probabilistic = prule_cnt > 0
(* methods for symbols *)
    method private add_sym : 'b. (#sym as 'b) -> sym_detailed =
      fun f ->
        let f' = new sym_detailed (f:>sym) in
        Hashtbl.add sym_table f#name f';
        if f#is_var then f'#set_arity 0 else fun_cnt <- fun_cnt + 1;
        f'
    method get_sym_name name =
      try Hashtbl.find sym_table name
      with Not_found -> x#add_sym (new sym_unmarked Fun name)
    method find_sym_name name =
      try Hashtbl.find sym_table name
      with Not_found -> new sym_detailed (new sym_unmarked Fun name)
    method get_sym : 'b. (#sym as 'b) -> sym_detailed =
      fun f ->
        if f#is_var then new sym_detailed (f:>sym) else
        try Hashtbl.find sym_table f#name with Not_found -> x#add_sym f
    method find_sym : 'b. (#sym as 'b) -> sym_detailed =
      fun f ->
        try Hashtbl.find sym_table f#name with Not_found -> new sym_detailed (f:>sym)
    method iter_syms : (sym_detailed -> unit) -> unit =
      fun iterer -> Hashtbl.iter (fun _ f -> iterer f) sym_table
    method iter_funs : (sym_detailed -> unit) -> unit =
      fun iterer -> Hashtbl.iter (fun _ f -> if f#is_fun then iterer f) sym_table
    method fold_syms : 'b. (sym_detailed -> 'b -> 'b) -> 'b -> 'b =
      fun folder acc ->
        Hashtbl.fold (fun _ -> folder) sym_table acc
    method strictly_defines_name name =
      try not (Rules.is_empty (Hashtbl.find sym_table name)#defined_by)
      with Not_found -> false
    method strictly_defines : 'b. (#sym as 'b) -> bool =
      fun f -> f#is_fun && x#strictly_defines_name f#name
    method defines : 'b. (#sym as 'b) -> bool =
      fun f ->
        f#is_fun &&
        try let f = Hashtbl.find sym_table f#name in
          f#is_defined || f#is_weakly_defined
        with Not_found -> false
    method weakly_defines : 'b. (#sym as 'b) -> bool =
      fun f ->
        f#is_fun &&
        try let f = Hashtbl.find sym_table f#name in
        f#is_weakly_defined
        with Not_found -> false
(* test for constructor terms *)
    method const_term : 'b. (#sym as 'b) term -> bool =
      fun (Node(f,ss)) ->
        not (x#defines f) && List.for_all x#const_term ss
    method relative_const : 'b. (#sym as 'b) term -> bool =
      fun (Node(f,ss)) ->
        not (x#strictly_defines f) && List.for_all x#relative_const ss

(* methods for rules *)
    method find_rule = Hashtbl.find rule_table
    method iter_rules f = Hashtbl.iter f rule_table
    method for_all_rules f = hashtbl_for_all f rule_table
    method exists_rule f = hashtbl_exists f rule_table
    method fold_rules : 'b. (int -> rule -> 'b -> 'b) -> 'b -> 'b =
      fun f a -> Hashtbl.fold f rule_table a
    method private add_rule_i i rule =
      let f = x#get_sym (root rule#l) in
      Hashtbl.add rule_table i rule;
      if rule#is_weak then begin
        f#weakly_define_by i;
      end else begin
        f#define_by i;
        strict_rule_cnt <- strict_rule_cnt + 1;
      end;
    method add_rule rule =
      rule_cnt <- rule_cnt + 1;
      x#add_rule_i rule_cnt rule;
    method remove_rule i =
      let rule = x#find_rule i in
      let f = x#get_sym (root rule#l) in
      if rule#is_weak then begin
        f#weakly_undefine_by i;
      end else begin
        f#undefine_by i;
        strict_rule_cnt <- strict_rule_cnt - 1;
      end;
      Hashtbl.remove rule_table i;
    method replace_rule i rule =
      x#remove_rule i;
      x#add_rule_i i rule;
    method modify_rule i l r =
      x#replace_rule i (new rule (x#find_rule i)#strength l r)

(* theory to rules *)
    method th_to_rules =
      let v1 = var "x" in
      let v2 = var "y" in
      let v3 = var "z" in
      let iterer (f:sym_detailed) =
        if f#is_associative then begin
          let l = app f [v1; app f [v2;v3]] in
          let r = app f [app f [v1;v2]; v3] in
          x#add_rule (weak_rule l r);
          if f#is_commutative then begin
            if Params.(params.naive_C) then begin
              x#add_rule (weak_rule (app f [v1;v2]) (app f [v2;v1]));
            end;
          end else begin
            x#add_rule (weak_rule r l);
          end;
        end else if Params.(params.naive_C) && f#is_commutative then begin
          x#add_rule (weak_rule (app f [v1;v2]) (app f [v2;v1]));
        end;
      in
      x#iter_syms iterer;

(* probabilistic rules *)
    method find_prule = Hashtbl.find prule_table
    method iter_prules f = Hashtbl.iter f prule_table
    method for_all_prules f = hashtbl_for_all f prule_table
    method exists_prule f = hashtbl_exists f prule_table
    method fold_prules : 'b. (int -> prule -> 'b -> 'b) -> 'b -> 'b =
      fun f a -> Hashtbl.fold f prule_table a
    method private add_prule_i i prule =
      let f = x#get_sym (root prule#l) in
      Hashtbl.add prule_table i prule;
      f#p_define_by i;
      prule_cnt <- prule_cnt + 1;
    method add_prule prule =
      x#add_prule_i prule_cnt prule;
    method remove_prule i =
      let prule = x#find_prule i in
      let f = x#get_sym (root prule#l) in
      f#p_undefine_by i;
      prule_cnt <- prule_cnt - 1;
      Hashtbl.remove prule_table i;
    method replace_prule i prule =
      x#remove_prule i;
      x#add_prule_i i prule;
    method modify_prule i l d =
      x#replace_prule i (new prule l d)



(* input *)
    method private trans_term (Trs_ast.Term ((_,fname),ss)) =
      let f = x#get_sym_name fname in
      if f#arity_is_unknown then f#set_arity (List.length ss);
      Node( (f :> sym), List.map (x#trans_term) ss)
    method private add_rule_raw =
      function
      | Trs_ast.Rew ([],l,r)    -> x#add_rule (rule (x#trans_term l) (x#trans_term r));
      | Trs_ast.RelRew ([],l,r) -> x#add_rule (weak_rule (x#trans_term l) (x#trans_term r));
      | Trs_ast.DistRew (l,d)   ->
        let d' = List.map (fun (i,r) -> (i, x#trans_term r)) d in
        x#add_prule (new prule (x#trans_term l) d');
      | _         -> raise ExistsConditionalRule
    method private add_eq_raw (l,r) =
      let l = x#trans_term l in
      let r = x#trans_term r in
      x#add_rule (weak_rule l r);
      x#add_rule (weak_rule r l);
    method private add_theory_raw =
      function
      | Trs_ast.Equations eqs -> List.iter (x#add_eq_raw) eqs
      | Trs_ast.Builtin ((_,th), syms) ->
        ths <- Ths.add th ths;
        let iterer =
          if th = "AC" || th = "A" || th = "C" then
            fun (_,name) -> (x#add_sym (new sym_unmarked (Th th) name))#set_arity 2
          else
            fun (_,name) -> ignore (x#add_sym (new sym_unmarked (Th th) name))
        in
        List.iter iterer syms
    method private add_decl =
      Trs_ast.(function 
      | VarDecl xs    ->
        List.iter (fun (_,name) -> ignore (x#add_sym (new sym_unmarked Var name))) xs
      | TheoryDecl ths  -> List.iter (x#add_theory_raw) ths
      | RulesDecl rs    -> List.iter (x#add_rule_raw) rs
      | StrategyDecl _  -> ()(* raise UnknownStrategy *)
      | OtherDecl _   -> ())
    method read file =
      let c = open_in file in
      List.iter x#add_decl (Read.check_trs file c);
      close_in c
    method read_stdin =
      List.iter x#add_decl (Read.check_trs "stdin" stdin);
(* outputs *)
    method output_ths : 'a. (#Io.printer as 'a) -> unit = fun pr ->
      let iterer_th th =
        pr#puts th;
        pr#puts " symbols:";
        let iterer_syms (f:#sym) =
          if f#ty = Th th then begin
            pr#putc ' ';
            f#output pr;
          end;
        in
        x#iter_syms iterer_syms;
        pr#endl;
      in
      Ths.iter iterer_th ths;
    method output_rules : 'a. (#Io.printer as 'a) -> unit = fun pr ->
      print_tbl pr "" rule_table;
      print_tbl pr "p" prule_table;
    method output_last_rule : 'a. (#Io.printer as 'a) -> unit = fun pr ->
      print_tbl_index pr "   " (rule_cnt, Hashtbl.find rule_table rule_cnt);
    method output : 'a. (#Io.printer as 'a) -> unit = fun pr ->
      x#output_ths pr;
      x#output_rules pr;
    method output_wst : 'a. (#Io.printer as 'a) -> unit = fun pr ->
      pr#puts "(VAR";
      let iterer_var (v : #sym) =
        if v#is_var then begin
          pr#putc ' ';
          v#output pr;
        end
      in
      x#iter_syms iterer_var;
      pr#putc ')';
      pr#endl;
      pr#puts "(RULES";
      pr#enter 4;
      let iterer_rule _ (rule : #rule) =
        pr#endl;
        rule#output pr;
      in
      x#iter_rules iterer_rule;
      let iterer_prule _ (prule : #prule) =
        pr#endl;
        prule#print pr;
      in
      x#iter_prules iterer_prule;
      pr#putc ')';
      pr#leave 4;
      pr#endl;
    method output_xml_ths : 'a. (#Io.printer as 'a) -> unit = fun pr ->
      let iterer_A (f:#sym) =
        match f#ty with
        | Th "AC" | Th "A" -> f#output_xml pr
        | _ -> ()
      in
      let iterer_C (f:#sym) =
        match f#ty with
        | Th "AC" | Th "C" -> f#output_xml pr
        | _ -> ()
      in
      if Ths.mem "AC" ths || Ths.mem "A" ths then begin
        Xml.enclose "Asymbols" (fun _ -> x#iter_syms iterer_A) pr;
      end else begin
        Xml.tag "Asymbols" pr; (* TODO refine CPF *)
      end;
      if Ths.mem "AC" ths || Ths.mem "C" ths then begin
        Xml.enclose "Csymbols" (fun _ -> x#iter_syms iterer_C) pr;
      end else begin
        Xml.tag "Csymbols" pr;
      end;
    method output_xml_rules : 'a. (#Io.printer as 'a) -> unit =
      Xml.enclose "rules" (fun pr ->
(*        x#iter_rules (fun _ rule -> rule#output_xml pr)
*)        for i = 1 to rule_cnt do
          (x#find_rule i)#output_xml pr;
        done
      )
    method output_xml : 'a. (#Io.printer as 'a) -> unit =
      Xml.enclose "trs" x#output_xml_rules << x#output_xml_ths

    method output_xml_ho_signature : 'a. (#Io.printer as 'a) -> unit = fun pr ->
      Xml.enter "higherOrderSignature" pr;
      let first = ref true in
      let iterer_var (v:#sym) =
        if v#is_var then begin
          if !first then begin
            Xml.enter "variableTypeInfo" pr;
            first := false;
          end;
          Xml.enclose "varDeclaration" (
            v#output_xml <<
            Xml.enclose "type" (Xml.enclose "basic" (puts "o"))
          ) pr;
        end;
      in
      x#iter_syms iterer_var;
      if not !first then
        Xml.leave "variableTypeInfo" pr;
      first := true;
      let iterer_fun (f:#sym) =
        if f#is_fun then begin
          if !first then begin
            Xml.enter "functionSymbolTypeInfo" pr;
            first := false;
          end;
          Xml.enter "funcDeclaration" pr;
          f#output_xml pr;
          Xml.enter "typeDeclaration" pr;
          for i = 0 to f#arity do
            Xml.enclose "type" (Xml.enclose "basic" (putc 'o')) pr;
          done;
          Xml.leave "typeDeclaration" pr;
          Xml.leave "funcDeclaration" pr;
        end;
      in
      x#iter_syms iterer_fun;
      if not !first then begin
        Xml.leave "functionSymbolTypeInfo" pr;
      end;
      Xml.leave "higherOrderSignature" pr;
    method output_xml_ho : 'a. (#Io.printer as 'a) -> unit =
      Xml.enclose "trs" ( x#output_xml_rules << x#output_xml_ho_signature )
  end;;

type path = int * (int list)

let path_append (c1,is1) (c2,is2) = (c1 + c2, is1 @ is2)
let cu_append (c1,u1) (c2,u2) = (c1 + c2, u1#compose u2)

