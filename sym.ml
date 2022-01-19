open Util
open Io

class virtual named = object (x)
  method virtual name : string
  method equals : 'b. (<name : string; ..> as 'b) -> bool =
    fun y -> x#name = y#name
end

module SymSet = Set.Make (
  struct
    type t = named
    let compare x y = String.compare x#name y#name
  end
)

type symtype = Var | Fun | Th of string

let put_name_pad min name (pr:#Io.outputter) =
  let n = String.length name in
  let rec sub i min =
    if i < n then begin
      match name.[i] with
      | '\\'  -> pr#puts "\\\\"; sub (i+1) (min-2);
      | '#' -> pr#puts "\\#"; sub (i+1) (min-2);
      | '^' -> pr#puts "\\^"; sub (i+1) (min-2);
      | ' ' -> pr#putc name.[i+1]; sub (i+2) min;
      | c   -> pr#putc c; sub (i+1) (min-1);
    end else begin
      for i = 1 to min do pr#putc ' ' done;
    end;
  in
  sub 0 min
let put_name name (pr:#Io.outputter) = put_name_pad 0 name pr

class virtual sym ty0 = object (x:'x)
  inherit named
  val mutable ty = ty0
  method is_var = ty = Var
  method is_fun = not x#is_var
  method is_theoried = match ty with Th _ -> true | _ -> false
  method is_associative = ty = Th "AC" || ty = Th "A"
  method is_commutative = ty = Th "AC" || ty = Th "C"
  method ty = ty
  method set_ty ty' = ty <- ty'
  method output : 'b. (#outputter as 'b) -> unit = put_name x#name
  method output_pad : 'b. int -> (#outputter as 'b) -> unit = fun min os -> put_name_pad min x#name os
  method virtual output_xml : 'b. (#printer as 'b) -> unit
end

class sym_unmarked ty0 name = object (x:'x)
  inherit sym ty0
  method name = name
  method output_xml : 'b. (#printer as 'b) -> unit =
    if x#is_var then MyXML.enclose_inline "var" x#output
    else MyXML.enclose_inline "name" x#output
end

let mark_name name = " #" ^ name
let marked_name name = String.sub name 0 2 = " #"
let unmark_name name = String.sub name 2 (String.length name - 2)


class sym_marked ty0 name0 = object
  inherit sym ty0
  val mutable name = name0
  method name = mark_name name
  method output_xml =
    MyXML.enclose_inline "sharp" (MyXML.enclose_inline "name" (put_name name))
end

let mark_sym (f:#sym) = new sym_marked f#ty f#name

let freeze_name fname gname i = fname ^ "❆" ^ string_of_int i ^ "_" ^ gname

class sym_freezed (f:#sym) (g:#sym) i =
  let name = freeze_name f#name g#name i in
  object
    inherit sym f#ty
    method name = name
    method output_xml : 'b. (#printer as 'b) -> unit =
      MyXML.enclose_inline "name" (
        f#output << puts "&middot;" <<
        g#output << MyXML.enclose "sup" (put_int i)
      )
  end

class sym_fresh ty i =
  let name = "†" ^ string_of_int i in
  object (x:'x)
    inherit sym ty
    method name = name
    method output_xml : 'b. (#printer as 'b) -> unit =
      MyXML.enclose_inline (if x#is_var then "var" else "name") (
        puts "_" << put_int i
      )
  end

