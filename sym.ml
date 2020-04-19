open Util
open Params
open Io

type symtype = Var | Fun | Th of string | Special

let put_name_pad min name (pr:#Io.outputter) =
	let n = String.length name in
	let rec sub i min =
		if i < n then begin
			match name.[i] with
			| '\\'	-> pr#puts "\\\\"; sub (i+1) (min-2);
			| '#'	-> pr#puts "\\#"; sub (i+1) (min-2);
			| '^'	-> pr#puts "\\^"; sub (i+1) (min-2);
			| ' '	-> pr#putc name.[i+1]; sub (i+2) min;
			| c		-> pr#putc c; sub (i+1) (min-1);
		end else begin
			for i = 1 to min do pr#putc ' ' done;
		end;
	in
	sub 0 min
let put_name name (pr:#Io.outputter) = put_name_pad 0 name pr

class virtual sym ty0 = object (x:'x)
	val mutable ty = ty0
	method is_var = ty = Var
	method is_fun = not x#is_var
	method is_theoried = match ty with Th _ -> true | _ -> false
	method is_associative = ty = Th "AC" || ty = Th "A"
	method is_commutative = ty = Th "AC" || ty = Th "C"
	method ty = ty
	method set_ty ty' = ty <- ty'
	method virtual name : string
	method equals : 'b. (<name:string;..> as 'b) -> bool = fun y ->
		x#name = y#name
	method output : 'b. (#outputter as 'b) -> unit = put_name x#name
	method output_pad : 'b. int -> (#outputter as 'b) -> unit = fun min os -> put_name_pad min x#name os
	method virtual output_xml : 'b. (#printer as 'b) -> unit
end

class sym_unmarked ty0 name = object (x:'x)
	inherit sym ty0
	method name = name
	method output_xml : 'b. (#printer as 'b) -> unit =
		if x#is_var then Xml.enclose_inline "var" (Xml.put_string name)
		else Xml.enclose_inline "name" (Xml.put_string name)
end

let escape c = " " ^ String.make 1 c

let mark_name name = escape '#' ^ name
let unmark_name name = String.sub name 2 (String.length name - 2)
let string_prefix s t =
	let n = String.length t in
	String.length s >= n &&
	let rec sub i =
		i >= n || s.[i] = t.[i] && sub (i+1)
	in
	sub 0

let marked_name name = string_prefix name (escape '#')

class sym_marked ty0 name0 = object
	inherit sym ty0
	val mutable name = name0
	method name = mark_name name
	method output_xml =
		Xml.enclose_inline "sharp" (Xml.enclose_inline "name" (Xml.put_string name))
end

let mark_sym (f:#sym) = new sym_marked f#ty f#name

let freeze_name fname gname i = fname ^ escape '^' ^ string_of_int i ^ "_" ^ gname

class sym_freezed (f:#sym) (g:#sym) i =
	let name = freeze_name f#name g#name i in
	object
		inherit sym f#ty
		method name = name
		method output_xml : 'b. (#printer as 'b) -> unit =
			Xml.enclose_inline "name" (
				Xml.put_string f#name << puts "&middot;" <<
				Xml.put_string g#name << Xml.enclose "sup" (put_int i)
			)
	end

class sym_fresh ty i =
	let name = escape '_' ^ string_of_int i in
	object (x:'x)
		inherit sym ty
		method name = name
		method output_xml : 'b. (#printer as 'b) -> unit =
			Xml.enclose_inline (if x#is_var then "var" else "name") (
				puts "_" << put_int i
			)
	end

