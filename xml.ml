open Io

let enter_inline name = putc '<' >> puts name >> putc '>'

let leave_inline name = puts "</" >> puts name >> putc '>'

let enter name (pr:#printer) =
	pr#cr;
	enter_inline name pr;
	pr#enter 1;;

let leave name (pr:#printer) =
	pr#leave 1;
	pr#cr;
	leave_inline name pr;;

let enclose_inline name body = endl >> enter_inline name >> body >> leave_inline name

let enclose name body = enter name >> body >> leave name

let tag name = putc '<' >> puts name >> puts "/>"

type content = Empty | Children | String

class t nam = object (x:'a)
	val mutable name = nam
	val mutable content = Children
	val mutable children : 'a list = []
	val mutable value = ""
	method add_child child =
		content <- Children;
		children <- children @ [child];
	method make_string str =
		content <- String;
		value <- str;
	method output : Io.printer -> unit = fun pr ->
		pr#output_char '<';
		pr#output_string name;
		match content with
		| Empty -> pr#output_string "/>"; pr#cr;
		| Children ->
			pr#output_char '>';
			pr#enter 1;
			List.iter (fun child -> pr#cr; child#output pr) children;
			pr#leave 1;
			pr#cr;
			pr#output_string "</";
			pr#output_string name;
			pr#output_char '>';
		| String ->
			pr#output_char '>';
			pr#output_string value;
			pr#output_string "</";
			pr#output_string name;
			pr#output_char '>';
end

