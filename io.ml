class virtual outputter =
	object (x)
		method virtual output_string : string -> unit
		method virtual output_char : char -> unit
		method output_int i = x#output_string (string_of_int i)
		method output_float f = x#output_string (string_of_float f)
		method virtual flush : unit
		method virtual close : unit
	end

class wrap_out os =
	object
		inherit outputter
		method output_string = output_string os
		method output_char = output_char os
		method flush = flush os
		method close = close_out os
	end

class virtual inputter =
	object
		method virtual ready : bool
		method virtual input_line : string
	end

class wrap_in is =
	object
		inherit inputter
		method ready = true
		method input_line = input_line is
	end

class virtual t =
	object
		inherit outputter
		inherit inputter
	end

class virtual printer =
	object (x)
		inherit outputter
		method cr = x#output_char '\n'
		method enter (_:int) = ()
		method leave (_:int) = ()
		method enter_inline = ()
		method leave_inline = ()
	end

class pretty_printer (base : #outputter) maxdepth =
	object (x)
		inherit printer
		method output_string = base#output_string
		method output_char = base#output_char
		method flush = base#flush
		method close = base#close
		val mutable depth = 0
		method enter n = depth <- depth + n
		method leave n = depth <- depth - n
		method enter_inline = x#enter maxdepth
		method leave_inline = x#leave maxdepth
		method cr =
			if depth < maxdepth then begin
				x#output_char '\n';
				for i = 1 to depth do
					base#output_char ' ';
				done;
			end
			else x#output_char ' '
	end

class debug_out main os =
	let debugger = new pretty_printer (new wrap_out os) 32 in
	object (x)
		inherit printer
		method output_string s = main#output_string s; debugger#output_string s;
		method output_char c = main#output_char c; debugger#output_char c;
		method flush = main#flush; debugger#flush;
		method close = main#close
	end

class debug_in main os =
	let debugger = new wrap_out os in
	object (x)
		inherit inputter
		method ready = main#ready
		method input_line =
				debugger#output_string "< ";
				debugger#flush;
				let s = main#input_line in
				debugger#output_string s;
				debugger#output_char '\n';
				debugger#flush;
				s
	end

class finalized finalizer =
	let rfin = ref ignore in
	let fin x = rfin := ignore; finalizer x; in
	object (x)
		initializer
			rfin := fin;
			Gc.finalise fin x;
			at_exit (fun _ -> !rfin x)
	end

let cerr = new pretty_printer (new wrap_out stderr) 32
let cout = new pretty_printer (new wrap_out stdout) 32

let puts s pr = pr#output_string s
let putc c pr = pr#output_char c
let put_int i pr = pr#output_int i
let endl pr = pr#cr; pr#flush

let (<<) f g pr = f pr; g pr

