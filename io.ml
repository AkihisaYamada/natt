class virtual outputter =
	object (x)
		method virtual puts : string -> unit
		method virtual putc : char -> unit
		method virtual flush : unit
		method virtual close : unit
		method put_int i = x#puts (string_of_int i)
		method put_hex i = x#puts (Printf.sprintf "%X" i)
		method put_float f = x#puts (string_of_float f)
		method endl = x#putc '\n'; x#flush;
	end

class wrap_out os =
	object
		inherit outputter
		method puts = output_string os
		method putc = output_char os
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
		method enter (_:int) = ()
		method leave (_:int) = ()
		method enter_inline = ()
		method leave_inline = ()
	end

class pretty_printer (base : #outputter) maxdepth =
	object (x)
		inherit printer
		method puts = base#puts
		method putc = base#putc
		method flush = base#flush
		method close = base#close
		val mutable depth = 0
		method enter n = depth <- depth + n
		method leave n = depth <- depth - n
		method enter_inline = x#enter maxdepth
		method leave_inline = x#leave maxdepth
		method endl =
			if depth < maxdepth then begin
				base#endl;
				for i = 1 to depth do
					base#putc ' ';
				done;
			end
			else x#putc ' '
	end

class debug_out main os =
	let debugger = new pretty_printer (new wrap_out os) 32 in
	object (x)
		inherit printer
		method puts s = main#puts s; debugger#puts s;
		method putc c = main#putc c; debugger#putc c;
		method flush = main#flush; debugger#flush;
		method close = main#close
	end

class debug_in main os =
	let debugger = new wrap_out os in
	object (x)
		inherit inputter
		method ready = main#ready
		method input_line =
				debugger#puts "< ";
				debugger#flush;
				let s = main#input_line in
				debugger#puts s;
				debugger#endl;
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

let pretty_wrap_out os = new pretty_printer (new wrap_out os) 32

let cerr = pretty_wrap_out stderr
let cout = pretty_wrap_out stdout

let puts s pr = pr#puts s
let putc c pr = pr#putc c
let put_int i pr = pr#put_int i
let endl pr = pr#endl
let enter n pr = pr#enter n
let leave n pr = pr#leave n


let (<<) f g pr = f pr; g pr

