open Params

exception Dead of string

class virtual outputter =
	object
		method virtual output_string : string -> unit
		method virtual output_char : char -> unit
		method virtual flush : unit
		method virtual close : unit
	end

class virtual inputter =
	object
		method virtual ready : bool
		method virtual input_line : string
	end

class virtual io =
	object
		inherit outputter
		inherit inputter
	end

class virtual printer =
	object (x)
		inherit outputter
		method pr = x#output_string
		method pr_c = x#output_char
		method cr = x#pr_c ' '
		method enter (_:int) = ()
		method leave (_:int) = ()
		method enter_inline = ()
		method leave_inline = ()
		method pr_i i = x#pr (string_of_int i)
		method pr_f f = x#pr (string_of_float f)
	end

class virtual debug_printer os =
	object (x)
		inherit printer as super
		val mutable depth = 0
		method pr s = super#pr s; output_string os s;
		method pr_c c = super#pr_c c; output_char os c;
		method enter n = depth <- depth + n
		method leave n = depth <- depth - n
		method enter_inline = x#enter 32
		method leave_inline = x#leave 32
		method cr =
			if depth < 32 then begin
				x#pr_c '\n';
				for i = 1 to depth do
					output_char os ' ';
				done;
			end
			else x#pr_c ' '
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

class stderr_outputter =
	object
		inherit outputter
		method output_string = prerr_string
		method output_char = prerr_char
		method flush = flush stderr
		method close = ()
	end;;


class t command opts =
	object (x)
		inherit io

		val mutable pid = 0
		val mutable in_from = Unix.stdin
		val mutable out_to = Unix.stdout
		val mutable is = stdin
		val mutable os = stdout

		method output_info os =
			output_string os "pid=";
			output_string os (string_of_int pid);

		method init =
			let (in_to_proc,out_to_proc) = Unix.pipe () in
			let (in_from_proc,out_from_proc) = Unix.pipe () in
			debug
			(fun _ ->
				prerr_string "Running: ";
				prerr_string (String.concat " " (command :: opts));
				prerr_string " ... ";
			);
			pid <- Unix.create_process
					command
					(Array.of_list (command::opts))
					in_to_proc
					out_from_proc
					Unix.stderr;
			debug (fun _ -> x#output_info stderr; prerr_newline (););
			Unix.close in_to_proc;
			Unix.close out_from_proc;
			in_from <- in_from_proc;
			out_to <- out_to_proc;
			is <- Unix.in_channel_of_descr in_from;
			os <- Unix.out_channel_of_descr out_to;

		method dead =
			pid = 0 || if fst Unix.(waitpid [ WNOHANG ] pid) = pid then (pid <- 0; true) else false
		method ready =
			if x#dead then raise (Dead command);
			match Unix.select [in_from] [] [] 0.0 with
			| ([_],_,_) -> true
			| _ -> false
		method input_line = input_line is
		method output_string = output_string os
		method output_char = output_char os
		method flush = flush os
		method close =
			if not x#dead then begin
				x#flush;
				if Sys.os_type <> "Win32" then begin
					debug (fun _ ->
						prerr_string "killing ";
						x#output_info stderr;
						flush stderr;
					);
					try
						x#flush;
						ignore Unix.(kill pid Sys.sigkill);
						pid <- 0;
						debug (fun _ -> prerr_endline ". ok.");
					with Unix.Unix_error(_,_,_) ->
					debug (fun _ -> prerr_endline "... failed.");
				end else begin
					Unix.waitpid [] pid;
					pid <- 0;
				end;
				Unix.close in_from;
				Unix.close out_to;
			end;
	end

class debug_in debug_os command opts =
	object (x)
		inherit io
		inherit t command opts as super

		method input_line =
				output_string debug_os "< ";
				flush debug_os;
				let s = super#input_line in
				output_string debug_os s;
				output_char debug_os '\n';
				flush debug_os;
				s
		method flush =
			super#flush;
			flush debug_os;
	end
