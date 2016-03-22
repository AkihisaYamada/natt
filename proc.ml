open Params

exception Dead of string

class finalized finalizer =
	let rfin = ref ignore in
	let fin x = rfin := ignore; finalizer x; in
	object (x)
		initializer
			rfin := fin;
			Gc.finalise fin x;
			at_exit (fun _ -> !rfin x)
	end

class t command opts =
	object (x)
		inherit Io.t

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
					ignore (Unix.waitpid [] pid);
					pid <- 0;
				end;
				Unix.close in_from;
				Unix.close out_to;
			end;
	end

