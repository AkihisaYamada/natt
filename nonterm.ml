open Util
open Params
open Term

let prerr_dp i l r =
	prerr_string "\t";
	prerr_term l;
	prerr_endline "  ->";
	prerr_string "  #";
	prerr_int i;
	prerr_string "\t";
	prerr_term r;
	prerr_endline "  ->>";
	;;

let prerr_loop dg u =
	let rec sub pos =
		function
		| [] -> ()
		| [i] ->
			let (l,r) = dg#find_dp i in
			let v = string_of_int pos in
			let l = u#subst (Subst.vrename v l) in
			prerr_string "   \t";
			prerr_term l;
			prerr_newline ();
		| i::is ->
			let (l,r) = dg#find_dp i in
			let v = string_of_int pos in
			let l = u#subst (Subst.vrename v l) in
			let r = u#subst (Subst.vrename v r) in
			prerr_dp i l r;
			sub (pos+1) is;
	in
	sub 1

let estimate_paths len trs dg scc =
	let subdg = dg#get_subdg scc in
	let rec sub n i k =
		if n > len then []
		else if n = len then
			if i = k then [[]] else []
		else
			Dp.SubDG.fold_succ
			(fun j paths ->
				let folder paths path =
					if List.mem j path then paths else (j::path) :: paths
				in
				List.fold_left folder paths (sub (n+1) j k)
			)
			subdg i []
	in
	sub 0

let find_loop lim trs dg scc =
	let iterer len nlim i1 =
		let (l1,r1) = dg#find_dp i1 in
		let rec sub pos loop u1 l2 r2 path strict =
			let cnt = ref 0 in
			match path with
			| [] ->
				begin
					let l1 = u1#subst l1 in
					let r1 = u1#subst r1 in
					let l2 = u1#subst l2 in
					match Subst.matches l2 l1 with
					| Some(u2) ->
						let print_loop _ =
							prerr_dp i1 l1 r1;
							prerr_loop dg u1 loop;
							prerr_endline "  Looping with:";
							u2#output stderr;
						in
						if strict then begin
							comment (fun _ -> prerr_endline " found.");
							proof print_loop;
							raise Nonterm;
						end else begin
							let l3 = u2#subst l2 in
							if duplicating l1 l3 then begin
								proof (fun _ -> prerr_endline "  Duplicating loop.");
								proof print_loop;
								raise Nonterm;
							end else begin
								debug2(fun _ -> prerr_endline "... only weak rules.");
							end;
						end;
					| _ -> ();
				end
			| i3::rest ->
				let (l3,r3) = dg#find_dp i3 in
				let v = string_of_int pos in
				let l3 = Subst.vrename v l3 in
				let r3 = Subst.vrename v r3 in
				List.iter
				(fun (c2,u2) -> sub (pos + 1) loop (u1#compose u2) l3 r3 rest (strict || dg#is_strict i3);)
				(Trs.instantiate_edge trs cnt nlim (u1#subst r2) l3);
		in
		let iterer2 loop =
			debug2
			(fun _ ->
				prerr_string "    Checking loop: #";
				prerr_int i1;
				List.iter (fun i -> prerr_string " -> #"; prerr_int i;) loop;
				flush stderr;
			);
			sub 1 loop (new Subst.t) l1 r1 loop (dg#is_strict i1);
			debug2 (fun _ -> prerr_newline ());
		in
		List.iter iterer2 (estimate_paths len trs dg scc i1 i1);
	in
	if lim > 0 then begin
		comment (fun _ -> prerr_string "  Finding a loop... "; flush stderr);
		debug2 (fun _ -> prerr_newline ());
		for len = 1 to lim do
			IntSet.iter (iterer len (max 0 (params.max_narrowing - IntSet.cardinal scc))) scc;
		done;
		comment (fun _ -> prerr_endline "failed.");
	end
