let continuous_int i j = abs(i - j) < 2
let continuous_index (i,_) (j,_) = continuous_int i j
let output_dots os = output_string os ".."
let output_int os i = output_string os (string_of_int i)
let output_index os (i,_) = output_int os i
let output_space os = output_char os ' '

class ['a] t os printer prefix infix continuous =
	object (self)
		val mutable curr = None
		method put =
			match curr with
			| None -> ()
			| Some(len,x) ->
				if len < 2 then prefix os else infix os;
				printer os x;
		method add (y:'a) =
			match curr with
			| None ->
				curr <- Some(0,y);
				self
			| Some(len,x) ->
				if continuous x y then begin
					if len = 0 then self#put;
					curr <- Some(len + 1, y);
				end else begin
					self#put;
					curr <- Some(0,y);
				end;
				self
		method close =
			self#put;
			curr <- None;
	end

class for_int os prefix =
	[int] t os output_int (fun os -> output_string os prefix) output_dots continuous_int

let output_int_list os prefix is =
	let folder abbr i = abbr#add i in
	(List.fold_left folder (new for_int os prefix) is)#close
