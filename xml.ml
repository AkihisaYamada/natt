let puts s os = output_string os s
let putc c os = output_char os c

let (>>) f g os = f os; g os

let opn name = putc '<' >> puts name >> putc '>'

let cls name = puts "</" >> puts name >> putc '>'

let enclose name body = opn name >> body >> cls name

class xml nam = object (x:'a)
	val mutable name = nam
	val mutable children : 'a list = []
	
end



