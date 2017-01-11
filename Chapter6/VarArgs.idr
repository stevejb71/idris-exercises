total AdderType : Num a => (numargs : Nat) -> Type
AdderType {a} Z = a
AdderType {a} (S k) = (next : a) -> AdderType k

-- Variable length adder, on any type of Num.
total adder : Num a => (numargs : Nat) -> (acc : a) -> AdderType numargs
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)

--

data Format = Number Format -- represents %d
            | Str Format    -- represents %s
            | Character Format    -- represents %c
            | FloatingPoint Format    -- represents %c
            | Lit String Format -- represents a literal
            | End           -- empty
%name Format fmt,fmt1

total PrintfType : Format -> Type
PrintfType (Number fmt) = (i : Int) -> PrintfType fmt
PrintfType (Str fmt) = (s : String) -> PrintfType fmt
PrintfType (Character fmt) = (c : Char) -> PrintfType fmt
PrintfType (FloatingPoint fmt) = (c : Double) -> PrintfType fmt
PrintfType (Lit s fmt) = PrintfType fmt
PrintfType End = String

total printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc = \s => printfFmt fmt (acc ++ s)
printfFmt (Character fmt) acc = \c => printfFmt fmt (acc ++ cast c)
printfFmt (FloatingPoint fmt) acc = \d => printfFmt fmt (acc ++ cast d)
printfFmt (Lit s fmt) acc = printfFmt fmt (acc ++ s)
printfFmt End acc = acc

total toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: rest) = Number (toFormat rest)
toFormat ('%' :: 's' :: rest) = Str (toFormat rest)
toFormat ('%' :: 'c' :: rest) = Character (toFormat rest)
toFormat ('%' :: 'f' :: rest) = FloatingPoint (toFormat rest)
toFormat (c :: cs) = case toFormat cs of 
                       Lit lit cs' => Lit (strCons c lit) cs'
                       fmt => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""