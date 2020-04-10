(* zip: string list * int list -> (string * int) list*)
fun zip ([], _): (string * int) list = []
  | zip (_, []) = []
  | zip (s::S, x::L) = (s,x)::zip(S,L);

val result = zip (["hello","world","cute"],[1,2,3,4]);

(* unzip: (string * int) list -> string list * int list *)
fun unzip (L: (string * int) list): string list * int list = 
    let 
        fun helpfun ([]:(string * int) list, slist:string list, intlist:int list) = (slist, intlist)
          | helpfun (x::L, slist, intlist) = helpfun(L,slist@[#1 x], intlist@[#2 x])
    in
        helpfun(L,[],[])
    end;


