fun map b [] = []
  | map b (x::L) = x * b :: map b L;

(* toInt: int -> int list -> int 
   Requires: b是基数 list is int list
   Ensures: ，list是用b进制表示的数字字符串，返回十进制的数*)
fun toInt b [] = 0
  | toInt b (x::L) = x +  toInt b (map b L);

(* toBase: int -> int -> int list 
   Requires: b是基数, n是十进制数字
   Ensures: 返回b进制表示的n的数字字符串*)
fun toBase b 0 = []
  | toBase b n = 
    let
        val redundant:int = n mod b
        val newn = (n - redundant) div b
    in
        redundant::(toBase b newn)  
    end;

(* convert: int * int -> int list -> int list 
   Requires: b1是基数, b2是基数，n是b1进制数字字符串
   Ensures: 返回b2进制表示的n的数字字符串*)
fun convert (b1, b2) [] = []
  | convert (b1, b2) L = 
    let 
        val num_10 = toInt b1 L
    in
        toBase b2 num_10
    end;



