(* ACM1701-U201714780-刘晨彦 *)
fun sum [] = 0
  | sum (x::L) = x + (sum L);

(* mult : int list -> int 		*)
(* REQUIRES: true		*)
(* ENSURES: mult(L) evaluates to the product of the integers in L. *)
fun mult [] = 1
  | mult (x::L) = x * mult(L);

(* Mult : int list list -> int 	*)
(* REQUIRES: true		*)
(* ENSURES: mult(R) evaluates to the product of all the integers in the lists of R. *)
fun Mult [] = 1
  | Mult (r::R) = mult(r) * Mult(R); 

(* mult’ : int list * int -> int *)
(* REQUIRES: true				*)
(* ENSURES: mult’(L, a) = mult L * a *)
fun mult' ([], a) = a
  | mult' (x::L, a) = mult'(L, x*a);
 (*mult' 得到a和L内元素的乘积*)

(* Mult’ : int list list * int -> int *)
(* REQUIRES: true				*)
(* ENSURES: Mult’(L, a) = Mult L * a *)
fun Mult' ([], a) = a
  | Mult' (x::L, a) = Mult'(L, mult'(x, a));

fun double (0: int): int = 0
  | double n = 2 + double(n-1);

(* square : int -> int *)
(* REQUIRES: n >= 0 *)
(* ENSURES: double n evaluates to 2 * n.*)
fun square (0: int): int = 0
  | square n = square(n - 1) + double(n - 1) + 1;

(* divisibleByThree : int -> bool 	*)
(* REQUIRES: true				*)
(* ENSURES: divisibleByThree n evaluates to true if n is a multiple of 3 and to false otherwise *)
fun divisibleByThree (0: int): bool = true
  | divisibleByThree (1) = false
  | divisibleByThree (2) = false
  | divisibleByThree (n) = divisibleByThree(n-3);

(* oddP : int -> bool 		*)
(* REQUIRES: n >= 0 		*)
(* ENSURES: oddP n evaluates to true iff n is odd. *)
fun oddP (0: int): bool = false
  | oddP (1) = true
  | oddP (n) = oddP(n-2);

(* ----------For tests------------ *)
val test_mult = 
	(mult [1,2,3,4] = 24) andalso
	(mult [] = 1) andalso
	(mult [5,2,1,8] = 80)
val test_Mult = 
	(Mult [[]] = 1) andalso
	(Mult [] = 1) andalso
	(Mult [[1,2],[3,4]] = 24)
val test_Mult' = 
	(Mult' ([[]], 5) = 5) andalso
	(Mult' ([], 5) = 5) andalso
	(Mult' ([[1,2],[3,4]],5) = 120)
val test_square = 
	(square 0 = 0) andalso
	(square 7 = 49)
val test_divisibleByThree = 
	(divisibleByThree 3 = true) andalso
	(divisibleByThree 28 = false) andalso
	(divisibleByThree 0 = true)
val test_oddP = 
	(oddP 81 = true) andalso
	(oddP 0 = false) andalso
	(oddP 52 = false)