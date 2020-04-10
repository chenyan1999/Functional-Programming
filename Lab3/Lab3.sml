datatype 'a option = SOME of 'a | NONE;
datatype 'a tree = Empty | Node of 'a tree * 'a * 'a tree;
(* thenAddOne: ((int -> int) * int) -> int
   REQUIRES: x is an integer
   ENSURES: f(x) + 1*)
fun thenAddOne (f, x) = f(x:int) + 1;

(* mapList: ((‘a -> ‘b) * ‘a list) -> ‘b list
   REQUIRES: input is a list
   ENSURES: for each element in list: f(x)*)
fun mapList (f, []) = []
  | mapList (f, (x::L)) = f(x)::mapList(f, L);

(* mapList': (‘a -> ‘b) -> (‘a list -> ‘b list)
   REQUIRES: input is a list
   ENSURES: for each element in list: f(x)*)
fun mapList' f [] = []
  | mapList' f (x::L) = f(x)::mapList' f L;

(* findOdd: int list -> int option
   REQUIRES: input is a list
   ENSURES: find the 1st odd num in list, return SOME X, else NONE*)
fun findOdd [] = NONE
  | findOdd (x::L) = 
    let 
        fun IsOdd 0 = false
          | IsOdd 1 = true
          | IsOdd x = IsOdd(x - 2) 
    in
        case IsOdd x of false => findOdd L
                      | true => SOME x
    end

(* subsetSumOption: int list * int -> int list option
   REQUIRES: input is a int list and an integer
   ENSURES: if exist a subset L' in L which the sum of all
            elements are equal to s, return SOME L', else NONE*)
fun subsetSumOption (L: int list, S: int) =
    let 
        fun subset [] = [[]]
          | subset (x::L) = 
            let 
                val s = subset L 
            in
                s @ mapList' (fn A => x::A) s
            end
        (* int int list * int -> int list option *)
        fun subsetsumcmp ([], _) = NONE
          | subsetsumcmp (L'::L, S) = 
            let 
            fun listsum [] = 0
            | listsum(x::L) = x + listsum L
            in
            case Int.compare(listsum L', S) 
            of EQUAL => SOME L'
            | _ => subsetsumcmp(L,S)
            end
    in
        subsetsumcmp(subset L, S)
        (* first create a list to store all sublist of L
        then compare the sum of each sublist with S *)
    end

(* exists: ('a -> bool) -> 'a list -> bool
   REQUIRES: input is a list
   ENSURES: true if there is an x in L such that f x=true *)
fun exists f [] = false
  | exists f (x::L) = 
    case f x 
    of true => true
    | false => exists f L;

(* forall: ('a -> bool) -> 'a list -> bool
   REQUIRES: input is a list and it's not an empty one
   ENSURES: true if f x = true for every item x in L *)
fun forall f [] = true
  | forall f (x::L) = 
    case f x
    of true => forall f L 
    | false => false

(* treeFilter: ('a -> bool) -> 'a tree -> 'a option tree
   REQUIRES: input is a tree
   ENSURES: for every node x satisfy f x, save it as SOME x, else NONE*)
fun treeFilter f Empty = Empty
  | treeFilter f (Node(L, x, R)) = 
    case f x
    of true => Node(treeFilter f L, SOME x, treeFilter f R)
    | false => Node(treeFilter f L, NONE, treeFilter f R);

(* --------For Tests--------*)
fun double x = 2*x;
fun square x = x*x;
fun odd x =
    case x mod 2
    of 1 => true
    | _ => false
fun divisibleby3 x = 
    case x mod 3 
    of 0 => true
    | _ => false
val t:int tree = Node(Node(Node(Empty,1,Empty),2,Node(Empty,3,Empty)),4, Node(Node(Empty,5,Empty),6,Node(Empty,7,Empty)));
val test_thenAddOne = 
    (thenAddOne (double, 7) = 15) andalso
    (thenAddOne (square, 8) = 65);
val test_mapList = 
    (mapList (double, [1,2,3,4]) = [2,4,6,8]) andalso
    (mapList (square, [1,3,5,7]) = [1,9,25,49]);
val test_mapList' = 
    (mapList' double [1,2,3,4] = [2,4,6,8]) andalso
    (mapList' square [1,3,5,7] = [1,9,25,49]);
val test_findOdd = 
    (findOdd [2,4,6,7,1,5,2] = SOME 7) andalso
    (findOdd [2,4,6,8,10] = NONE) andalso
    (findOdd [] = NONE);
val test_subsetSumOption = 
    (subsetSumOption([1,2,3,4,5], 16) = NONE) andalso
    (subsetSumOption([], 0) = SOME []) andalso
    (subsetSumOption([],5) = NONE) andalso
    (subsetSumOption([1,2,3,4,5,6], 16) = SOME [2,3,5,6]);
val test_exists = 
    (exists odd [2,4,6,8,10] = false) andalso
    (exists divisibleby3 [2,4,6,8,10] = true) andalso
    (exists odd [1,2,3,4,5] = true);
val test_forall = 
    (forall odd [1,2,3,4] = false) andalso
    (forall odd [1,3,85,71] = true) andalso
    (forall divisibleby3 [3,6,72,81] = true);
val test_treeFilter = 
    (treeFilter odd t = Node(Node(Node(Empty,SOME 1,Empty),NONE,Node(Empty,SOME 3,Empty)),NONE, Node(Node(Empty,SOME 5,Empty),NONE,Node(Empty,SOME 7,Empty))))
    andalso
    (treeFilter divisibleby3 t = Node(Node(Node(Empty,NONE,Empty),NONE,Node(Empty,SOME 3,Empty)),NONE,Node(Node(Empty,NONE,Empty),SOME 6,Node(Empty,NONE,Empty))));


