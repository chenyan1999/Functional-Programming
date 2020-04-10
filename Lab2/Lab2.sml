datatype 'a tree = Empty | Node of 'a tree * 'a * 'a tree;
(* reverse: int list ->int list
   REQUIRES: elements in list are all integer
   ENSURES: reverse a list's order *)
fun reverse[] = []
  | reverse(x::L): int list = (reverse(L)) @ [x];

(* reverse': int list ->int list
   REQUIRES: elements in list are all int
   ENSURES: reverse a list's order *)
fun reverse'(L : int list): int list = 
    let fun helpfun(L : int list, R : int list): int list = 
        case L of [] => R
                | (x::L') => helpfun(L', x::R)
        in
            helpfun(L, [])
        end;

(* interleave: int list * int list -> int list 
   REQUIRES: elements in any list are all integer
   ENSURES: merge two list into one*)
fun interleave(L: int list, R: int list):int list =
    let fun helpfun(L: int list, R: int list, Res: int list): int list =
        case (L,R) of ([], []) => Res
                    | (x::L', []) => Res @ (x::L')
                    | ([], y::R') => Res @ (y::R')
                    | (x::L', y::R') => helpfun(L', R', Res@ [x]@ [y])
        in
            helpfun(L, R, [])
        end;

(* listToTree: int list -> int tree
   REQUIRES: elements in list are all intergers
   ENSURES: transform a list into a balanced tree*)
fun listToTree(L: int list): int tree = 
    case L 
        of [] => Empty
        | _ =>  let
                    val mid:int = length(L) div 2
                    val leftlist = List.take(L,mid)
                    val x:int = hd(List.drop(L,mid))
                    val rightlist = tl(List.drop(L,mid))
                in 
                    Node(listToTree(leftlist), x, listToTree(rightlist))
                end;

(* revT: int list -> int tree
   REQUIRES: elements in list are all intergers
   ENSURES: exchange left-subtree and right-subtree for ever node*)
fun revT(Empty:int tree): int tree = Empty
  | revT(Node(L,x,R)) = Node(revT(R),x,revT(L));

(* trav: int tree -> int list
   REQUIRES: elements in tree are all intergers
   ENSURES: transform a tree into a list*)
fun trav(Empty:int tree):int list = []
  | trav(Node(L,x,R)) = trav(L)@[x]@trav(R);

(* binarySearch: int tree * int -> bool
   REQUIRES: elements in tree are ordered
   ENSURES: find x in tree or not*)
fun binarySearch(Empty:int tree, x: int): bool = false
  | binarySearch(Node(L, m, R), x:int) = 
    case Int.compare(m,x)
    of GREATER => binarySearch(L,x)
    |  EQUAL => true
    |  LESS => binarySearch(R,x);

(* ----Next are for test--- *)
val t:int tree = Node(Node(Node(Empty,1,Empty),2,Node(Empty,3,Empty)),4, Node(Node(Empty,5,Empty),6,Node(Empty,7,Empty)));
val reverse_test = ([1,2,3,4,5,6,7,8,9] = reverse([9,8,7,6,5,4,3,2,1]));
val reverse'_test = ([1,2,3,4,5,6,7,8,9] = reverse'([9,8,7,6,5,4,3,2,1]));
val interleave_test = 
    (interleave([2],[4]) = [2,4]) andalso 
    (interleave([2,3],[4,5]) = [2,4,3,5]) andalso
    (interleave([2,3],[4,5,6,7,8,9]) = [2,4,3,5,6,7,8,9]) andalso
    (interleave([2,3],[ ]) = [2,3]);
val listToTree_test = 
    (listToTree([]) = Empty) andalso
    (listToTree([1,2]) = Node (Node (Empty,1,Empty),2,Empty)) andalso
    (listToTree([1,2,3,4,5,6,7]) = t);
val revT_test = (trav(revT t) = reverse(trav t));
val binarySearch_test = 
    (binarySearch(t, 0) = false) andalso
    (binarySearch(t,7) = true) andalso
    (binarySearch(Empty, 4) = false)