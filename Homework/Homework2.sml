datatype 'a tree = Empty | Node of 'a tree * 'a * 'a tree;
fun PrefixSum [] = []
  | PrefixSum L:int list = 
    let
    	fun helpfun([], sum):int list = []
          | helpfun(x::L, sum) = (x + sum)::helpfun(L, x + sum)
    in
      	helpfun(L, 0)
    end

fun fastPrefixSum [] = []
  | fastPrefixSum L = 
    let
      	fun helpfun([], sum, newlist) = newlist
          | helpfun(x::L, sum, newlist) = helpfun(L, x+ sum, newlist @ [x + sum])
    in
      	helpfun(L, 0, [])
    end

(* treecompare: tree * tree -> order *)
fun treecompare (Empty, Node(_, x, _)) = LESS
  | treecompare (Node(_, x, _), Empty) = GREATER
  | treecompare (Empty, Empty) = EQUAL
  | treecompare (Node(_, x, _), Node(_, y, _)) = 
    case Int.compare(x,y) 
      	of LESS => LESS
        | EQUAL => EQUAL
        | GREATER => GREATER

fun changeorder (l,m,r) = 
	let 
		fun cmp (x,y):int = 
			case Int.compare(x,y) 
			of GREATER => 1
			| _ => 0
	in
		case (cmp(m,l), cmp(m,r), cmp(l,r))
		of (0, 0, _) => (l,m,r)
		| (0, 1, _) => (l,r,m)
		| (1, 0, _) => (m,l,r)
		| (1, 1, 0) => (m,l,r)
		| (1, 1, 1) => (l,r,m)
	end

(* SwapDown: tree -> tree *)
fun SwapDown Empty = Empty
  | SwapDown (Node(Empty, x, Empty)) = Node(Empty, x, Empty)
  | SwapDown (Node(Node(ll, L, lr), x, Empty)) = 
	(case Int.compare(L,x)
		of LESS => Node(Node(ll,x,lr),L,Empty)
		| _ => Node(Node(ll, L, lr), x, Empty))
  | SwapDown (Node(Empty, x, Node(rl,R,rr))) = 
	(case Int.compare(R,x)
		of LESS => Node(Empty, R, Node(rl,x,rr))
		| _ => Node(Empty, x, Node(rl,R,rr)))
  | SwapDown (Node(Node(ll, L, lr), x, Node( rl, R, rr ))) = 
	let 
		val (l,m,r) = changeorder(L,x,R)
	in
		Node((Node(ll, x, lr), m, Node( rl, r, rr )))
	end

(* heapify : tree -> tree  *)
fun heapify Empty = Empty
  | heapify (Node(Empty, x, Empty)) = Node(Empty, x, Empty)
  | heapify (Node(Node(ll, L, lr), x, Empty)) = 
	(case Int.compare(L,x)
		of LESS => Node(heapify(Node(ll, x, lr)), L, Empty)
		| _ => Node(heapify(Node(ll, L, lr)), x, Empty))
  | heapify ( Node( Empty, x, Node( rl, R, rr ) ) ) = 
	(case Int.compare(R,x)
		of LESS => Node(Empty, R, heapify(Node(rl, x, rr)))
		| _ => Node(Empty, x, heapify(Node(rl, R, rr))))
  | heapify (Node(Node(ll, L, lr), x, Node( rl, R, rr ))) = 
	let 
		val (l,x,r) = changeorder(L,x,R)
	in
		Node(heapify(Node(ll,l,lr)), x, heapify(Node(rl, r, rr)))
	end

