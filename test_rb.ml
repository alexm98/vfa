let test (n: int) =
 let rec f (j, t) = if j=0 then t
                    else f(j-1, RedBlackTree.insert (Random.int n) t)
  in let t1 = f(n,RedBlackTree.empty)
  in let rec g (j,count) = if j=0 then count
                       else if RedBlackTree.member (Random.int n) t1
                            then g(j-1,count+1)
                            else g(j-1,count)
  in let start = Sys.time()
  in let answer = g(n,0)
      in (answer, Sys.time() -. start)
