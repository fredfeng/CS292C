The following is the grammar for the **BV** language:

    Prog := Stmt* 
    Stmt := (define id Expr) | (store id Expr) (load id)
    Expr := id | const | (unary-op Expr) |
             (binary-op Expr Expr) | (nary-op Expr+)
    unary-op := bvneg | bvnot
    binary-op := = | bvule | bvult | bvuge | bvugt | bvsle | bvslt | bvsge | bvsgt |
                    bvsdiv | bvsrem | bvshl | bvlshr | bvashr | bvsub
    nary-op := bvor | bvand | bvxor | bvadd | bvmul
    id := identifier
    const := 32-bit integer | true | false
                
      
      
      
We first provide a pre-defined **bvmax** function:
                          
    (define (bvmax x y)
        (if (equal? (bvsge x y) (int32 1)) x y))
        

The above implementation is straightforward but not efficient. We'd like to implement an equivalent version 
without using **if-else** statement.

Task 1: Verifying the equivalence between **bvmax** and **bvmax0**. In particular, 
complete the **ver** function in [hw1.rkt](hw1.rkt) using the **verify** API in Rosette. 
If they are not equivalent, please print a counter-example.
    
    (def/dbg bvmax0 
      ([0 r0] [1 r1]) 
      (2 bvsge 0 1)
      (3 bvneg 2)
      (4 bvxor 0 2)
      (5 bvand 3 4)
      (6 bvxor 1 5))

Task 2: Synthesizing the **bvmax1** function such that **bvmax1** and **bvmax** are equivalent.
In particular, complete the **syn** function in [hw1.rkt](hw1.rkt) using the **synthesize** API in Rosette.

    (def bvmax1
      ([0 r0] [1 r1]) 
      (2 bvsge 0 1)
      (3 bvneg (??))
      (4 bvxor 0 (??))
      (5 bvand 3 4)
      (6 bvxor (??) 5))
      
      
