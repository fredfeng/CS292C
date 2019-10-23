In this assignment, you need to complete the missing pieces in the DPLL algorithm for solving CNF formulars:
```
(define (dpll f)
  (define g (??? f))
  (match g
    [`((,lit) ...) lit]                         ; model
    [`(,_ ... () ,_ ...) #f]                    ; unsat
    [`((,assigned) ... (,lit ,_ ,_ ...) ,_ ...) ; search
     (let* ([undecided (drop g (length assigned))]
            [result    (??? (??? `((,lit) ,@undecided))
                           (??? `((,(- lit)) ,@undecided)))])
       (??? result `(,@assigned ,@result)))]))
       
       
; Applies BCP to f.
(define (bcp f)
  (match f
    [`(,ci ... (,lit) ,cj ...)
     `((,lit) ,@(??? (unit-rule lit `(,@ci ,@cj))))]
    [_ f]))
```                
Before you start this homework, you should understand the DIMACS format that is a standard interface to SAT solvers.      
The basic input format is as follows. At the top you can have comment lines that start with a c, like this:

>>c This line is a comment.

Then comes the problem line, which starts with a p and then says how many variables and clauses there are. For instance, here is a problem line that says this is a CNF problem with 3 variables and 4 clauses:

>>p cnf 3 4

Finally the clauses are listed. Each clause is represented as a list of numbers like 3 and -2. A positive number like 3 represents a positive occurrence of variable 3. A negative number like -2 represents a negated occurrence of variable 2.
The number 0 is treated in a special way: it is not a variable, but instead marks the end of each clause. This allows a single clause to be split up over multiple lines. For instance, the clause **¬x2 ∨ x3** is represented as:
>> -2 3 0

Happy hacking.

