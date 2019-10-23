#lang racket
 

(provide search-sat dpll read-cnf)

; The procedures search-sat and dpll assume that a CNF formula is
; given as a list of clauses, where each clause is a list of non-zero
; integers representing positive or negative literals.  

; If f is satisfiable, returns a model of f given as a list of
; integers (positive or negative literals). Otherwise returns false.
(define (search-sat f)
  (let search ([vars (variables f)] [I (list)])
    (if (evaluate f I)
        I
        (match vars
          [(list) #f]
          [(list v vs ...)
           (or (search vs (cons v I))
               (search vs (cons (- v) I)))]))))

; If f is satisfiable, returns a model of f given as a list of
; integers (positive or negative literals). Otherwise returns false.
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

; Applies the unit rule to f with respect to the given literal.
(define (unit-rule lit f)
  (define -lit (- lit))
  (for/list ([clause f] #:unless (member lit clause))
    (match clause
      [`(,li ... ,(== -lit) ,lj ...) `(,@li ,@lj)]
      [_ clause])))


; Returns the variables in a CNF formula f represented as a
; list of lists of integers.
(define (variables f)
  (remove-duplicates (map abs (flatten f))))

; Returns true iff I is a model of the CNF formula f
; represented as a list of lists of integers.
(define (evaluate f I)
  (for/and ([c f])
    (for/or ([l c] #:when (member l I)) #t)))

; Returns a list of lists representation of a CNF formula
; in the standard DIMACS format.
(define (read-cnf file)
  (call-with-input-file file
    (lambda (port)
      (filter-map
       (lambda (ln)
         (and (not (string-prefix? ln "c"))
              (not (string-prefix? ln "p"))
              (map string->number (drop-right (string-split ln) 1))))
       (port->lines port)))))

(define f1 (read-cnf "test1.cnf"))
(define f2 (read-cnf "test2.cnf"))
;; This line should print the model: '(16 -17 -21 -28 -13 18 -31 -38 44 -8 -12 -27 40 23 -4 -3 -49 -34 -26 19 36 24 43 42 -5 20 -7 10 -41 46 -33 -37 32 6 25 -48 -9 2 35 22 50 -29 -1 11 -45 39 15 14 47 -30)
(time (dpll f1))
;; This following line should print: #f
(time (dpll f2))
