#lang rosette

; ----- Modified based on Emina's version. -----;

(require 
 rosette/query/debug 
 rosette/lib/render 
 rosette/lib/synthax
 (prefix-in $ (only-in rosette bveq bvslt bvsgt bvsle bvsge bvult bvugt bvule bvuge))
 (only-in racket [eval racket/eval]))

(define-namespace-anchor bvlang)
(define ns (namespace-anchor->namespace bvlang))
(define (eval form) (racket/eval form ns))

; ----- BV raw syntax -----;

; The def macro turns a BV program into a procedure that invokes the
; BV interpreter on the provided inputs.
(define-syntax-rule (def id ([idx r] ...) (out op in ...) ...)
  (define (id r ...)
    (interpret `((out op ,in ...) ...) `(,r ...))))

(define-syntax (relax-reg stx)
  (syntax-case stx ()
    [(_ in) (with-syntax ([iden (syntax/loc #'in identity)])
              (syntax/loc #'in (iden in)))]))

; The def/debug macro is the same as def, except that it marks the
; defined procedure as a candidate for debugging.
(define-syntax-rule (def/dbg id ([idx r] ...) (out op in ...) ...)
  (define/debug (id r ...)
    (interpret `((out op ,(relax-reg in) ...) ...) `(,r ...))))

; ----- BV semantics -----;

; BV comparison operators return 1/0 instead of #t/#f.
; Tj=he language is similar to the one defined in this paper:
; https://dl.acm.org/citation.cfm?id=1993506
(define int32? (bitvector 32))
(define (int32 c) (bv c int32?))
(define register? integer?)

(define-syntax-rule (bool->bv b) (if b (int32 1) (int32 0)))

(define (bvredor x)  (bveq (bveq x (int32 0)) (int32 0)))
(define (bvredand x) (bveq x (int32 -1)))

(define-syntax-rule (define-comparators [id op] ...)
  (begin
    (define (id x y) (bool->bv (op x y))) ...))

(define-comparators
  [bveq $bveq] 
  [bvslt $bvslt] [bvult $bvult]
  [bvsle $bvsle] [bvule $bvule]
  [bvsgt $bvsgt] [bvugt $bvugt]
  [bvsge $bvsge] [bvuge $bvuge])


; Global registers.
(define memory          
  (let ([m (vector)])
    (case-lambda [() m]
                 [(size) (set! m (make-vector size #f))])))

 ; Returns the contents of the register idx.    
(define (load idx)     
  (vector-ref (memory) idx))

; Stores val in the register idx.
(define (store idx val) 
  (vector-set! (memory) idx val))

; Returns the contents of the last register.   
(define (last)          
  (sub1 (vector-length (memory))))

; Creates the registers for the given program and input.
(define (make-registers prog inputs) 
  (memory (+ (length prog) (length inputs)))
  (for ([(in idx) (in-indexed inputs)])
    (store idx in)))

; The BV interpreter.
(define (interpret prog inputs)
  (make-registers prog inputs) 
  (for ([stmt prog])
    (match stmt
      [(list out opcode in ...)
       (define op (eval opcode))
       (define args (map load in))
       (store out (apply op args))]))  
  (load (last)))

; FIXME: The BV verifier.
(define (ver impl spec)
  (define-symbolic* in int32? [(procedure-arity spec)])
  ; please write your code here.

)

; FIXME: The BV synthesizer.
(define (syn impl spec)
  (define-symbolic* in int32? [(procedure-arity spec)])
  ; please write your code here.

)

; ----- BV demo -----;
(define (bvmax x y)
  (if (equal? (bvsge x y) (int32 1)) x y))

(def/dbg bvmax0 
  ([0 r0] [1 r1]) 
  (2 bvsge 0 1)
  (3 bvneg 2)
  (4 bvxor 0 2)
  (5 bvand 3 4)
  (6 bvxor 1 5))

(def bvmax1
  ([0 r0] [1 r1]) 
  (2 bvsge 0 1)
  (3 bvneg (??))
  (4 bvxor 0 (??))
  (5 bvand 3 4)
  (6 bvxor (??) 5))



