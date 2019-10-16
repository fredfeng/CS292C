#lang rosette

(define-symbolic x y integer?)

(assert (< x 2))

(asserts)

(pretty-display "SAT problem===================")
(define sol0 (solve (assert (and (> y 0) (< y 10)))))
(evaluate y sol0)

(define sol
    (optimize #:maximize (list (+ x y))
              #:guarantee (assert (and (> y 0) (< y 10)))))

(pretty-display "Optimization problem===================")

(evaluate x sol)

(evaluate y sol)