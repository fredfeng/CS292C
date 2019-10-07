#lang rosette


;; n is the number of examples you need
(define (print-examples n)
  (define-symbolic x integer?)

  (for/fold ([examples '()])
            ([i (in-range n)])
    (define y (* 2 x))
    (define solution
      (solve (assert (> x y))))
    (if (sat? solution)
        (let ([x-value (evaluate x solution)])
          (assert (not (= x x-value)))
          (cons x-value examples))
        examples)))