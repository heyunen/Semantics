#lang racket
(require "pmatch.rkt")


(define atom?
  (lambda (x)
    (and (not (pair? x)) (not (null? x)))))

                         
(define union
  (lambda (ls1 ls2)
    (cond
      [(null? ls1) ls2]
      [(memv (car ls1) ls2) (union (cdr ls1) ls2)]
      [else (cons (car ls1) (union (cdr ls1) ls2))])))


(define FV
  (lambda (expr)
    (pmatch expr
            [`,X (guard (atom? X)) `(,X)]
            [`(lambda (,X) ,M) (remv X (FV M))]
            [`(,M1 ,M2) (union (FV M1) (FV M2))])))


; '(x)
(FV `x)
; '(y x)
(FV `(x (y x)))
; '(y)
(FV `(lambda (x) (x y)))
; '(z)
(FV `(z (lambda (z) z)))
