#lang racket
(require "pmatch.rkt")

(define atom?
  (lambda (x)
    (and (not (pair? x)) (not (null? x)))))

                         
(define (union set1 set2)
  (cond
    ((eq? set1 null) set2)
     ((eq? set2 null) set1)
     (else (if (not (memv (car set1) set2))
                       (cons (car set1) (union (cdr set1) (remv (car set1) set2)))
                       (union (cdr set1) set2)))))


(define FV
  (lambda (expr)
    (pmatch expr
      [`,X (guard (atom? X)) `(,X)]
      [`(lambda (,X) ,M) (remv X (FV M))]
      [`(,M1 ,M2) (union (FV M1) (FV M2))])))


(FV `x)
(FV `(x (y x)))
(FV `(lambda (x) (x y)))
(FV `(z (lambda (z) z)))