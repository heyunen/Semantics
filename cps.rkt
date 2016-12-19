#lang racket

(require "pmatch.rkt")

; Informally, to convert a program to CPS:
; 1. Add an extra argument k to each function.
; 2. Instead of returning a result in a function, pass the result to k.
; 3. Lift a nested function call out of its sub-expression by selecting a variable X to replace the function
; call, wrapping the expression with (lambda (X) . . . ), and providing the resulting (lambda X ) as
; the third argument to the function. For example, convert (add1 (f x )) to (f x (lambda (v) (add1 v))).
; Applications of primitive operations need no lifting.

(define id
  (lambda (v) v))

(define ctx0
  (lambda (v) `(k ,v)))

(define delta-b1?
  (lambda (x) (memq x `(add1 sub1 zero?))))

(define new-var
  (let ([n -1])
    (lambda ()
      (set! n (+ 1 n))
      (string->symbol
       (string-append "v" (number->string n))))))

(define cps
  (lambda (exp)
    (define cps1
      (lambda (exp ctx)
        (pmatch exp
                [`,x (guard (not (pair? x))) (ctx x)]
                [`(lambda (,x) ,body) (ctx `(lambda (,x k) ,(cps1 body ctx0)))]
                [`(,func ,arg) (cps1 func (lambda (x)
                                            (cps1 arg (lambda (x^)
                                                        (cond
                                                          [(delta-b1? x) `(,x ,x^)]
                                                          [else (let ([var (new-var)])
                                                                  `(,x ,x^ (lambda (,var) ,(ctx var))))
                                                                ])))))])))
    (cps1 exp id)))

;;; tests

(cps 'x)
; x

(cps '(lambda (x) x))
; (lambda (x k) (k x))

(cps '(f x))
; (f x (lambda (v0) v0))

(cps '(add1 (f x)))
; (f x (lambda (v0)
;        (add1 v0)))

(cps '((f x) 1))
; (f x (lambda (v0)
;        (v0 1 (lambda (v1)
;                v1))))
