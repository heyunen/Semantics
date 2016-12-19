#lang racket

(require "pmatch.rkt")

;;
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