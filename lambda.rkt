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


; <exp> ::=  <var>
;        |   (<exp> <exp>)
;        |   (lambda (<var>) <exp>)


;; substitute exp[x <- y]
(define substitute
  (lambda (x y exp)
    (pmatch exp
            [`,a (guard (atom? a)) (if (eq? a x)
                                       y
                                       exp)]
            [`(lambda (,v) ,b) (if (eq? x v)
                                   exp
                                   (let* ([$v (gensym v)]
                                          [$b (substitute v $v b)]
                                          [$$b (substitute x y $b)])
                                     `(lambda (,$v) ,$$b)))]
            [`(,rator, rand) `(,(substitute x y rator) ,(substitute x y rand))])))


(define (beta-reduce exp)
  (pmatch exp
    [`,a (guard (atom? a))       (error "cannot β-reduce variable")]
    [`(lambda (,v) ,b)           (error "cannot β-reduce λ-term")]
    [`((lambda (,v) ,b) ,arg)    (substitute v arg b)]
    [`(,_ ,_)                    (error "cannot β-reduce application")]))


(define (step/eager exp)
  (pmatch exp
          [`,a (guard (atom? a))                     exp]
          [`(lambda (,_) ,_)                         exp]
          [`((lambda (,_) ,_) (lambda (,_) ,_))      (beta-reduce exp)]
          [`((lambda (,v) ,b) ,a)                    (if (atom? a)
                                                         (beta-reduce exp)
                                                         `((lambda (,v) ,b) ,(step/eager a)))]
          [`(,f ,a)                                  `(,(step/eager f) ,a)]))


(define (step/lazy exp)
  (pmatch exp
          [`,a (guard (atom? a))                       exp]
          [`(lambda (,_) ,_)                           exp]
          [`((lambda (,v) ,b) ,a)                      `((lambda (,v) ,b) ,(step/eager a))]
          [`(,rator ,rand)                             `(,(step/eager rator) ,rand)]))


(define (eval/step step exp #:verbose [verbose? #f])
  (when verbose?
    (printf "step: ~a~n" exp))
  (let ([next (step exp)])
    (if (equal? next exp)
        exp
        (eval/step step next #:verbose verbose?))))


(eval/step step/eager `((lambda (x) x) (lambda (z) z)) #:verbose #t)
(eval/step step/eager `((lambda (f) (f f)) (lambda (g) (g g))) #:verbose #t)
(eval/step step/eager `((lambda (x) ((lambda (z) z) x)) (lambda (x) x)) #:verbose #t)
(eval/step step/eager `((((lambda (v)
                            (lambda (t)
                              (lambda (f)
                                ((v t) f))))
                          (lambda (x)
                            (lambda (y) x))) M) N)
           #:verbose #t)