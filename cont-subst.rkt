#lang racket

;; substitute exp[x <- y]
(define substitute
  (lambda (x y exp)
    (match exp
      [`,a #:when (number? a) a]
      [`,a #:when (symbol? a) (if (eq? a x)
                                  y
                                  exp)]
      [`(+ ,n ,m) `(+ ,(substitute x y n) ,(substitute x y m))]
      [`(lambda (,v) ,b) (if (eq? x v)
                             exp
                             (let* ([$v (gensym v)]
                                    [$b (substitute v $v b)]
                                    [$$b (substitute x y $b)])
                               `(lambda (,$v) ,$$b)))]
      [`(,rator, rand) `(,(substitute x y rator) ,(substitute x y rand))]
      [`(let ((,a ,v)) ,b) `(let ((,(substitute x y a) ,(substitute x y v))) ,(substitute x y b))])))

(define eval
  (lambda (exp)
    (match exp
      [`,x #:when (symbol? x) x]
      [`,x #:when (number? x) x]
      [`(lambda (,x) ,t) `(lambda (,x) ,t)]
      [`(+ ,n ,m) (let ([v (eval n)])
                    (let ([w (eval m)])
                      (+ v w)))]
      [`(,f ,a) (match-let
                    ([`(lambda (,x) ,b) (eval f)])
                  (eval (substitute x a b)))]
      [`(let ((,x ,t)) ,b) (let ([v (eval t)])
                             (eval (substitute x v b)))])))

(eval '(let ([x 1])
         (let ([y (lambda (z) x)])
           (let ([x 3])
             (y 17)))))

(eval '(((lambda (x)
           (lambda (y)
             (+ x y))) 2) 3))