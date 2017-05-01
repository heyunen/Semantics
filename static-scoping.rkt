#lang racket

;; Static scoping

(define empty-env
  (lambda ()
    (lambda (y) (error 'value-of "unbound variable ~s" y))))

(define extend-env
  (lambda (id arg env)
    (lambda (var)
      (if (eq? id var)
          arg
          (apply-env env var)))))

(define apply-env
  (lambda (env var)
    (env var)))

(define eval
  (lambda (exp env)
    (match exp
      [`,x #:when (symbol? x) (match-let ([`(,t ,env^) (apply-env env x)])
                                (eval t env^))]
      [`,x #:when (number? x) `(,x ,env)]
      [`(lambda (,x) ,t) `((lambda (,x) ,t) ,env)]
      [`(+ ,n ,m) (match-let ([`(,v ,env1) (eval n env)]
                              [`(,w ,env2) (eval m env)])
                    `(,(+ v w) ,env))]
      [`(,f ,a) (match-let
                    ([`((lambda (,x) ,b) ,env^) (eval f env)])
                  (eval b (extend-env x (eval a env) env^)))]
      [`(let ((,x ,t)) ,b) (match-let ([`(,v ,env^) (eval t env)])
                             (eval b (extend-env x `(,v ,env^) env)))])))

(eval
   '(let ([x 1])
      (let ([y x])
        (let ([x 3])
          y)))
   (empty-env))

(eval
   '(let ([x 1])
      (let ([y (lambda (z) x)])
        (let ([x 3])
          (y 17))))
   (empty-env))