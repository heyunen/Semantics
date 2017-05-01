#lang racket

;; Dynamic scoping

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
      [`,x #:when (number? x) x]
      [`,x #:when (symbol? x) (apply-env env x)]
      [`(lambda (,x) ,t) `(lambda (,x) ,t)]
      [`(+ ,n ,m) (let ([v (eval n env)]
                        [w (eval m env)])
                    (+ v w))]
      [`(,f ,a) (match-let ([`(lambda (,x) ,b) (eval f env)])
                  (eval b (extend-env x a env)))]
      [`(let ((,x ,t)) ,b) (let ([v (eval t env)])
                             (eval b (extend-env x v env)))])))

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