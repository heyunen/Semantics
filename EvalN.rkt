#lang racket

;; Untyped (nominal) lambda-calculus with integers and the conditional

(require "pmatch.rkt")

;; env0 :: Env
(define env0 '())

;; lkup :: Env -> VarName -> Value
(define lkup
  (lambda (env x)
    (if (eq? env '())
        (error 'eval "unbound variable ~s" x)
        (if (eq? (caar env) x)
            (cadar env)
            (lkup (cdr env) x)))))

;; ext :: Env -> (VarName, Value) -> Env
(define ext
  (lambda (env x)
    (cons x env)))

;; Denotational semantics
;; eval :: Env -> Term -> Value
(define eval
  (lambda (env term)
    (pmatch term
            [`,n (guard (integer? n)) n]
            [`,var (guard (symbol? var)) (lkup env var)]
            [`(lambda (,x) ,e) (lambda (v) (eval (ext env `(,x ,v)) e))]
            [`(,e1 ,e2) (let ([v1 (eval env e1)] [v2 (eval env e2)]) (v1 v2))]
            [`(+ ,e1 ,e2) (let ([v1 (eval env e1)] [v2 (eval env e2)]) (+ v1 v2))]
            [`(ifz ,e1 ,e2 ,e3) (let ([v1 (eval env e1)])
                                  (if (eq? v1 0)
                                      (eval env e2)
                                      (eval env e3)))])))

;; Tests

(eval env0 `(lambda (x)
              (ifz x 1 (+ 2 x))))

(eval env0 `((lambda (x)
              (ifz x 1 (+ 2 x))) 2))

(eval env0 `((lambda (x)
              (ifz x 1 (+ 2 x))) 0))

;; (eval env0 `((lambda (x) (ifz x 1 (+ 2 x))) x)) -- unbound variable x