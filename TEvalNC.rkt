#lang racket

;; Simply-typed Church-style (nominal) lambda-calculus
;; with integers and zero-comparison
;; Type checking

(require "pmatch.rkt")

; (Int) -> Int
(define atom
  (lambda (x)
    (if (eq? (length x) 1)
        (car x)
        x)))

;;
(define TInt `Int)

(define TInt?
  (lambda (t)
    (eq? t TInt)))

; Typ :> Typ
(define (Typ:>Typ? t)
  (and (list? t)
       (eq? (list-ref t 1) `:>)))

;; env0 :: TEnv
(define env0 '())

;; lkup :: TEnv -> VarName -> Typ
(define lkup
  (lambda (env x)
    (if (eq? env '())
        (error 'teval "unbound variable ~s" x)
        (if (eq? (caar env) x)
            (cadar env)
            (lkup (cdr env) x)))))

;; ext :: TEnv -> (VarName,Typ) -> TEnv
(define ext
  (lambda (env x)
    (cons x env)))

;; Type reconstruction: abstract evaluation
;; teval :: TEnv -> Term -> Typ
(define teval
  (lambda (env term)
    (pmatch term
            [`,n (guard (integer? n)) TInt]
            [`,var (guard (symbol? var)) (lkup env var)]
            [`(lambda ([: ,x ,t]) ,e) `(,t :> ,(teval (ext env `(,x ,t)) e))]
            [`(+ ,e1 ,e2) (let ([t1 (teval env e1)] [t2 (teval env e2)])
                            (cond
                              [(and (TInt? t1) (TInt? t2)) TInt]))]
            [`(ifz ,e1 ,e2 ,e3) (let ([t1 (teval env e1)] [t2 (teval env e2)] [t3 (teval env e3)])
                                  (cond
                                    [(and (TInt? t1) (eq? t2 t3)) t3]
                                    [(TInt? t1) (error 'teval "Branches of IFZ have different types: ~s and ~s" t2 t3)]
                                    [else (error 'teval "Trying to compare a non-integer to 0: ~s" t1)]))]
            ; ((Int :> (Int :> Int)) :> (Int :> (Int :> Int)))
            ; ((ta1 :> tb1) :> (ta2 :> tb2)) | ta1 == ta2 && tb1 == tb2 -> ta1 :> tb1
            [`(fix ,e) (let ([t (teval env e)])
                         (cond
                           [(Typ:>Typ? t) (let* ([f1 (car t)]
                                                 [ta1 (car f1)]
                                                 [tb1 (car (cddr f1))]
                                                 [f2 (car (cddr t))]
                                                 [ta2 (car f2)]
                                                 [tb2 (car (cddr f2))])
                                            (if (and (equal? ta1 ta2)
                                                     (equal? tb1 tb2))
                                                `(,ta1 :> ,tb1)
                                                (error 'teval "Inappropriate type in Fix: ~s" t)))]
                           [else (error 'teval "Inappropriate type in Fix: ~s" t)]))]                 
            ; t1a :> t1r
            [`(,e1 ,e2) (let ([t1 (teval env e1)] [t2 (teval env e2)])
                          (cond
                            [(Typ:>Typ? t1) (let ([t1a (car t1)] [t1r (cddr t1)])
                                              (if (eq? t1a t2)
                                                  (atom t1r)
                                                  (error 'teval "Applying a function of arg type ~s to argument of type ~s" t1a t2)))]
                            [else (error 'teval "Trying to apply a non-function: ~s" t1)]))]
            )))

;; Tests

; Int :> Int
(teval env0 `(lambda ([: x Int])
               (ifz x
                    1
                    (+ 2 x))))

; *** Exception: Trying to apply a non-function: Int
(teval env0 `(lambda ([: x Int])
               (lambda ([: y Int])
                 (x y))))

; ((Int :> Int) :> (Int :> Int))
(teval env0 `(lambda ([: x (Int :> Int)])
               (lambda ([: y Int])
                 (x y))))

; teval: unbound variable y
(teval env0 `(lambda ([: x Int])
               (ifz x
                    1
                    y)))

; teval: Trying to apply a non-function: Int
(teval env0 `(lambda ([: x Int])
               (ifz x
                    1
                    (x 1))))

; teval: Trying to compare a non-integer to 0: (Int :> Int)
(teval env0 `(lambda ([: x (Int :> Int)])
               (ifz x
                    1
                    (x 1))))

; teval: unbound variable y
(teval env0 `((lambda ([: x Int])
                1) y))

; teval: Applying a function of arg type Int to argument of type (Int :> Int)
(teval env0 `(lambda ([: y (Int :> Int)])
               (y y)))

; (TInt :> (TInt :> TInt)) :> TInt
(teval env0 `(lambda ([: self (Int :> (Int :> Int))])
               ((self 1) 2)))

; (TInt :> (TInt :> (TInt :> TInt)))
(teval env0 `(lambda ([: self (Int :> (Int :> (Int :> Int)))])
               ((self 1) 2)))

; (TInt :> (TInt :> TInt)) :> (TInt :> (TInt :> TInt))
; TInt :> (TInt :> TInt)

; ((Int :> (Int :> Int)) :> (Int :> (Int :> Int)))
; (Int :> (Int :> Int))
(teval env0 `(fix (lambda ([: self (Int :> (Int :> Int))])
                    (lambda ([: x Int])
                      (lambda ([: y Int])
                        (ifz x
                             0
                             (+ ((self (+ x -1)) y) y)))))))