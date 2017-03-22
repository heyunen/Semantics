#lang racket

;; Simply-typed Church-style (nominal) lambda-calculus
;; with integers and zero-comparison
;; Type reconstruction, for all subterms

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

;; A virtual typed AST: associating a type to each subterm
;; Typs -> Typ
(define topterm
  (lambda (x)
    (list (cons '() x))))

;; Typs -> Typ
(define toptyp
  (lambda (ts)
    (cdar ts)))

;;
(define (union s1 s2)
  (cond
    ((equal? '() s1) s2)
    ((pair? s1)
     (let ((a (car s1))
           (d (cdr s1)))
       (cond
         ((member a s2) (union d s2))
         (else (cons a (union d s2))))))))

;; Int -> Typs -> Typs
(define shift
  (lambda (n ts)
    (if (eq? ts '())
        '()
        (let* ([t (car ts)]
               [k (car t)]
               [v (cdr t)])
          (cons (cons (cons n k) v) (shift n (cdr ts)))))))

;; Type reconstruction: abstract evaluation
;; teval :: TEnv -> Term -> Typ
(define teval
  (lambda (env term)
    (pmatch term
            [`,n (guard (integer? n)) (topterm TInt)]
            [`,var (guard (symbol? var)) (topterm (lkup env var))]
            [`(lambda ([: ,x ,t]) ,e) (let ([ts (teval (ext env `(,x ,t)) e)])
                                        (union (topterm `(,t :> ,(toptyp ts))) (shift 0 ts)))]
            [`(+ ,e1 ,e2) (let ([t1 (teval env e1)] [t2 (teval env e2)])
                            (cond
                              [(and (TInt? (toptyp t1)) (TInt? (toptyp t2))) (union (union (topterm TInt) (shift 0 t1)) (shift 1 t2))]
                              [else (error 'teval "Trying to add non-integers: ~s , ~s" t1 t2)]))]
            [`(ifz ,e1 ,e2 ,e3) (let* ([t1 (teval env e1)]
                                       [t2 (teval env e2)]
                                       [t3 (teval env e3)]
                                       [tr (union (union (shift 0 t1) (shift 1 t2)) (shift 2 t3))])
                                  (cond
                                    [(and (TInt? (toptyp t1)) (eq? (toptyp t2) (toptyp t3))) (union (topterm (toptyp t2)) tr)]
                                    [(TInt? t1) (error 'teval "Branches of IFZ have different types: ~s and ~s" (toptyp t2) (toptyp t3))]
                                    [else (error 'teval "Trying to compare a non-integer to 0: ~s" (toptyp t1))]))]
            [`(fix ,e) (let ([t (teval env e)])
                         (cond
                           [(Typ:>Typ? (toptyp t)) (let* ([f1 (car (toptyp t))]
                                                          [ta1 (car f1)]
                                                          [tb1 (car (cddr f1))]
                                                          [f2 (car (cddr (toptyp t)))]
                                                          [ta2 (car f2)]
                                                          [tb2 (car (cddr f2))])
                                                     (if (and (equal? ta1 ta2)
                                                              (equal? tb1 tb2))
                                                         (union (topterm `(,ta1 :> ,tb1)) (shift 0 t))
                                                         (error 'teval "Inappropriate type in Fix: ~s" (toptyp t))))]
                           [else (error 'teval "Inappropriate type in Fix: ~s" (toptyp t))]))] 
            ; t1a :> t1r
            [`(,e1 ,e2) (let ([t1 (teval env e1)] [t2 (teval env e2)])
                          (cond
                            [(Typ:>Typ? (toptyp t1)) (let ([t1a (car (toptyp t1))] [t1r (cddr (toptyp t1))])
                                                       (if (eq? t1a (toptyp t2))
                                                           (union (union (topterm (atom t1r)) (shift 0 t1)) (shift 1 t2))
                                                           (error 'teval "Applying a function of arg type ~s to argument of type ~s" t1a (toptyp t2))))]
                            [else (error 'teval "Trying to apply a non-function: ~s" (toptyp t1))]))])))

;; Tests
; [([],TInt :> TInt),([0],TInt),([0,0],TInt),([0,1],TInt),([0,2],TInt),([0,2,0],TInt),([0,2,1],TInt)]
; ((() Int :> Int) ((0) . Int) ((0 0) . Int) ((0 1) . Int) ((0 2) . Int) ((0 2 0) . Int) ((0 2 1) . Int))
(teval env0 `(lambda ([: x Int])
               (ifz x
                    1
                    (+ 2 x))))

; teval: Trying to apply a non-function: Int
(teval env0 `(lambda ([: x Int])
               (lambda ([: y Int])
                 (x y))))

; [([],(TInt :> TInt) :> (TInt :> TInt)),([0],TInt :> TInt),([0,0],TInt),([0,0,0],TInt :> TInt),([0,0,1],TInt)]
; ((() (Int :> Int) :> (Int :> Int)) ((0) Int :> Int) ((0 0) . Int) ((0 0 0) Int :> Int) ((0 0 1) . Int))
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

; [([],TInt :> (TInt :> TInt)),([0],(TInt :> (TInt :> TInt)) :> (TInt :> (TInt :> TInt))),([0,0],TInt :> (TInt :> TInt)),([0,0,0],TInt :> TInt),([0,0,0,0],TInt),([0,0,0,0,0],TInt),([0,0,0,0,1],TInt),([0,0,0,0,2],TInt),([0,0,0,0,2,0],TInt),([0,0,0,0,2,0,0],TInt :> TInt),([0,0,0,0,2,0,0,0],TInt :> (TInt :> TInt)),([0,0,0,0,2,0,0,1],TInt),([0,0,0,0,2,0,0,1,0],TInt),([0,0,0,0,2,0,0,1,1],TInt),([0,0,0,0,2,0,1],TInt),([0,0,0,0,2,1],TInt)]
; '((() Int :> (Int :> Int))
;  ((0) (Int :> (Int :> Int)) :> (Int :> (Int :> Int)))
;  ((0 0) Int :> (Int :> Int))
;  ((0 0 0) Int :> Int)
;  ((0 0 0 0) . Int)
;  ((0 0 0 0 0) . Int)
;  ((0 0 0 0 1) . Int)
;  ((0 0 0 0 2) . Int)
;  ((0 0 0 0 2 0) . Int)
;  ((0 0 0 0 2 0 0) Int :> Int)
;  ((0 0 0 0 2 0 0 0) Int :> (Int :> Int))
;  ((0 0 0 0 2 0 0 1) . Int)
;  ((0 0 0 0 2 0 0 1 0) . Int)
;  ((0 0 0 0 2 0 0 1 1) . Int)
;  ((0 0 0 0 2 0 1) . Int)
;  ((0 0 0 0 2 1) . Int))
(teval env0 `(fix (lambda ([: self (Int :> (Int :> Int))])
                    (lambda ([: x Int])
                      (lambda ([: y Int])
                        (ifz x
                             0
                             (+ ((self (+ x -1)) y) y)))))))