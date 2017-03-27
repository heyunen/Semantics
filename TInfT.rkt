#lang racket

;; Simply-typed Church-style (nominal) lambda-calculus
;; with integers and zero-comparison
;; Type inference

(require "pmatch.rkt")

;;
(define (error-msg? m)
  (and (pair? m)
       (eq? (car m) 'ERROR)))

(define error-msg
  (lambda (msg v)
    (list 'ERROR msg v)))

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

(define (TV? tv)
  (and (pair? tv)
       (eq? (car tv) 'TV)))

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

;; Type Environment
;; TVE
(define tve0
  (list 'TVE 0 '()))

;; Allocate a fresh type variable (see the first component of TVE)
;; TVE -> (Typ,TVE)
(define newtv
  (lambda (tve)
    (let ([n (list-ref tve 1)]
          [s (list-ref tve 2)])
      (cons (cons 'TV n) (list 'TVE (add1 n) s)))))

;; TVE -> TVarName -> Maybe Typ
(define tvlkup
  (lambda (tve tvarn)
    (define lookup
      (lambda (env x)
        (if (eq? env '())
            '()
            (if (eq? (caar env) x)
                (cadar env)
                (lookup (cdr env) x)))))
    (lookup (caddr tve) tvarn)))

;; TVE -> (TVarName,Typ) -> TVE
(define tvext
  (lambda (tve tvt)
    (let ([c (cadr tve)]
          [s (caddr tve)]
          [tv (car tvt)]
          [t (cdr tvt)])
      (list 'TVE c (cons `(,tv ,(atom t)) s)))))

;; Type variables are logic variables: hypothetical reasoning
;; TVE -> Typ -> Typ
(define tvsub
  (lambda (tve t)
    (cond
      [(Typ:>Typ? t) (let ([t1 (car t)] [t2 (caddr t)])
                       `(,(tvsub tve t1) :> ,(tvsub tve t2)))]
      [(TV? t) (let ([t1 (tvlkup tve (cdr t))])
                 (if (eq? t1 '())
                     t
                     (tvsub tve t1)))]
      [else t])))

;; `shallow' substitution; check if tv is bound to anything `substantial'
;; TVE -> Typ -> Typ
(define tvchase
  (lambda (tve t)
    (cond
      [(and (TV? t) (let ([t1 (tvlkup tve (cdr t))])
                      (if (eq? t1 '())
                          t
                          (tvchase tve t1))))]
      [else t])))

;; The unification. If unification failed, return the reason
(define unify
  (lambda (t1 t2 tve)
    (unify^ (tvchase tve t1) (tvchase tve t2) tve)))

;; If either t1 or t2 are type variables, they are definitely unbound
;; Typ -> Typ -> TVE -> Either String TVE
(define unify^
  (lambda (t1 t2 tve)
    (cond
      [(and (TInt? t1) (TInt? t2)) tve]
      [(and (Typ:>Typ? t1) (Typ:>Typ? t2)) (let ([t1a (car t1)]
                                                 [t1r (car (cddr t1))]
                                                 [t2a (car t2)]
                                                 [t2r (car (cddr t2))])
                                             (unify t1r t2r (unify t1a t2a tve)))]
      [(TV? t1) (unifyv (cdr t1) t2 tve)]
      [(TV? t2) (unifyv (cdr t2) t1 tve)]
      [else (error-msg `constant_mismatch (cons t1 t2))]
      )))

(define unifyv
  (lambda (v t tve)
    (cond
      [(TV? t) (let ([v2 (cdr t)])
                 (if (eq? v v2)
                     tve
                     (tvext tve `(,v ,(cons 'TV v2)))))]
      [else (if (occurs v t tve)
                `error
                (tvext tve `(,v ,t)))])))

(define occurs
  (lambda (v t tve)
    (cond
      [(TInt? t) #f]
      [(Typ:>Typ? t) (let ([t1 (car t)]
                           [t2 (car (cddr t))])
                       (or (occurs v t1 tve) (occurs v t2 tve)))]
      [(TV? t) (let* ([v2 (cdr t)]
                      [r (tvlkup tve v2)])
                 (if (eq? r '())
                     (eq? v v2)
                     (occurs v r tve)))])))

;; TEnv -> Term -> (TVE -> (Typ,TVE))
(define teval^
  (lambda (env term)
    (pmatch term
            [`,n (guard (integer? n)) (lambda (tve0)
                                        (cons TInt tve0))]
            [`,var (guard (symbol? var)) (lambda (tve0)
                                           (cons (lkup env var) tve0))]
            [`(+ ,e1 ,e2) (lambda (tve0)
                            (let* ([r1 ((teval^ env e1) tve0)]
                                   [t1 (car r1)]
                                   [tve1 (cdr r1)]
                                   [r2 ((teval^ env e2) tve1)]
                                   [t2 (car r2)]
                                   [tve2 (cdr r2)])
                              (cons TInt (unify t2 TInt (unify t1 TInt tve2)))))]
            [`(ifz ,e1 ,e2 ,e3) (lambda (tve0)
                                  (let* ([r1 ((teval^ env e1) tve0)]
                                         [t1 (car r1)]
                                         [tve1 (cdr r1)]
                                         [r2 ((teval^ env e2) tve1)]
                                         [t2 (car r2)]
                                         [tve2 (cdr r2)]
                                         [r3 ((teval^ env e3) tve2)]
                                         [t3 (car r3)]
                                         [tve3 (cdr r3)])
                                    (let ([tve4 (unify t1 TInt tve3)])
                                      (if (error-msg? tve4)
                                          (error 'teval "Trying to compare a non-integer to 0: ~s ~s" (cadr tve4) (caddr tve4))
                                          (cons t2 (unify t2 t3 tve4))))))]
            [`(lambda (,x) ,e) (lambda (tve0)
                                 (let* ([r1 (newtv tve0)]
                                        [tv (car r1)]
                                        [tve1 (cdr r1)]
                                        [r2 ((teval^ (ext env `(,x ,tv)) e) tve1)]
                                        [te (car r2)]
                                        [tve2 (cdr r2)])
                                   (cons `(,tv :> ,te) tve2)))]
            [`(,e1 ,e2) (lambda (tve0)
                          (let* ([r1 ((teval^ env e1) tve0)]
                                 [t1 (car r1)]
                                 [tve1 (cdr r1)]
                                 [r2 ((teval^ env e2) tve1)]
                                 [t2 (car r2)]
                                 [tve2 (cdr r2)]
                                 [r3 (newtv tve2)]
                                 [t1r (car r3)]
                                 [tve3 (cdr r3)])
                            (cons t1r (unify t1 `(,t2 :> ,t1r) tve3))))]
            )))

;; Resolve all type variables, as far as possible
;; TEnv -> Term -> Typ
(define teval
  (lambda (tenv e)
    (let* ([r1  ((teval^ tenv e) tve0)]
           [t (car r1)]
           [tve (cdr r1)])
      (tvsub tve t)

      )))

;; Tests
; '(((TV . 0) :> (TV . 0)) TVE 1 ())
; '((TV . 0) :> (TV . 0))
(teval env0 `(lambda (x) x))

; '(Int TVE 0 ())
; 'TInt
(teval env0 `(+ 1 1))

; '(((TV . 0) :> Int) TVE 1 ((0 Int)))
; '(Int :> Int)
(teval env0 `(lambda (x) (+ x 2)))

; '((TV . 1) TVE 2 ((1 Int) (0 Int)))
; 'Int
(teval env0 `((lambda (x) (+ x 2)) 1))

; '(((TV . 0) :> Int) TVE 1 ((0 Int)))
; '(Int :> Int)
(teval env0 `(lambda (x) (ifz x 1 (+ x 2))))

; '((TV . 0) :> (TV . 0))
(teval env0 `(lambda (x) x))

; '(((TV . 0) :> ((TV . 1) :> (TV . 2))) TVE 3 ((0 ((TV . 1) :> (TV . 2)))))
; '(((TV . 1) :> (TV . 2)) :> ((TV . 1) :> (TV . 2)))
(teval env0 `(lambda (x)
               (lambda (y)
                 (x y))))

; teval: unbound variable y
; (teval env0 `(lambda (x) (ifz x 1 y)))

; *** Exception: Trying to compare a non-integer to 0: constant mismatch: TInt :> TV 1 and TInt
; teval: Trying to compare a non-integer to 0: constant_mismatch ((Int :> (TV . 1)) . Int)
; (teval env0 `(lambda (x) (ifz x 1 (x 1))))