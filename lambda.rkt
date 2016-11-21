#lang racket

; <exp> ::=  <var>
;        |   (<exp> <exp>)
;        |   (λ (<var>) <exp>)


(define (gen-eq? value)
  (λ (value*)
    (eq? value value*)))

(define (substitute x y exp)
  (match exp
    [(? (gen-eq? x)) y]
    [(? symbol?)     exp]
    
    [`(λ (,(? (gen-eq? x))) ,_)     exp]
    [`(λ (,v) ,b)
     
     (define $v (gensym v))
     
     (define $b (substitute v $v b))
     
     (define $$b (substitute x y $b))
     
     `(λ (,$v) ,$$b)]
    
    [`(,f ,a)
     `(,(substitute x y f) ,(substitute x y a))]))


#;(substitute 'x 'y '(λ (a) ((+ a) x)))

#;(substitute 'x 'y '(λ (y) x))




(define (β-reduce exp)
  (match exp
    [(? symbol?)            (error "cannot β-reduce variable")]
    [`(λ (,v) ,b)           (error "cannot β-reduce λ-term")]
    [`((λ (,v) ,b) ,arg)    (substitute v arg b)]
    [`(,_ ,_)               (error "cannot β-reduce application")]))

(define (step/eager exp)
  (match exp
    [(? symbol?)                     exp]
    [`(λ (,_) ,_)                    exp]
    [`((λ (,_) ,_) ,(? symbol?))     (β-reduce exp)]
    [`((λ (,_) ,_) (λ (,_) ,_))      (β-reduce exp)]
    [`((λ (,v) ,b) ,a)              `((λ (,v) ,b) ,(step/eager a))]
    [`(,f ,a)                       `(,(step/eager f) ,a)]))

(define (step/lazy exp)
  (match exp
    [(? symbol?)                     exp]
    [`(λ (,_) ,_)                    exp]
    #;[`((λ (,_) ,_) ,(? symbol?))     (β-reduce exp)]
    #;[`((λ (,_) ,_) (λ (,_) ,_))      (β-reduce exp)]
    [`((λ (,v) ,b) ,a)              `((λ (,v) ,b) ,(step/eager a))]
    [`(,f ,a)                       `(,(step/eager f) ,a)]))

(define (eval/step step exp #:verbose [verbose? #f])
  (when verbose?
    (printf "step: ~a~n" exp))
  (let ([next (step exp)])
    (if (equal? next exp)
        exp
        (eval/step step next #:verbose verbose?))))

(eval/step step/eager '((λ (x) x) (λ (z) z)) #:verbose #t)

(eval/step step/eager '((λ (f) (f f)) (λ (g) (g g))) #:verbose #t)

(eval/step step/lazy `((((λ  (v)
                            (λ  (t)
                              (λ  (f)
                                ((v t) f))))
                          (λ  (x)
                            (λ  (y) x))) M) N) #:verbose #t)


;(eval/step step/eager '((λ (f) (f (f f))) (λ (g) (g (g g)))) #:verbose #t)


; <exp> ::=  <var>
;        |   <number>
;        |   #t | #f
;        |   (<exp> <exp> ...)
;        |   (λ (<var> ...) <exp>)
;        |   (let ((<var> <exp>) ...) <exp>)
;        |   (if <exp> <exp> <exp>)
;        |   (<prim> <exp> ...)


(define (atom? exp)
  (or (symbol? exp)
      (number? exp)
      (boolean? exp)))

(define (irreducible? exp)
  (match exp
    [(? atom?)        #t]
    [`(λ ,vars ,body) #t]
    [else             #f]))

(define (prim? sym)
  (case sym
    [(+ * - =) #t]
    [else      #f]))


(define (exp-map-bu f exp)
  (match exp
    [(? symbol?)       (f exp)]
    [(? number?)       (f exp)]
    [(? boolean?)      (f exp)]
    [`(λ ,vars ,body)  (f `(λ ,vars ,(exp-map-bu f body)))]
    
    [`(let ,(list `(,vars ,args) ...) ,body)
     (f `(let ,(map list vars (map (λ (x) (exp-map-bu f x)) args)) ,(exp-map-bu f body)))]
    
    [`(if ,cond ,cons ,alt) (f `(if ,(exp-map-bu f cond)
                                    ,(exp-map-bu f cons)
                                    ,(exp-map-bu f alt)))]
    
    [`(,(? prim?) . ,args)  (f `(,(car exp) ,@(map (λ (x) (exp-map-bu f x)) args)))]
    
    [`(,_ . ,args)          (f (map (λ (x) (exp-map-bu f x)) exp))]
   
    [else               (error "unknown expression type")]))
  

(define (iterate/fix f z)
  (let ((next (f z)))
    (if (equal? next z)
        z
        (iterate/fix f next))))


(define (desugar-let-locally exp)
  (match exp
    [`(let ,(list `(,vars ,args) ...) ,body)
     `((λ ,vars ,body) ,@args)]
    
    [else exp]))

(define (desugar-let-once exp)
  (exp-map-bu desugar-let-locally exp))

(define (desugar-let exp)
  (iterate/fix desugar-let-once exp))



#;(desugar-let
 '(let ((x 3) (y 4))
    (let ((y 5))
      (+ x y)))) 


(define (subst x y exp)
  (match exp
    [(? (gen-eq? x))  y]
    [(? atom?)        exp]
    
    [`(λ ,vars ,body)
     (if (set-member? (apply set vars) x)
         `(λ ,vars ,body)
         `(λ ,vars ,(subst x y body)))]
    
    [`(if ,cond ,cons ,alt)
     `(if ,(subst x y cond)
          ,(subst x y cons)
          ,(subst x y alt))]

    [`(,(? prim?) . ,args)
     `(,(car exp) ,@(map (λ (a) (subst x y a)) args))]

    
    [`(,f . ,args)
     (map (λ (a) (subst x y a)) exp)]))


(define (δ-reduce op args)
  (case op
    [(+) (apply + args)]
    [(-) (apply - args)]
    [(*) (apply * args)]
    [(=) (apply = args)]))

(define (step exp)
  (match exp
    [(? irreducible?)       exp]
     
    [`(if #f ,cons ,alt)    alt]
    
    [`(if ,(? irreducible?) ,cons ,alt) cons]
    
    [`(if ,cond ,cons ,alt)
     `(if ,(step cond) ,cons ,alt)]
    
    [(list (and op (? prim?)) (and args (? irreducible?)) ...)
     (δ-reduce op args)]
    
    [(list (and op (? prim?)) args)
     `(,op ,@(map step args))]
    
    [(list `(λ ,vars ,body) (and args (? irreducible?)) ...)
     (for/fold
         ([body body])
         ([v    vars]
          [a    args])
       (subst v a body))]
    
    [`(,f . ,args)  (map step exp)]))
    


#;(eval/step #:verbose #t step
 (desugar-let
  '(let ([f (λ (x) (+ x 1))]
         [g (λ (a b) (* a b))])
     (g (f (f (f 0)))
        10))))