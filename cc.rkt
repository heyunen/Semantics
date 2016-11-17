#lang scheme

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Syntax recognizers, extractors, and makers

;; Value
(define (val? m)
  (or (number? m)
      (func? m)
      (symbol? m)))

;; Function
(define (func? m)
  (and (list? m)
       (eq? 'lam (list-ref m 0))))

(define (func-var m)
  (list-ref m 1))

(define (func-body m)
  (list-ref m 2))

(define (make-func var body)
  (unless (symbol? var)
    (error 'make-func "variable is not a symbol: ~e" var))
  (list 'lam var body))

;; Application
(define (app? m)
  (and (list? m)
       (not (func? m))
       (not (primapp? m))))

(define (app-func m)
  (list-ref m 0))

(define (app-arg m)
  (list-ref m 1))

(define (make-app f a)
  (list f a))

;; Primitive operation
(define (primapp? m)
  (and (list? m)
       (let ([o (list-ref m 0)])
         (member o '(+ - =)))))

(define (primapp-op m)
  (list-ref m 0))

(define (primapp-arg1 m)
  (list-ref m 1))

(define (primapp-arg2 m)
  (list-ref m 2))

(define (make-primapp o a1 a2)
  (unless (member o '(+ - =))
    (error 'make-primapp "operation is not +, -, or =: ~e" o))
  (list o a1 a2))

;; Hole
(define hole '*)

(define (hole? m)
  (eq? m hole))

;; State
(define-struct state (m e))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The one-step evaluator

(define (next-state s)
  (let ([m (state-m s)]
        [e (state-e s)])
    (cond
     ;; Rule 1
     [(and (app? m)
           (not (val? (app-func m))))
      (make-state (app-func m)
                  (replace e hole (make-app hole (app-arg m))))]
     ;; Rule 2
     [(and (app? m)
           (not (val? (app-arg m))))
      (make-state (app-arg m)
                  (replace e hole (make-app (app-func m) hole)))]
     ;; Rule 3
     [(and (primapp? m)
           (not (val? (primapp-arg1 m))))
      (make-state (primapp-arg1 m)
                  (replace e hole (make-primapp (primapp-op m) hole (primapp-arg2 m))))]
     [(and (primapp? m)
           (not (val? (primapp-arg2 m))))
      (make-state (primapp-arg2 m)
                  (replace e hole (make-primapp (primapp-op m) (primapp-arg1 m) hole)))]
     ;; Rule beta-v
     [(and (app? m)
           (func? (app-func m))
           (val? (app-arg m)))
      (make-state (substitute (func-body (app-func m))
                              (func-var (app-func m))
                              (app-arg m)) e)]
     ;; Rule delta
     [(and (primapp? m)
           (val? (primapp-arg1 m))
           (val? (primapp-arg2 m)))
      (make-state (apply-op (primapp-op m)
                            (primapp-arg1 m)
                            (primapp-arg2 m))
                  e)]
     ;; Hole in the context
     [(val? m)
      (let ([h (hole-expression e)])
        (cond
          ;; Rule 4
          [(and (app? h)
                (hole? (app-arg h)))
           (make-state (make-app (app-func h) m)
                       (replace e h hole))]
          ;; Rule 5
          [(and (app? h)
                (hole? (app-func h)))
           (make-state (make-app m (app-arg h))
                       (replace e h hole))]
          ;; Rule 6
          [(and (primapp? h)
                (hole? (primapp-arg1 h)))
           (make-state (make-primapp (primapp-op h) (primapp-arg2 h) m)
                       (replace e h hole))]
          [(and (primapp? h)
                (hole? (primapp-arg2 h)))
           (make-state (make-primapp (primapp-op h) (primapp-arg1 h) m)
                       (replace e h hole))]
          ;; Error
          [else (error 'next-state "no recognized context around hole: ~e" e)]))]
     ;; Error
     [else (error 'next-state "stuck: ~e" m)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Context replacer

;; Puts a hole in place of a sub-context, or a context of expression
;; in place of a hole.
;;  (replace (make-app hole 5) hole (make-func 'x 'x))  = (make-app (make-func 'x 'x) 5)
;;  (replace (make-app (make-func 'x hole) 5) (make-func 'x hole) hole)  = (make-app hole 5)

(define (replace e old new)
  (cond
   [(equal? e old) new]
   [(app? e) (make-app
              (replace (app-func e) old new)
              (replace (app-arg e) old new))]
   [(primapp? e) (make-primapp
                  (primapp-op e)
                  (replace (primapp-arg1 e) old new)
                  (replace (primapp-arg2 e) old new))]
   [(func? e) (make-func (func-var e)
                         (replace (func-body e) old new))]
   [(number? e) e]
   [(symbol? e) e]
   [else (error 'replace "ill-formed expression: ~e" e)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Context extractor

;; Gets the expression in E that wraps a hole, or returns #f
;;  if there's no wrapped hole in the expression.
;; Examples:
;;  (hole-expression (make-app hole 10)) = (make-app hole 10)
;;  (hole-expression (make-app 12 (make-app hole 10))) = (make-app hole 10)
;;  (hole-expression (make-app 0 10)) = #f
;;  (hole-expression hole) = #f

(define (hole-expression e)
  (cond
    [(app? e)
     (cond
       ;; ([] M) or (M [])
       [(or (hole? (app-func e)) (hole? (app-arg e))) e]
       [else
        (or (hole-expression (app-func e))
            (hole-expression (app-arg e)))])]
    [(primapp? e)
     (cond
       ;; (o [] M) or (o M [])
       [(or (hole? (primapp-arg1 e)) (hole? (primapp-arg2 e))) e]
       [else
        (or (hole-expression (primapp-arg1 e))
            (hole-expression (primapp-arg2 e)))])]
    [else #f]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Substitute m[v <- x]

(define (substitute m x v)
  (cond
    [(eq? m x) v]
    [(app? m) (make-app (substitute (app-func m) x v)
                        (substitute (app-arg m) x v))]
    [(primapp? m) (make-primapp (primapp-op m)
                                (substitute (primapp-arg1 m) x v)
                                (substitute (primapp-arg2 m) x v))]
   [(func? m)
    (if (eq? x (func-var m))
        m
        ;; rename formal var, if necessary
        (let ([m2 (if (member (func-var m) (free-vars v null))
                      ;; rename
                      (let ([v2 (gensym)])
                        (make-func v2 (substitute (func-body m) (func-var m) v2)))
                      ;; no rename needed
                      m)])
          (make-func (func-var m2)
                     (substitute (func-body m2) x v))))]
   [(number? m) m]
   [(symbol? m) m]
   [else (error 'substitute "ill-formed expression: ~e" m)]))

(define (free-vars m bound)
  (cond
    [(symbol? m) (if (memq m bound)
                     null
                     (list m))]
    [(app? m) (append (free-vars (app-func m) bound)
                      (free-vars (app-arg m) bound))]
    [(primapp? m) (append (free-vars (primapp-arg1 m) bound)
                          (free-vars (primapp-arg2 m) bound))]
    [(func? m) (free-vars (func-body m)
                          (cons (func-var m) bound))]
    [else null]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The delta function

(define (apply-op o a1 a2)
  (cond
   [(eq? o '+) (+ a1 a2)]
   [(eq? o '-) (- a1 a2)]
   [(eq? o '=) (if (= a1 a2)
		   '(lam x (lam y (x 0)))
		   '(lam x (lam y (y 0))))]
   [else (error 'apply-op "unrecognized op: ~e" o)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The evaluation function:

(define (print-state s)
  (printf "<~a, ~a>" (state-m s) (state-e s)))

(define (show-eval s)
  (if (and (val? (state-m s))
	   (hole? (state-e s)))

      (begin
        (print-state s)
        (printf "~n~nDone~n~n"))

      (begin
	;; Print initial state
	(print-state s)
	(printf " |->~n~n")
	(let ([s2 (next-state s)])
	  ;; Keep going
          (show-eval s2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests

(define example1 '(+ (- 1 0) (+ 2 (- 4 3))))
(show-eval (make-state example1 hole))

(define example2 '((lam y y) ((lam x (+ x 5)) 12)))
(show-eval (make-state example2 hole))

(define Y '(lam f
		(lam x
		     (((lam g (f (lam x ((g g) x))))
		       (lam g (f (lam x ((g g) x)))))
		      x))))

(define sum (make-app Y
		      '(lam s
			    (lam x
				 (((= x 0)
                                   (lam d 0))
				  (lam d (+ x (s (- x 1)))))))))

(define example3 (make-app sum 3))
(show-eval (make-state example3 hole))

(define example4 (make-app
                  (make-app '(lam f
                                  (lam x (f x)))
                            '(lam y
                                  (+ y y)))
                  1))
(show-eval (make-state example4 hole))