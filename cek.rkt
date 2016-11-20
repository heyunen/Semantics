#lang scheme

;; CEK Machine
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Syntax recognizers, extractors, and makers

;;
(define (val? m)
  (or (number? m)
      (func? m)
      (symbol? m)))

;;
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

;;
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

;;
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

;;
;(define-struct closure (m e))
(define-struct closure(m e)
  #:property prop:custom-write
  (lambda (closure port write?)
    (fprintf port (if write? "<~s, ~s>" "<~a, ~a>")
             (closure-m closure) (closure-e closure))))

;;
;(define-struct mtK ())
(define-struct mtK()
  #:property prop:custom-write
  (lambda (mtK port write?)
    (fprintf port "mt")))

;(define-struct funK (v k))
(define-struct funK(vcl k)
  #:property prop:custom-write
  (lambda (funK port write?)
    (fprintf port (if write? "<~s, ~s>" "<~a, ~a>")
             (funK-vcl funK) (funK-k funK))))

;(define-struct argK (n k))
(define-struct argK(ncl k)
  #:property prop:custom-write
  (lambda (argK port write?)
    (fprintf port (if write? "<~s, ~s>" "<~a, ~a>")
             (argK-ncl argK) (argK-k argK))))

;(define-struct primargK (o n k))
(define-struct primargK(o ncl k)
  #:property prop:custom-write
  (lambda (primargK port write?)
    (fprintf port (if write? "<~s, ~s, ~s>" "<~a, ~a, ~a>")
             (primargK-o primargK) (primargK-ncl primargK) (primargK-k primargK))))

;(define-struct primK (o v k))
(define-struct primK(o vcl k)
  #:property prop:custom-write
  (lambda (primK port write?)
    (fprintf port (if write? "<~s, ~s, ~s>" "<~a, ~a, ~a>")
             (primK-o primK) (primK-vcl primK) (primK-k primK))))

;;
(define-struct state (cl k))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The one-step evaluator

(define (next-state s)
  (let* ([cl (state-cl s)]
        [m (closure-m cl)]
        [e (closure-e cl)]
        [k (state-k s)])
    (cond
      ;; cek1
      [(app? m)
       (make-state (make-closure (app-func m) e)
                   (make-argK (make-closure (app-arg m) e) k))]
      ;; cek2
      [(primapp? m)
       (make-state (make-closure (primapp-arg1 m) e)
                   (make-primargK (primapp-op m)
                                  (make-closure (primapp-arg2 m) e) k))]
      ;; cek7
      [(symbol? m)
       (make-state (lookup m e) k)]      
      ;; cek3
      [(funK? k)
       (make-state (make-closure (func-body (closure-m (funK-vcl k)))
                                 (extend (closure-e (funK-vcl k))
                                         (func-var (closure-m (funK-vcl k)))
                                         cl))
                   (funK-k k))]
      ;; cek4
      [(argK? k)
       (make-state (argK-ncl k) (make-funK cl (argK-k k)))]
      ;; cek5
      [(primK? k)
       (make-state (make-closure (apply-op (primK-o k)
                                           (closure-m (primK-vcl k))
                                           m)
                                 empty)
                   (primK-k k))]
      ;; cek6
      [(primargK? k)
       (make-state (primargK-ncl k)
                   (make-primK (primargK-o k) cl (primargK-k k)))]
     [else (error 'next-state "stuck: ~e" m)])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Environments

(define empty null)
;(define-struct bind (var vcl))
(define-struct bind(var vcl)
  #:property prop:custom-write
  (lambda (bind port write?)
    (fprintf port (if write? "<~s, ~s>" "<~a, ~a>")
             (bind-var bind) (bind-vcl bind))))

(define (lookup m e)
  (cond
    [(null? e) (error 'lookup "Couldn't find ~e in environment" m)]
    [(eq? m (bind-var (car e)))  (bind-vcl (car e))]
    [else (lookup m (cdr e))]))

(define (extend e m vcl)
  (cond
    [(null? e) (list (make-bind m vcl))]
    [(eq? m (bind-var (car e))) (cons (make-bind m vcl)
                                      (cdr e))]
    [else (cons (car e) (extend (cdr e) m vcl))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Substitute m[x <- v]

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

(print-struct #t)

(define (print-state s)
  (printf "<~a, ~a>" (state-cl s) (state-k s)))

(define (show-eval s)
  (if (and (val? (closure-m (state-cl s)))
	   (not (symbol? (closure-m (state-cl s))))
	   (mtK? (state-k s)))

      (begin
        (print-state s)
        (printf "~n~nDone~n~n"))

      (begin
	;; Print initial state
	(print-state s)
	(printf " |->~n~n")
	(let ([s2 (next-state s)])
	  ;; Keep going:
	  (show-eval s2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests

(define example1 '(+ (- 1 0) (+ 2 (- 4 3))))
(show-eval (make-state (make-closure example1 empty) (make-mtK)))

(define example2 '((lam y y) ((lam x (+ x 5)) 12)))
(show-eval (make-state (make-closure example2 empty) (make-mtK)))

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
(show-eval (make-state (make-closure example3 empty) (make-mtK)))

(define example4 (make-app
                  (make-app '(lam f
                                  (lam x (f x)))
                            '(lam y
                                  (+ y y)))
                  1))

(show-eval (make-state (make-closure example4 empty) (make-mtK)))

(define example5 (make-app '(lam x
                                 (+ 10 (- 11 x)))
                           '((lam z
                                  (+ z z)) 12)))
(show-eval (make-state (make-closure example5 empty) (make-mtK)))