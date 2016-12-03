#lang scheme

;; CS Machine
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Syntax recognizers, extractors, and makers

;;
(define (void? m)
  (eq? m 'void))

(define void 'void)

;; 
(define (val? m)
  (or (number? m)
      (func? m)))

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
       (not (primapp? m))
       (not (set? m))))

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
(define (make-let x m n)
  (list 'let x '= m 'in n))

;;
(define (set? m)
  (and (list? m)
       (eq? (list-ref m 0) 'set)))

(define (set-x m)
  (list-ref m 1))

(define (set-v m)
  (list-ref m 2))

(define (make-set x v)
  (list 'set x v))

;;
(define-struct state (e t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The one-step evaluator

(define (next-state s)
  (let ([e (state-e s)]
        [t (state-t s)])
    (cond
      ;; csfiv
      [(and (app? e)
            (func? (app-func e))
            (not (member (func-var (app-func e)) (assign-vars (func-body (app-func e)))))
            (val? (app-arg e)))
       (make-state (substitute (func-body (app-func e)) (func-var (app-func e)) (app-arg e)) t)]
      ;; csfis
      [(and (app? e)
            (func? (app-func e))
            (member (func-var (app-func e)) (assign-vars (func-body (app-func e))))
            (val? (app-arg e)))
       (let ([y (gensym 'δ)])
         (make-state (substitute (func-body (app-func e)) (func-var (app-func e)) y) (extend t y (app-arg e))))]
      ;; cs!
      [(symbol? e)
       (let ([v (lookup t e)])
         (make-state v (remove t e v)))]
      ;; cs=
      [(set? e)
       (make-state void (extend t (set-x e) (set-v e)))]
      ;; csffi
      [(primapp? e)
       (make-state (apply-op (primapp-op e) (primapp-arg1 e) (primapp-arg2 e)) t)]
      ;; Error
      [else (error 'next-state "stuck: ~e" e)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Assignable variables

(define union
  (lambda (ls1 ls2)
    (cond
      [(null? ls1) ls2]
      [(memv (car ls1) ls2) (union (cdr ls1) ls2)]
      [else (cons (car ls1) (union (cdr ls1) ls2))])))

(define (assign-vars m)
  (cond
    [(number? m) null]
    [(func? m) (remv (func-var m) (assign-vars (func-body m)))]    
    [(app? m) (union (assign-vars (app-func m)) (assign-vars (app-arg m)))]
    [(set? m) (union (assign-vars (set-v m)) (list (set-x m)))]
    [(primapp? m) (union (assign-vars (primapp-arg1 m)) (assign-vars (primapp-arg2 m)))]
    [(symbol? m) null]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Stores
(define empty null)

;(define-struct bind (var val))
(define-struct bind (var val)
  #:property prop:custom-write
  (lambda (bind port write?)
    (fprintf port (if write? "<~s, ~s>" "<~a, ~a>")
             (bind-var bind) (bind-val bind))))

(define (lookup t var)
  (cond
    [(null? t) (error 'lookup "Couldn't find ~e in store" var)]
    [(eq? (bind-var (car t)) var) (bind-val (car t))]
    [else (lookup (cdr t) var)]))

(define (extend t var val)
  (cond
    [(null? t) (list (make-bind var val))]
    [(eq? var (bind-var (car t))) (cons (make-bind var val)
                                      (cdr t))]
    [else (cons (car t) (extend (cdr t) var val))]))

(define (remove t var val)
  (cond
    [(null? t) null]
    [(and (eq? var (bind-var (car t)))
          (eq? val (bind-val (car t)))) (cdr t)]
    [else (cons (car t) (remove (cdr t) var val))]))

(define (all-vars t)
  (cond
    [(null? t) '()]
    [else (cons (bind-var (car t)) (all-vars (cdr t)))]))

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
   [(set? m) (make-set (substitute (set-x m) x v) (substitute (set-v m) x v))]
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
    [(set? m) (append (free-vars (set-v m) bound)
                      (list (set-x m)))]
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
  (printf "<~a, ~a>" (state-e s) (state-t s)))

(define (show-eval s)
  (if (and (or (val? (state-e s))
               (void? (state-e s)))
           (null? (state-t s)))
      
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
; (let ([x 12]) (begin (set! x 13) x))
((lambda (x) ((lambda (y) x) (set! x (+ x 1)))) 12)

(define example1 '((lam x ((lam y x) (set x (+ x 1)))) 12))
(show-eval (make-state example1 empty))


