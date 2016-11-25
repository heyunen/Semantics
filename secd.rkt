#lang scheme
(require "pmatch.rkt")

;; SECD Machine
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Syntax recognizers, extractors, and makers
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
(define (o? o)
  (member o '(+ - =)))

(define (primapp? m)
  (and (list? m)
       (> (length m) 2)
       (let ([o (list-ref m 0)]
             [arg1 (list-ref m 1)]
             [arg2 (list-ref m 2)])
         (and (member o '(+ - =))
              (not (member arg1 '(+ - =)))
              (not (member arg2 '(+ - =)))))))

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
;; Environments

(define empty null)

(define (empty? a)
  (null? a))

;(define-struct bind (var v))
(define-struct bind(var v)
  #:property prop:custom-write
  (lambda (bind port write?)
    (fprintf port (if write? "<~s, ~s>" "<~a, ~a>")
             (bind-var bind) (bind-v bind))))

(define (lookup m e)
  (cond
    [(null? e) (error 'lookup "Couldn't find ~e in environment" m)]
    [(eq? m (bind-var (car e)))  (bind-v (car e))]
    [else (lookup m (cdr e))]))

(define (extend e m v)
  (cond
    [(null? e) (list (make-bind m v))]
    [(eq? m (bind-var (car e))) (cons (make-bind m v)
                                      (cdr e))]
    [else (cons (car e) (extend (cdr e) m v))]))

;;
(define-struct state (s e c d))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The one-step evaluator

(define (next-state state)
  (let* ([stack (state-s state)]
         [env (state-e state)]
         [control (state-c state)]
         [dump (state-d state)])
    (cond 
      ;; secd 1
      [(and (pair? control)
            (number? (car control)))
       (make-state (cons (car control) stack) env (cdr control) dump)]
      ;; secd PA
      [(primapp? control)
       (make-state stack env (list (primapp-arg1 control) (primapp-arg2 control) (primapp-op control)) dump)]      
      [(and (pair? control)
            (list? (car control))
            (primapp? (car control)))
       (make-state stack env
                   (append (list (primapp-arg1 (car control)) (primapp-arg2 (car control)) (primapp-op (car control))) (cdr control))
                   dump)]
      ;; secd 3
      [(and (not (null? control))
            (> (length stack) 1)
            (number? (car stack))
            (number? (cadr stack))
            (o? (car control)))
       (make-state (cons (apply-op (car control)
                                   (cadr stack)
                                   (car stack)) (cddr stack))
                   env (cdr control) dump)]
      ;; secd LA   
      [(and
        (pair? control)
        (app? (car control)))  
       (make-state stack env (append (append (car control) '(ap)) (cdr control)) dump)]
       ;(make-state stack env (append (append (list (app-func (car control)) (app-arg (car control))) '(ap)) (cdr control)) dump)]
      ;; secd 4
      [(and (pair? control)
            (func? (car control)))
       (make-state (cons (list (car control) env) stack) env (cdr control) dump)]
      ;; secd 5
      [(and (> (length stack) 1)
            (pair? (cadr stack))
            (func? (caadr stack))
            (null? control))
       (make-state '() (extend (cadadr stack) (func-var (caadr stack)) (car stack))
                   (list (func-body (caadr stack))) (list (cddr stack) env control dump))]
      [(and (> (length stack) 1)
            (pair? (cadr stack))
            (func? (caadr stack))
            (eq? (car control) 'ap))
       (make-state '() (extend (cadadr stack) (func-var (caadr stack)) (car stack))
                   (list (func-body (caadr stack))) (list (cddr stack) env (cdr control) dump))]
      ;; secd 6
      [(null? control)
       (make-state (cons (car stack) (list-ref dump 0)) (list-ref dump 1) (list-ref dump 2)  (list-ref dump 3))]  
      ;; secd 2
      [(symbol? (car control))
       (make-state (cons (lookup (car control) env) stack) env (cdr control) dump)]
      )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Substitute exp[x <- y]

(define substitute
  (lambda (x y exp)
    (pmatch exp
            [`,a (guard (symbol? a)) (if (eq? a x)
                                       y
                                       exp)]
            [`(lambda (,v) ,b) (if (eq? x v)
                                   exp
                                   (let* ([$v (gensym v)]
                                          [$b (substitute v $v b)]
                                          [$$b (substitute x y $b)])
                                     `(lambda (,$v) ,$$b)))]
            [`(,rator, rand) `(,(substitute x y rator) ,(substitute x y rand))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The evaluation function:

(print-struct #t)

(define (print-state s)
  (printf "<~a, ~a, ~a, ~a>" (state-s s) (state-e s) (state-c s) (state-d s)))

(define (show-eval s)
  (if (and 
       (empty? (state-c s))
       (empty? (state-d s))
       (or (and (number? (car (state-s s)))
                (eq? (length (state-s s)) 1))
           (func? (car (state-s s)))))
      
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

;; Test
(define example0 '(+ 1 1))
(show-eval (make-state '() '() example0 '()))

(define example1 '(+ (- 1 0) (+ 2 (- 4 3))))
(show-eval (make-state '() '() example1 '()))

(define example2 '((lam y y) ((lam x (+ x 5)) 12)))
(show-eval (make-state '() '() example2 '()))

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
(define example3 (make-app sum 1))
;(show-eval (make-state '() '() example3 '()))

(define example4 (make-app
                  (make-app '(lam f
                                  (lam x (f x)))
                            '(lam y
                                  (+ y y)))
                  1))
(show-eval (make-state '() '() example4 '()))

(define example5 (make-app '(lam x
                                 (+ 10 (- 11 x)))
                           '((lam z
                                  (+ z z)) 12)))
(show-eval (make-state '() '() example5 '()))