#lang scheme

;; CEKS Machine (CESK Machine) without GC
;; based on State ISWIM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Syntax recognizers, extractors, and makers

;;
(define empty null)

(define (empty? m)
  (eq? m empty))

;;
(define void 'void)

(define (void? m)
  (eq? m 'void))

;; V = b
;;   | (λX.M)
(define (val? m)
  (or (number? m)
      (func? m)
      ;(symbol? m) 
      ))

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

;(define-struct primargK (o ncl k))
(define-struct primargK(o ncl k)
  #:property prop:custom-write
  (lambda (primargK port write?)
    (fprintf port (if write? "<~s, ~s, ~s>" "<~a, ~a, ~a>")
             (primargK-o primargK) (primargK-ncl primargK) (primargK-k primargK))))

;(define-struct primK (o vcl k))
(define-struct primK(o vcl k)
  #:property prop:custom-write
  (lambda (primK port write?)
    (fprintf port (if write? "<~s, ~s, ~s>" "<~a, ~a, ~a>")
             (primK-o primK) (primK-vcl primK) (primK-k primK))))

;(define-struct setK (c k))
(define-struct setK(c k)
  #:property prop:custom-write
  (lambda (setK port write?)
    (fprintf port (if write? "<~s, ~s>" "<~a, ~a>")
             (setK-c setK) (setK-k setK))))

;;
(define-struct state (cl k store))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The one-step evaluator

(define (next-state s)
  (let* ([cl (state-cl s)]
         [m (closure-m cl)]
         [e (closure-e cl)]
         [k (state-k s)]
         [store (state-store s)])
    (cond
      ;; ceks1
      [(app? m)
       (make-state (make-closure (app-func m) e)
                   (make-argK (make-closure (app-arg m) e) k) store)]
      ;; cek2
      [(primapp? m)
       (make-state (make-closure (primapp-arg1 m) e)
                   (make-primargK (primapp-op m)
                                  (make-closure (primapp-arg2 m) e) k) store)]
 
      ;; ceks3*
      [(and (val? m)
            (funK? k))
       (let ([δ (gensym 'δ)])
         (make-state (make-closure (func-body (closure-m (funK-vcl k)))
                                   (env-extend (closure-e (funK-vcl k))
                                               (func-var (closure-m (funK-vcl k)))
                                               δ))
                     (funK-k k) (store-extend store δ cl)))]
      ;; ceks4
      [(and (val? m)
            (argK? k))
       (make-state (argK-ncl k) (make-funK cl (argK-k k)) store)]
      ;; ceks5
      [(and (number? m)
            (primK? k)
            (number? (closure-m (primK-vcl k))))
       (make-state (make-closure (apply-op (primK-o k)
                                           (closure-m (primK-vcl k))
                                           m)
                                 empty)
                   (primK-k k) store)]
      ;; ceks6
      [(and (val? m)
            (primargK? k))
       (make-state (primargK-ncl k)
                   (make-primK (primargK-o k) cl (primargK-k k)) store)]    
      ;; ceks7*
      [(symbol? m)
       (make-state (store-lookup (env-lookup m e) store) k store)]   
      ;; ceks8*
      [(set? m)
       (make-state (make-closure (set-v m) e) (make-setK (make-closure (set-x m) e) k) store)]
      ;; ceks9*
      [(and (val? m)
            (setK? k))
       (let ([δ (env-lookup (closure-m (setK-c k)) (closure-e (setK-c k)))])
         (make-state (store-lookup δ store) (setK-k k) (store-extend store δ cl)))]
      [else (error 'next-state "stuck: ~e" cl)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Environments

;(define-struct env-bind (var vcl))
(define-struct env-bind (var vcl)
  #:property prop:custom-write
  (lambda (env-bind port write?)
    (fprintf port (if write? "<~s, ~s>" "<~a, ~a>")
             (env-bind-var env-bind) (env-bind-vcl env-bind))))

(define (env-lookup m e)
  (cond
    [(null? e) (error 'env-lookup "Couldn't find ~e in environment" m)]
    [(eq? m (env-bind-var (car e)))  (env-bind-vcl (car e))]
    [else (env-lookup m (cdr e))]))

(define (env-extend e m vcl)
  (cond
    [(null? e) (list (make-env-bind m vcl))]
    [(eq? m (env-bind-var (car e))) (cons (make-env-bind m vcl)
                                      (cdr e))]
    [else (cons (car e) (env-extend (cdr e) m vcl))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Stores

;(define-struct store-bind (var val))
(define-struct store-bind (var val)
  #:property prop:custom-write
  (lambda (store-bind port write?)
    (fprintf port (if write? "<~s, ~s>" "<~a, ~a>")
             (store-bind-var store-bind) (store-bind-val store-bind))))

(define (store-lookup var t)
  (cond
    [(null? t) (error 'store-lookup "Couldn't find ~e in store" var)]
    [(eq? (store-bind-var (car t)) var) (store-bind-val (car t))]
    [else (store-lookup var (cdr t))]))

(define (store-extend t var val)
  (cond
    [(null? t) (list (make-store-bind var val))]
    [(eq? var (store-bind-var (car t))) (cons (make-store-bind var val)
                                      (cdr t))]
    [else (cons (car t) (store-extend (cdr t) var val))]))

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
  (printf "<~a, ~a, ~a>" (state-cl s) (state-k s) (state-store s)))

(define (show-eval s)
  (if (and (empty? (closure-e (state-cl s)))
           (not (symbol? (closure-m (state-cl s))))
           (mtK? (state-k s))
           ;(empty? (state-store s))
           (or (val? (closure-m (state-cl s)))
               (void? (closure-m (state-cl s)))))
      
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
;(show-eval (make-state (make-closure example1 empty) (make-mtK) empty))

(define example2 '((lam y y) ((lam x (+ x 5)) 12)))
;(show-eval (make-state (make-closure example2 empty) (make-mtK) empty))

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
;(show-eval (make-state (make-closure example3 empty) (make-mtK) empty))

(define example4 (make-app
                  (make-app '(lam f
                                  (lam x (f x)))
                            '(lam y
                                  (+ y y)))
                  1))

;(show-eval (make-state (make-closure example4 empty) (make-mtK) empty))

(define example5 (make-app '(lam x
                                 (+ 10 (- 11 x)))
                           '((lam z
                                  (+ z z)) 12)))
;(show-eval (make-state (make-closure example5 empty) (make-mtK) empty))

(define example6 '((lam x ((lam y x) 1)) 12))
;(show-eval (make-state (make-closure example6 empty) (make-mtK) empty))

;((lambda (x) ((lambda (y) x) (set! x (+ x 1)))) 12)
(define example7 '((lam x ((lam y x) (set x (+ x 1)))) 12))
;(show-eval (make-state (make-closure example7 empty) (make-mtK) empty))
