#lang scheme

;; CK Machine
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
;(define-struct mtK ())
(define-struct mtK()
  #:property prop:custom-write
  (lambda (mtK port write?)
    (fprintf port "mt")))

;(define-struct funK (v k))
(define-struct funK(v k)
  #:property prop:custom-write
  (lambda (funK port write?)
    (fprintf port (if write? "<~s, ~s>" "<~a, ~a>")
             (funK-v funK) (funK-k funK))))

;(define-struct argK (n k))
(define-struct argK(n k)
  #:property prop:custom-write
  (lambda (argK port write?)
    (fprintf port (if write? "<~s, ~s>" "<~a, ~a>")
             (argK-n argK) (argK-k argK))))

;(define-struct primargK (o n k))
(define-struct primargK(o n k)
  #:property prop:custom-write
  (lambda (primargK port write?)
    (fprintf port (if write? "<~s, ~s, ~s>" "<~a, ~a, ~a>")
             (primargK-o primargK) (primargK-n primargK) (primargK-k primargK))))

;(define-struct primK (o v k))
(define-struct primK(o v k)
  #:property prop:custom-write
  (lambda (primK port write?)
    (fprintf port (if write? "<~s, ~s, ~s>" "<~a, ~a, ~a>")
             (primK-o primK) (primK-v primK) (primK-k primK))))

;;
(define-struct state (m k))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The one-step evaluator

(define (next-state s)
  (let ([m (state-m s)]
        [k (state-k s)])
    (cond
      ;; ck1
      [(app? m)
       (make-state (app-func m)
                   (make-argK (app-arg m) k))]
      ;; ck2
      [(primapp? m)
       (make-state (primapp-arg1 m)
                   (make-primargK (primapp-op m) (primapp-arg2 m) k))]
      [(val? m)
       (cond
         ;; ck3
         [(funK? k)
          (make-state (substitute (func-body (funK-v k))
                                  (func-var (funK-v k))
                                  m) (funK-k k))]
         ;; ck4
         [(argK? k)
          (make-state (argK-n k) (make-funK m (argK-k k)))]
         ;; ck5
         [(and (number? m)
               (primargK? k)
               (number? (primargK-n k)))
          (make-state (apply-op (primargK-o k)
                                m
                                (primargK-n k))
                      (primargK-k k))]
         ;; ck6
         [(primargK? k)
          (make-state (primargK-n k)
                      (make-primargK (primargK-o k)
                                     m
                                     (primargK-k k)))]         
         ;; Error
         [else (error 'next-state "no recognized : ~k" k)]
         )]
      [else (error 'next-state "stuck: " m)]
      )))

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

(define (print-state s)
  (printf "<~a, ~a>" (state-m s) (state-k s)))

(define (show-eval s)
  (if (and (val? (state-m s))
	   (mtK? (state-k s)))

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
(show-eval (make-state example1 (make-mtK)))

(define example2 '((lam y y) ((lam x (+ x 5)) 12)))
(show-eval (make-state example2 (make-mtK)))

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
(show-eval (make-state example3 (make-mtK)))

(define example4 (make-app
                  (make-app '(lam f
                                  (lam x (f x)))
                            '(lam y
                                  (+ y y)))
                  1))
(show-eval (make-state example4 (make-mtK)))

(define example5 (make-app '(lam x
                                 (+ 10 (- 11 x)))
                           '((lam z
                                  (+ z z)) 12)))
(show-eval (make-state example5 (make-mtK)))