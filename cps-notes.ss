(cps '(add1 (f x)))
(f x (lambda (v0) (add1 v0)))

(define cps
  (lambda (exp)
    (define cps1
      (lambda (exp ctx)
        (pmatch exp
                [`,x (guard (not (pair? x))) (ctx x)]
                [`(lambda (,x) ,body) (ctx `(lambda (,x k) ,(cps1 body ctx0)))]
                [`(,rator ,rand) `(,rand (lambda (v) (,rator v)))])))
    (cps1 exp id)))

(cps '(add1 (f x)))
((f x) (lambda (v) (add1 v)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(cps '(f x)) => (f x) (如何转换为这样？)

(define cps
  (lambda (exp)
    (define cps1
      (lambda (exp ctx)
        (pmatch exp
                [`,x (guard (not (pair? x))) (ctx x)]
                [`(lambda (,x) ,body) (ctx `(lambda (,x k) ,(cps1 body ctx0)))]
                [`(,func ,arg) (cps1 func (lambda (x)
                                            (cps1 arg (lambda (x^)
                                                        `(,x ,x^)))))])))
    (cps1 exp id)))


(cps '(f x)) => (f x (lambda (v0) v0)) (如何转换为这样？)

(define cps
  (lambda (exp)
    (define cps1
      (lambda (exp ctx)
        (pmatch exp
                [`,x (guard (not (pair? x))) (ctx x)]
                [`(lambda (,x) ,body) (ctx `(lambda (,x k) ,(cps1 body ctx0)))]
                [`(,func ,arg) (cps1 func (lambda (x)
                                            (cps1 arg (lambda (x^)
                                                        `(,x ,x^ (lambda (v0) v0))))))])))
    (cps1 exp id)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(cps '(add1 (f x))) => (f x (lambda (v0) v0)) (wrong)

(cps '(add1 (f x))) => (f x (lambda (v0) add1 v0)) (如何转换为这样？)

并未使用过 ctx ，显示 ctx 出来观察一下。

(define cps
  (lambda (exp)
    (define cps1
      (lambda (exp ctx)
        (pmatch exp
                [`,x (guard (not (pair? x))) (ctx x)]
                [`(lambda (,x) ,body) (ctx `(lambda (,x k) ,(cps1 body ctx0)))]
                [`(,func ,arg) (cps1 func (lambda (x)
                                            (cps1 arg (lambda (x^)
                                                        `(,x ,x^ (lambda (v0) ,ctx))))))])))
    (cps1 exp id)))

(cps '(add1 (f x))) => '(f x (lambda (v0) #<procedure:...emantics/cps.rkt:20:54>))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

向 ctx 填入一个参数。

(define cps
  (lambda (exp)
    (define cps1
      (lambda (exp ctx)
        (pmatch exp
                [`,x (guard (not (pair? x))) (ctx x)]
                [`(lambda (,x) ,body) (ctx `(lambda (,x k) ,(cps1 body ctx0)))]
                [`(,func ,arg) (cps1 func (lambda (x)
                                            (cps1 arg (lambda (x^)
                                                        `(,x ,x^ (lambda (v0) ,(ctx `v0)))))))])))
    (cps1 exp id)))


(cps '(add1 (f x))) => '(f x (lambda (v0) (add1 v0 (lambda (v0) v0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define id
  (lambda (v) v))

(define ctx0
  (lambda (v) `(k ,v)))

(define delta-b1?
  (lambda (x) (memq x `(add1 sub1 zero?))))

(define cps
  (lambda (exp)
    (define cps1
      (lambda (exp ctx)
        (pmatch exp
                [`,x (guard (not (pair? x))) (ctx x)]
                [`(lambda (,x) ,body) (ctx `(lambda (,x k) ,(cps1 body ctx0)))]
                [`(,func ,arg) (cps1 func (lambda (x)
                                            (cps1 arg (lambda (x^)
                                                        (cond
                                                          [(delta-b1? x) `(,x ,x^)]
                                                          [else
                                                           `(,x ,x^ (lambda (v0) ,(ctx 'v0)))])))))])))
    (cps1 exp id)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define id
  (lambda (v) v))

(define ctx0
  (lambda (v) `(k ,v)))

(define delta-b1?
  (lambda (x) (memq x `(add1 sub1 zero?))))

(define new-var
  (let ([n -1])
    (lambda ()
      (set! n (+ 1 n))
      (string->symbol
       (string-append "v" (number->string n))))))

(define cps
  (lambda (exp)
    (define cps1
      (lambda (exp ctx)
        (pmatch exp
                [`,x (guard (not (pair? x))) (ctx x)]
                [`(lambda (,x) ,body) (ctx `(lambda (,x k) ,(cps1 body ctx0)))]
                [`(,func ,arg) (cps1 func (lambda (x)
                                            (cps1 arg (lambda (x^)
                                                        (cond
                                                          [(delta-b1? x) `(,x ,x^)]
                                                          [else (let ([var (new-var)])
                                                                  `(,x ,x^ (lambda (,var) ,(ctx var))))
                                                                ])))))])))
    (cps1 exp id)))

;;; tests

(cps 'x)
; x

(cps '(lambda (x) x))
; (lambda (x k) (k x))

(cps '(f x))
; (f x (lambda (v0) v0))

(cps '(add1 (f x)))
; (f x (lambda (v0)
;        (add1 v0)))

(cps '((f x) 1))
; (f x (lambda (v0)
;        (v0 1 (lambda (v1)
;                v1))))
