#lang racket


;(define mult
;  (lambda (n)
;    (lambda (m)
;      (cond
;        [(zero? n) 0]
;        [else (+ m ((mult (sub1 n)) m))]))))


(define mkmult
  (lambda (t)
    (lambda (n)
      (lambda (m)
        (cond
          [(zero? n) 0]
          [else (+ m (((t t) (sub1 n)) m))])))))

(define mult (mkmult mkmult))


((mult 4) 2)


((lambda (t)
   (lambda (n)
     (lambda (m)
       (cond
         [(zero? n) 0]
         [else (+ m (((t t) (sub1 n)) m))]))))
 (lambda (t)
   (lambda (n)
     (lambda (m)
       (cond
         [(zero? n) 0]
         [else (+ m (((t t) (sub1 n)) m))])))))


((((lambda (t)
     (lambda (n)
       (lambda (m)
         (cond
           [(zero? n) 0]
           [else (+ m (((t t) (sub1 n)) m))]))))
   (lambda (t)
     (lambda (n)
       (lambda (m)
         (cond
           [(zero? n) 0]
           [else (+ m (((t t) (sub1 n)) m))]))))) 4) 2)


((lambda (u) (u u))
 (lambda (t)
   (lambda (n)
     (lambda (m)
       (cond
         [(zero? n) 0]
         [else (+ m (((t t) (sub1 n)) m))])))))


((((lambda (u) (u u))
 (lambda (t)
   (lambda (n)
     (lambda (m)
       (cond
         [(zero? n) 0]
         [else (+ m (((t t) (sub1 n)) m))]))))) 2) 5)


((lambda (u) (u u))
 (lambda (mult)
   ((lambda (t)
      (lambda (n)
        (lambda (m)
          (cond
            [(zero? n) 0]
            [else (+ m ((t (sub1 n)) m))]))))
    (lambda (v) ((mult mult) v)))))


((((lambda (u) (u u))
 (lambda (mult)
   ((lambda (t)
      (lambda (n)
        (lambda (m)
          (cond
            [(zero? n) 0]
            [else (+ m ((t (sub1 n)) m))]))))
    (lambda (v) ((mult mult) v))))) 2) 6)


((lambda (f)
   ((lambda (u) (u u))
    (lambda (mult)
      (f
       (lambda (v) ((mult mult) v))))))
 (lambda (t)
      (lambda (n)
        (lambda (m)
          (cond
            [(zero? n) 0]
            [else (+ m ((t (sub1 n)) m))])))))


((((lambda (f)
     ((lambda (u) (u u))
      (lambda (mult)
        (f
         (lambda (v) ((mult mult) v))))))
   (lambda (t)
     (lambda (n)
       (lambda (m)
         (cond
           [(zero? n) 0]
           [else (+ m ((t (sub1 n)) m))]))))) 2) 6)


(lambda (f)
   ((lambda (u) (u u))
    (lambda (x)
      (f
       (lambda (v) ((x x) v))))))


(lambda (f)
  ((lambda (x) (f (lambda (v) ((x x) v))))
   (lambda (x) (f (lambda (v) ((x x) v))))))


; test
((((lambda (f)
   ((lambda (x) (f (lambda (v) ((x x) v))))
    (lambda (x) (f (lambda (v) ((x x) v))))))
 (lambda (t)
   (lambda (n)
     (lambda (m)
       (cond
         [(zero? n) 0]
         [else (+ m ((t (sub1 n)) m))]))))) 2) 6)
 