#lang scheme

(lambda (x y k) (q y (lambda (qy) (p (+ 8 x) qy k))))

(lambda (x y u v)
  (g x y
     (lambda (gxy)
       (f gxy (+ u v)
          (lambda (fr) (+ 1 fr))))))

(g x y
   (lambda (gxy)
      (h v
         (lambda (hv)
            (f gxy (+ u hv)
               (lambda (fr)
                 (+ 1 fr)))))))


(if a
    (p x (lambda (px) (zero? px cont)))
    (p y (lambda (py) (zero? py cont))))

(f a
  (lambda (fa)
     (if fa
         (p x (lambda (px) (zero? px cont)))
         (p y (lambda (py) (zero? py cont))))))

(let ((y 8))
  (p y
     (lambda (x)
       x)))

(if a
   (p x (lambda (x) x))
   (p y (lambda (x) x)))
