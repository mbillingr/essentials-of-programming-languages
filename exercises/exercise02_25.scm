#lang eopl

(define-datatype bintree bintree?
    (leaf-node 
        (num integer?))
    (interior-node
        (key symbol?)
        (left bintree?)
        (right bintree?)))

(define (max-interior tree)
    (caddr (max-interior-helper tree)))
        
(define (max-interior-helper tree)
    (define (get-sum m)
        (car m))
    (define (get-max-sum m)
        (cadr m))
    (define (get-max-key m)
        (caddr m))
    (cases bintree tree
        (leaf-node (num) 
            (list num num 'n/a))
        (interior-node (key left right)
            (let* ((ml (max-interior-helper left))
                   (mr (max-interior-helper right))
                   (sum (+ (get-sum ml) (get-sum mr))))
                (if (and (>= sum (get-max-sum ml))
                         (>= sum (get-max-sum mr)))
                    (list sum sum key)
                    (if (>= (get-max-sum ml) (get-max-sum mr))
                        (list sum (get-max-sum ml) (get-max-key ml))
                        (list sum (get-max-sum mr) (get-max-key mr))))))))
                 
(define tree-1
    (interior-node 'foo (leaf-node 2) (leaf-node 3)))

(define tree-2
    (interior-node 'bar (leaf-node -1) tree-1))

(define tree-3
    (interior-node 'baz tree-2 (leaf-node 1)))