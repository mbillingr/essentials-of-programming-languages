#lang eopl

(define-datatype bintree bintree?
    (leaf-node 
        (num integer?))
    (interior-node
        (key symbol?)
        (left bintree?)
        (right bintree?)))
        
(define (bintree-to-list tree)
    (cases bintree tree
        (leaf-node (num)
            (list 'leaf-node num))
        (interior-node (key left right)
            (list 'interior-node 
                  key 
                  (bintree-to-list left) 
                  (bintree-to-list right)))))