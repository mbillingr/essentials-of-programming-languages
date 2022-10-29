#lang eopl

(define (list-of-red-blue-subtrees? obj)
    (or (null? obj)
        (and (pair? obj)
             (red-blue-subtree? (car obj))
             (list-of-red-blue-subtrees? (cdr obj)))))

(define-datatype red-blue-subtree red-blue-subtree?
    (red-node
        (left red-blue-subtree?)
        (right red-blue-subtree?))
    (blue-node
        (children list-of-red-blue-subtrees?))
    (leaf-node
        (num integer?)))
    
(define (mark-leaves-with-red-depth-helper tree n-red)
    (cases red-blue-subtree tree
        (red-node (left right)
            (red-node (mark-leaves-with-red-depth-helper left (+ 1 n-red))
                      (mark-leaves-with-red-depth-helper right (+ 1 n-red))))
        (blue-node (children)
            (blue-node 
                (map (lambda (t) (mark-leaves-with-red-depth-helper t n-red))
                     children)))
        (leaf-node (num)
            (leaf-node n-red))))
                
(define sample-tree
    (red-node
        (blue-node
            (list (leaf-node 26) (leaf-node 12)))
        (red-node
            (leaf-node 11)
            (blue-node 
                (list (leaf-node 117) (leaf-node 14))))))