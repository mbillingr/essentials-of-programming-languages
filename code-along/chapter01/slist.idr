
mutual
    data Sexpr = S String | L Slist

    Slist : Type
    Slist = List Sexpr
    
mutual
    subst : String -> String -> Slist -> Slist
    subst new old [] = []
    subst new old (x :: xs) = (subst_in_sexp new old x) :: (subst new old xs)

    subst_in_sexp : String -> String -> Sexpr -> Sexpr
    subst_in_sexp new old (S x) = S (if x == old then new else old)
    subst_in_sexp new old (L xs) = L (subst new old xs)
