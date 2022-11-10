
          (value-of exp1 rho s0) = (val1, s1)
--------------------------------------------------------
  (value-of (zero?-exp exp1) rho s0)
    = ((val-bool #t), s1)  if (expval->num val1) = 0
    | ((val-bool #f), s1)  if (expval->num val1) != 0