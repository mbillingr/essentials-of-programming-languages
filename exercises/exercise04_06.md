
          (value-of exp1 rho s0) = (l, s1)
          (value-of exp2 rho s1) = (val, s2)
--------------------------------------------------------------------------
  (value-of (setref-exp exp1 exp2) rho s0) = (val, [l=val]s2)