
data LcExp = Ident String
           | Lambda String LcExp
           | Call LcExp LcExp


occurs_free : String -> LcExp  -> Bool
-- usage: returns True if the symbol var occurs free
--        in exp, otherwise returns False.
occurs_free var (Ident s) = s == var
occurs_free var (Lambda y e) = y /= var && occurs_free var e
occurs_free var (Call e1 e2) = occurs_free var e1 || occurs_free var e2
