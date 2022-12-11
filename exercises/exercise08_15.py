
"""
This is a manual translation of the following program to python.
Obviously, there are no opaque types in Python, but I want to verify that the logic works without first writing an interpreter for that language.

module tables
  interface [
    opaque table]
    empty : table
    add-to-table : (int -> (int -> (table -> table)))
    lookup-in-table : (int -> (table -> int))
  ]
  body [
    type table = (int -> int)

    empty = proc (key : int) 0

    add-to-table = proc (key : int)
                     proc (val : int)
                       proc (tbl : table)
                         proc (lookup-key : int)
                           if ((equal? lookup-key) key)
                           then val
                           else (tbl lookup-key)

    lookup-in-table = proc (lookup-key : int)
                        proc (tbl : table)
                          (tbl lookup-key)

    equal? = proc (a : int)
               proc (b : int)
                 zero?(-(a,b))
  ]

let empty = from tables take empty
in let add-binding = from tables take add-to-table
in let lookup = from tables take lookup-in-table
in let table1 = (((add-binding 3) 300)
                 (((add-binding 4) 400)
                  (((add-binding 3) 600)
                   empty)))
in -(((lookup 4) table1),
     ((lookup 3) table1))

; should result in 100
"""

def empty(key):
  return 0

def add_binding(key):
  return lambda val: lambda tbl: lambda lookup_key: val if is_equal(lookup_key)(key) else tbl(lookup_key)

def lookup(lookup_key):
  return lambda tbl: tbl(lookup_key)

def is_equal(a):
  return lambda b: a - b == 0


table1 = add_binding(3)(300)(add_binding(4)(400)(add_binding(3)(600)(empty)))

assert lookup(4)(table1) - lookup(3)(table1) == 100
print("OK")