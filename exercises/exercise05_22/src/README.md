
It is possible to use the trampolining technique, even if the
interpreter does not use continuation-passing style.

In the CPS interpreter, we only need one global trampoline
because control context is extended in the continuations.

Here, we need to explicitly insert a nested trampoline whenever
the control context is extended (i.e. whenever a value is needed).