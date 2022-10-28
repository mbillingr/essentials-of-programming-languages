"""Implementation of stuff we know and love from Scheme"""

from typing import Any, Self


def is_null(obj: Any) -> bool:
    return obj == ()

def cons(a: Any, b: Any) -> "Pair":
    return Pair(a, b)

def car(p: "Pair") -> Any:
    return p.first

def cdr(p: "Pair") -> Any:
    return p.second


class Pair:
    def __init__(self, first: Any, second: Any) -> Self:
        self.first = first
        self.second = second

    def stringify(self) -> str:
        if isinstance(self.second, Pair):
            return f"{self.first} {self.second.stringify()}"
        elif is_null(self.second):
            return str(self.first)
        return f"{self.first} . {self.second}"

    def __repr__(self):
        return f"({self.stringify()})"
