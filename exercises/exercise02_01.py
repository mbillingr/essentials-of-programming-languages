import timeit
import matplotlib.pyplot as plt


N = 16

def zero():
    return ()

def is_zero(obj):
    return obj == ()

def successor(n):
    match n:
        case (): return (1, ())
        case (r, q) if r == N-1: return (0, successor(q))
        case (r, q): return (r+1, q)
        case _: raise TypeError(n)


def predecessor(n):
    match n:
        case (1, ()): return zero()
        case (0, q): return (N-1, predecessor(q))
        case (r, q): return (r-1, q)
        case _: raise TypeError(n)


def from_int(k: int):
    n = zero()
    for _ in range(k):
        n = successor(n)
    return n


assert zero() == ()
assert successor(zero()) == (1, ())
assert successor((N-1,())) == (0, (1, ()))
assert from_int(33) == (1, (2, ()))
assert from_int(258) == (2, (0, (1, ())))
assert predecessor((1, (0, (1, ())))) == (0, (0, (1, ())))
assert predecessor((0, (0, (1, ())))) == (N-1, (N-1, ()))


def plus(x, y):
    ## using iteration because the recursive implementation overflows python's stack
    while not is_zero(x):
        x = predecessor(x)
        y = successor(y)
    return y


assert plus(from_int(9), from_int(9)) == from_int(18)


def mult(x, y):
    ## using iteration because the recursive implementation overflows python's stack
    result = zero()
    while not is_zero(x):
        x = predecessor(x)
        result = plus(y, result)
    return result

assert mult(from_int(5), from_int(7)) == from_int(35)

def factorial(n):
    if is_zero(n):
        return successor(zero())
    return mult(n, factorial(predecessor(n)))

assert factorial(from_int(0)) == from_int(1)
assert factorial(from_int(1)) == from_int(1)
assert factorial(from_int(2)) == from_int(2)
assert factorial(from_int(3)) == from_int(6)
assert factorial(from_int(5)) == from_int(120)

print("OK")

if __name__ == "__main__":
    def time_factorial():
        factorial(n)

    N = 256

    x_data, y_data = [], []
    for k in range(11):
        n = from_int(k)
        count, total_time = timeit.Timer(time_factorial).autorange()
        print(k, total_time/count)
        x_data.append(k)
        y_data.append(total_time/count)
    plt.figure()
    plt.plot(x_data, y_data)
    plt.xlabel("n!")
    plt.ylabel("time")
    plt.title(f"N={N}")
    plt.savefig("exercise02_01a.png")

    n_ = 10
    n = from_int(n_)
    x_data, y_data = [], []
    for k in range(1, 17):
        N = 2**k
        count, total_time = timeit.Timer(time_factorial).autorange()
        print(k, total_time/count)
        x_data.append(k)
        y_data.append(total_time/count)
    plt.figure()
    plt.plot(x_data, y_data)
    plt.xlabel("N = 2**x")
    plt.ylabel("time")
    plt.title(f"{n_}!")
    plt.savefig("exercise02_01b.png")

    plt.show()

# The computation time increases exponentially with n in n!.
# This is directly related to the amount of increments required to compute the factorial.

# Performance improves with increasing base N.
# With lower N, there is a higher chance that the predecessor/successor operation need to recur.
# In contrast, with larger N, most predecessor/successor calls tend to affect only the first element.
# There is a decrease in performance for N>256. This is probably due Python's optimized small integer handling.