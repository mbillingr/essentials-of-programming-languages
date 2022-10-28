
def empty_stack():
    def the_stack():
        raise RuntimeError("Empty Stack")
    return the_stack


def push(value, stack):
    return lambda: (value, stack)


def pop(stack):
    return stack()[1]

def top(stack):
    return stack()[0]

stack = empty_stack()
stack = push(1, stack)
stack = push(2, stack)
print(top(stack))
print(top(stack))
stack = pop(stack)
print(top(stack))
