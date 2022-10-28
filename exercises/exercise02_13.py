
def empty_env():
    return (
        lambda search_var: report_no_binding_found(search_var),
        lambda: True
    )


def extend_env(var, val, env):
    return (
        lambda search_var: val if var == search_var else apply_env(env, search_var),
        lambda: False
    )


def apply_env(env, var):
    return env[0](var)


def is_empty_env(env):
    return env[1]()


def report_no_binding_found(search_var):
    raise LookupError(search_var)


assert apply_env(extend_env("x", 42, empty_env()), "x") == 42
assert is_empty_env(empty_env())
assert not is_empty_env(extend_env("x", 42, empty_env()))
