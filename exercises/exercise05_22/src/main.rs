use std::rc::Rc;

macro_rules! expr {
    ((proc ($x:ident) $body:tt)) => {
        Rc::new(Expression::Proc(stringify!($x).to_string(), expr!($body)))
    };

    ((letrec ($f:ident $x:ident $fbody:tt) $body:tt)) => {
        Rc::new(Expression::LetRec(
            stringify!($f).to_string(),
            stringify!($x).to_string(),
            expr!($fbody),
            expr!($body),
        ))
    };

    ((zero? $x:tt)) => {
        Rc::new(Expression::IsZero(expr!($x)))
    };

    ((if $a:tt $b:tt $c:tt)) => {
        Rc::new(Expression::If(expr!($a), expr!($b), expr!($c)))
    };

    ((- $x:tt $y:tt)) => {
        Rc::new(Expression::Diff(expr!($x), expr!($y)))
    };

    (($rator:tt $rand:tt)) => {
        Rc::new(Expression::Call(expr!($rator), expr!($rand)))
    };

    ($x:ident) => {
        Rc::new(Expression::Var(stringify!($x).to_string()))
    };

    ($x:expr) => {
        Rc::new(Expression::Const($x))
    };
}

fn main() {
    use crate::Expression::*;
    println!(
        "{:?}",
        value_of_program(&Program {
            exp: expr! {
                    (letrec (foo x (if (zero? x) 42 (foo (- x 1))))
                        (foo 9999))
            }
        })
    )
}

#[derive(Debug, Clone)]
enum ExpVal {
    Num(i64),
    Bool(bool),
    Proc(Procedure),
}

impl ExpVal {
    fn to_num(&self) -> i64 {
        match self {
            ExpVal::Num(n) => *n,
            _ => panic!("Expected number: {:?}", self),
        }
    }

    fn to_bool(&self) -> bool {
        match self {
            ExpVal::Bool(b) => *b,
            _ => panic!("Expected boolean: {:?}", self),
        }
    }

    fn to_proc(&self) -> Procedure {
        match self {
            ExpVal::Proc(p) => p.clone(),
            _ => panic!("Expected procedure: {:?}", self),
        }
    }
}

#[derive(Debug, Clone)]
struct Procedure {
    var: String,
    body: Rc<Expression>,
    env: Rc<Environment>,
}

impl Procedure {
    fn bounce(self, val: ExpVal) -> Bounce {
        Bounce::Thunk(self, val)
    }

    fn apply(self, val: ExpVal) -> Bounce {
        value_of(&self.body, self.env.extend(self.var.clone(), val))
    }
}

struct Program {
    exp: Rc<Expression>,
}

type FinalAnswer = ExpVal;

fn value_of_program(prog: &Program) -> FinalAnswer {
    trampoline(value_of(&prog.exp, Rc::new(Environment::Empty)))
}

#[derive(Debug)]
enum Bounce {
    Value(ExpVal),
    Thunk(Procedure, ExpVal),
}

fn trampoline(mut bounce: Bounce) -> FinalAnswer {
    loop {
        match bounce {
            Bounce::Value(expr) => return expr,
            Bounce::Thunk(proc, val) => bounce = proc.apply(val),
        }
    }
}

fn trampolined_value_of(exp: &Rc<Expression>, env: Rc<Environment>) -> ExpVal {
    trampoline(value_of(exp, env))
}

#[derive(Debug, Clone)]
enum Expression {
    Const(i64),
    Var(String),
    Proc(String, Rc<Expression>),
    LetRec(String, String, Rc<Expression>, Rc<Expression>),
    IsZero(Rc<Expression>),
    If(Rc<Expression>, Rc<Expression>, Rc<Expression>),
    Diff(Rc<Expression>, Rc<Expression>),
    Call(Rc<Expression>, Rc<Expression>),
}

fn value_of(exp: &Rc<Expression>, env: Rc<Environment>) -> Bounce {
    match &**exp {
        Expression::Const(num) => Bounce::Value(ExpVal::Num(*num)),
        Expression::Var(var) => Bounce::Value(env.apply(var)),
        Expression::Proc(var, body) => Bounce::Value(ExpVal::Proc(Procedure {
            var: var.clone(),
            body: body.clone(),
            env: env.clone(),
        })),
        Expression::LetRec(proc_name, bound_var, proc_body, letrec_body) => value_of(
            letrec_body,
            env.extend_rec(proc_name.clone(), bound_var.clone(), proc_body),
        ),
        Expression::IsZero(exp1) => {
            Bounce::Value(ExpVal::Bool(trampolined_value_of(exp1, env).to_num() == 0))
        }
        Expression::If(exp1, exp2, exp3) => {
            if trampolined_value_of(exp1, env.clone()).to_bool() {
                value_of(exp2, env)
            } else {
                value_of(exp3, env)
            }
        }
        Expression::Diff(exp1, exp2) => {
            let num1 = trampolined_value_of(exp1, env.clone()).to_num();
            let num2 = trampolined_value_of(exp2, env).to_num();
            Bounce::Value(ExpVal::Num(num1 - num2))
        }
        Expression::Call(rator, rand) => {
            let func = trampolined_value_of(rator, env.clone());
            let arg = trampolined_value_of(rand, env);
            Bounce::Thunk(func.to_proc(), arg)
        }
    }
}

#[derive(Debug, Clone)]
enum Environment {
    Empty,
    Extend(String, ExpVal, Rc<Environment>),
    Rec(String, String, Rc<Expression>, Rc<Environment>),
}

impl Environment {
    fn extend(self: &Rc<Self>, var: String, val: ExpVal) -> Rc<Self> {
        Rc::new(Environment::Extend(var, val, self.clone()))
    }

    fn extend_rec(
        self: &Rc<Self>,
        p_name: String,
        b_var: String,
        body: &Rc<Expression>,
    ) -> Rc<Self> {
        Rc::new(Environment::Rec(p_name, b_var, body.clone(), self.clone()))
    }

    fn apply(self: &Rc<Self>, var: &str) -> ExpVal {
        match &**self {
            Environment::Empty => panic!("Unbound variable {}", var),
            Environment::Extend(bound_var, bound_val, env) => {
                if bound_var == var {
                    bound_val.clone()
                } else {
                    env.apply(var)
                }
            }
            Environment::Rec(p_name, b_var, body, env) => {
                if p_name == var {
                    ExpVal::Proc(Procedure {
                        var: b_var.clone(),
                        body: body.clone(),
                        env: self.clone(),
                    })
                } else {
                    env.apply(var)
                }
            }
        }
    }
}
