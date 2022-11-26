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
    fn bounce(self, val: ExpVal, cont: Continuation) -> Bounce {
        Bounce::Thunk(self, val, cont)
    }

    fn apply(self, val: ExpVal, cont: Continuation) -> Bounce {
        value_of_k(&self.body, self.env.extend(self.var.clone(), val), cont)
    }
}

struct Program {
    exp: Rc<Expression>,
}

type FinalAnswer = ExpVal;

fn value_of_program(prog: &Program) -> FinalAnswer {
    trampoline(value_of_k(
        &prog.exp,
        Rc::new(Environment::Empty),
        Continuation::End,
    ))
}

#[derive(Debug)]
enum Bounce {
    Value(ExpVal),
    Thunk(Procedure, ExpVal, Continuation),
}

fn trampoline(mut bounce: Bounce) -> FinalAnswer {
    loop {
        println!("{:?}", bounce);
        match bounce {
            Bounce::Value(expr) => return expr,
            Bounce::Thunk(proc, val, cont) => bounce = proc.apply(val, cont),
        }
    }
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

fn value_of_k(exp: &Rc<Expression>, env: Rc<Environment>, cont: Continuation) -> Bounce {
    match &**exp {
        Expression::Const(num) => cont.apply(ExpVal::Num(*num)),
        Expression::Var(var) => cont.apply(env.apply(var)),
        Expression::Proc(var, body) => cont.apply(ExpVal::Proc(Procedure {
            var: var.clone(),
            body: body.clone(),
            env: env.clone(),
        })),
        Expression::LetRec(proc_name, bound_var, proc_body, letrec_body) => value_of_k(
            letrec_body,
            env.extend_rec(proc_name.clone(), bound_var.clone(), proc_body),
            cont,
        ),
        Expression::IsZero(exp1) => value_of_k(exp1, env, Continuation::Zero1(Box::new(cont))),
        Expression::If(exp1, exp2, exp3) => value_of_k(
            exp1,
            env.clone(),
            Continuation::If(exp2.clone(), exp3.clone(), env, Box::new(cont)),
        ),
        Expression::Diff(exp1, exp2) => value_of_k(
            exp1,
            env.clone(),
            Continuation::Diff1(exp2.clone(), env, Box::new(cont)),
        ),
        Expression::Call(rator, rand) => value_of_k(
            rator,
            env.clone(),
            Continuation::Call1(rand.clone(), env, Box::new(cont)),
        ),
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

#[derive(Debug)]
enum Continuation {
    End,
    Zero1(Box<Continuation>),
    If(
        Rc<Expression>,
        Rc<Expression>,
        Rc<Environment>,
        Box<Continuation>,
    ),
    Diff1(Rc<Expression>, Rc<Environment>, Box<Continuation>),
    Diff2(ExpVal, Box<Continuation>),
    Call1(Rc<Expression>, Rc<Environment>, Box<Continuation>),
    Call2(Procedure, Box<Continuation>),
}

impl Continuation {
    fn apply(self, val: ExpVal) -> Bounce {
        match self {
            Continuation::End => {
                println!("End of computation");
                Bounce::Value(val.clone())
            }
            Continuation::Zero1(cont) => cont.apply(ExpVal::Bool(val.to_num() == 0)),
            Continuation::If(exp2, exp3, env, cont) => {
                value_of_k(&if val.to_bool() { exp2 } else { exp3 }, env, *cont)
            }
            Continuation::Diff1(exp2, env, cont) => {
                value_of_k(&exp2, env, Continuation::Diff2(val, cont))
            }
            Continuation::Diff2(exp1, cont) => {
                cont.apply(ExpVal::Num(exp1.to_num() - val.to_num()))
            }
            Continuation::Call1(rand, env, cont) => {
                value_of_k(&rand, env, Continuation::Call2(val.to_proc(), cont))
            }
            Continuation::Call2(proc, cont) => proc.bounce(val, *cont),
        }
    }
}
