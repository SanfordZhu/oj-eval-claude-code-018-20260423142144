/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 * 
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp" 
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    std::vector<Value> args;
    for (auto &r : rands) args.push_back(r->eval(e));
    return evalRator(args);
}

Value Var::eval(Assoc &e) { // evaluation of variable
    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
             static std::map<ExprType, std::pair<Expr, std::vector<std::string>>> primitive_map = {
                    {E_VOID,     {new MakeVoid(), {}}},
                    {E_EXIT,     {new Exit(), {}}},
                    {E_BOOLQ,    {new IsBoolean(new Var("parm")), {"parm"}}},
                    {E_INTQ,     {new IsFixnum(new Var("parm")), {"parm"}}},
                    {E_NULLQ,    {new IsNull(new Var("parm")), {"parm"}}},
                    {E_PAIRQ,    {new IsPair(new Var("parm")), {"parm"}}},
                    {E_PROCQ,    {new IsProcedure(new Var("parm")), {"parm"}}},
                    {E_SYMBOLQ,  {new IsSymbol(new Var("parm")), {"parm"}}},
                    {E_STRINGQ,  {new IsString(new Var("parm")), {"parm"}}},
                    {E_DISPLAY,  {new Display(new Var("parm")), {"parm"}}},
                    {E_PLUS,     {new PlusVar({}),  {}}},
                    {E_MINUS,    {new MinusVar({}), {}}},
                    {E_MUL,      {new MultVar({}),  {}}},
                    {E_DIV,      {new DivVar({}),   {}}},
                    {E_MODULO,   {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EXPT,     {new Expt(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EQQ,      {new EqualVar({}), {}}},
            };

            auto it = primitive_map.find(primitives[x]);
            if (it != primitive_map.end()) {
                return ProcedureV(it->second.second, it->second.first, e);
            }
      }
      throw RuntimeError("undefined");
    }
    return matched_value;
}

static Value normalize_frac(int num, int den) {
    Value v = RationalV(num, den);
    Rational* r = dynamic_cast<Rational*>(v.get());
    if (r->denominator == 1) return IntegerV(r->numerator);
    return v;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int a = dynamic_cast<Integer*>(rand1.get())->n;
        int b = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(a + b);
    }
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r = dynamic_cast<Rational*>(rand1.get());
        int b = dynamic_cast<Integer*>(rand2.get())->n;
        return normalize_frac(r->numerator + b * r->denominator, r->denominator);
    }
    if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int a = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r = dynamic_cast<Rational*>(rand2.get());
        return normalize_frac(a * r->denominator + r->numerator, r->denominator);
    }
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        return normalize_frac(r1->numerator * r2->denominator + r2->numerator * r1->denominator,
                         r1->denominator * r2->denominator);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int a = dynamic_cast<Integer*>(rand1.get())->n;
        int b = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(a - b);
    }
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r = dynamic_cast<Rational*>(rand1.get());
        int b = dynamic_cast<Integer*>(rand2.get())->n;
        return normalize_frac(r->numerator - b * r->denominator, r->denominator);
    }
    if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int a = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r = dynamic_cast<Rational*>(rand2.get());
        return normalize_frac(a * r->denominator - r->numerator, r->denominator);
    }
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        return normalize_frac(r1->numerator * r2->denominator - r2->numerator * r1->denominator,
                         r1->denominator * r2->denominator);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int a = dynamic_cast<Integer*>(rand1.get())->n;
        int b = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(a * b);
    }
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r = dynamic_cast<Rational*>(rand1.get());
        int b = dynamic_cast<Integer*>(rand2.get())->n;
        return RationalV(r->numerator * b, r->denominator);
    }
    if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int a = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r = dynamic_cast<Rational*>(rand2.get());
        return RationalV(a * r->numerator, r->denominator);
    }
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        return RationalV(r1->numerator * r2->numerator,
                         r1->denominator * r2->denominator);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    if (rand2->v_type == V_INT && dynamic_cast<Integer*>(rand2.get())->n == 0) {
        throw RuntimeError("Division by zero");
    }
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int a = dynamic_cast<Integer*>(rand1.get())->n;
        int b = dynamic_cast<Integer*>(rand2.get())->n;
        return RationalV(a, b);
    }
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r = dynamic_cast<Rational*>(rand1.get());
        int b = dynamic_cast<Integer*>(rand2.get())->n;
        if (b == 0) throw RuntimeError("Division by zero");
        return RationalV(r->numerator, r->denominator * b);
    }
    if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int a = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r = dynamic_cast<Rational*>(rand2.get());
        if (r->numerator == 0) throw RuntimeError("Division by zero");
        return RationalV(a * r->denominator, r->numerator);
    }
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        if (r2->numerator == 0) throw RuntimeError("Division by zero");
        return RationalV(r1->numerator * r2->denominator,
                         r1->denominator * r2->numerator);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    if (args.empty()) return IntegerV(0);
    Value acc = args[0];
    Plus op(Expr(new Fixnum(0)), Expr(new Fixnum(0)));
    for (size_t i = 1; i < args.size(); ++i) acc = op.evalRator(acc, args[i]);
    return acc;
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args
    if (args.empty()) throw RuntimeError("Wrong number of arguments for -");
    Minus op(Expr(new Fixnum(0)), Expr(new Fixnum(0)));
    if (args.size() == 1) {
        return op.evalRator(IntegerV(0), args[0]);
    }
    Value acc = args[0];
    for (size_t i = 1; i < args.size(); ++i) acc = op.evalRator(acc, args[i]);
    return acc;
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args
    if (args.empty()) return IntegerV(1);
    Value acc = args[0];
    Mult op(Expr(new Fixnum(0)), Expr(new Fixnum(0)));
    for (size_t i = 1; i < args.size(); ++i) acc = op.evalRator(acc, args[i]);
    return acc;
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    if (args.empty()) throw RuntimeError("Wrong number of arguments for /");
    Div op(Expr(new Fixnum(0)), Expr(new Fixnum(0)));
    if (args.size() == 1) {
        return op.evalRator(IntegerV(1), args[0]);
    }
    Value acc = args[0];
    for (size_t i = 1; i < args.size(); ++i) acc = op.evalRator(acc, args[i]);
    return acc;
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;
        
        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }
        
        long long result = 1;
        long long b = base;
        int exp = exponent;
        
        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }
        
        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    int c = compareNumericValues(rand1, rand2);
    return BooleanV(c < 0);
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    int c = compareNumericValues(rand1, rand2);
    return BooleanV(c <= 0);
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    int c = compareNumericValues(rand1, rand2);
    return BooleanV(c == 0);
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    int c = compareNumericValues(rand1, rand2);
    return BooleanV(c >= 0);
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    int c = compareNumericValues(rand1, rand2);
    return BooleanV(c > 0);
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    if (args.size() < 2) throw RuntimeError("Wrong number of arguments for <");
    for (size_t i = 1; i < args.size(); ++i) {
        if (compareNumericValues(args[i-1], args[i]) >= 0) return BooleanV(false);
    }
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    if (args.size() < 2) throw RuntimeError("Wrong number of arguments for <=");
    for (size_t i = 1; i < args.size(); ++i) {
        if (compareNumericValues(args[i-1], args[i]) > 0) return BooleanV(false);
    }
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    if (args.size() < 2) throw RuntimeError("Wrong number of arguments for =");
    for (size_t i = 1; i < args.size(); ++i) {
        if (compareNumericValues(args[i-1], args[i]) != 0) return BooleanV(false);
    }
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    if (args.size() < 2) throw RuntimeError("Wrong number of arguments for >=");
    for (size_t i = 1; i < args.size(); ++i) {
        if (compareNumericValues(args[i-1], args[i]) < 0) return BooleanV(false);
    }
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    if (args.size() < 2) throw RuntimeError("Wrong number of arguments for >");
    for (size_t i = 1; i < args.size(); ++i) {
        if (compareNumericValues(args[i-1], args[i]) <= 0) return BooleanV(false);
    }
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function
    Value res = NullV();
    for (int i = (int)args.size() - 1; i >= 0; --i) {
        res = PairV(args[i], res);
    }
    return res;
}

Value IsList::evalRator(const Value &rand) { // list?
    Value v = rand;
    while (v->v_type == V_PAIR) {
        v = dynamic_cast<Pair*>(v.get())->cdr;
    }
    return BooleanV(v->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) { // car
    if (rand->v_type != V_PAIR) throw RuntimeError("car on non-pair");
    return dynamic_cast<Pair*>(rand.get())->car;
}

Value Cdr::evalRator(const Value &rand) { // cdr
    if (rand->v_type != V_PAIR) throw RuntimeError("cdr on non-pair");
    return dynamic_cast<Pair*>(rand.get())->cdr;
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    if (rand1->v_type != V_PAIR) throw RuntimeError("set-car! on non-pair");
    Pair* p = dynamic_cast<Pair*>(rand1.get());
    p->car = rand2;
    return VoidV();
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
    if (rand1->v_type != V_PAIR) throw RuntimeError("set-cdr! on non-pair");
    Pair* p = dynamic_cast<Pair*>(rand1.get());
    p->cdr = rand2;
    return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // Check if type is Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // Check if type is Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // Check if type is Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // Check if type is Null or Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

Value Begin::eval(Assoc &e) {
    Value last = VoidV();
    for (auto &ex : es) last = ex->eval(e);
    return last;
}

Value Quote::eval(Assoc& e) {
    SyntaxBase* sb = s.get();
    if (auto num = dynamic_cast<Number*>(sb)) return IntegerV(num->n);
    if (auto rat = dynamic_cast<RationalSyntax*>(sb)) return RationalV(rat->numerator, rat->denominator);
    if (auto ts = dynamic_cast<TrueSyntax*>(sb)) return BooleanV(true);
    if (auto fs = dynamic_cast<FalseSyntax*>(sb)) return BooleanV(false);
    if (auto ss = dynamic_cast<StringSyntax*>(sb)) return StringV(ss->s);
    if (auto sy = dynamic_cast<SymbolSyntax*>(sb)) return SymbolV(sy->s);
    if (auto lst = dynamic_cast<List*>(sb)) {
        // Detect dotted pair
        int dot_pos = -1;
        for (size_t i = 0; i < lst->stxs.size(); ++i) {
            SymbolSyntax* sym = dynamic_cast<SymbolSyntax*>(lst->stxs[i].get());
            if (sym && sym->s == ".") {
                if (dot_pos != -1) throw RuntimeError("invalid dotted list");
                dot_pos = (int)i;
            }
        }
        if (dot_pos == -1) {
            Value res = NullV();
            for (int i = (int)lst->stxs.size() - 1; i >= 0; --i) {
                Quote q(lst->stxs[i]);
                res = PairV(q.eval(e), res);
            }
            return res;
        } else {
            if (dot_pos == 0 || dot_pos >= (int)lst->stxs.size() - 1) throw RuntimeError("invalid dotted list");
            Quote tail_q(lst->stxs[dot_pos + 1]);
            Value res = tail_q.eval(e);
            for (int i = dot_pos - 1; i >= 0; --i) {
                Quote q(lst->stxs[i]);
                res = PairV(q.eval(e), res);
            }
            return res;
        }
    }
    throw RuntimeError("quote unsupported syntax");
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    if (rands.empty()) return BooleanV(true);
    Value last = BooleanV(true);
    for (auto &ex : rands) {
        Value v = ex->eval(e);
        if (v->v_type == V_BOOL && !dynamic_cast<Boolean*>(v.get())->b) {
            return BooleanV(false);
        }
        last = v;
    }
    return last;
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    if (rands.empty()) return BooleanV(false);
    for (auto &ex : rands) {
        Value v = ex->eval(e);
        if (!(v->v_type == V_BOOL && !dynamic_cast<Boolean*>(v.get())->b)) {
            return v;
        }
    }
    return BooleanV(false);
}

Value Not::evalRator(const Value &rand) { // not
    bool is_false = (rand->v_type == V_BOOL && !dynamic_cast<Boolean*>(rand.get())->b);
    return BooleanV(is_false);
}

Value If::eval(Assoc &e) {
    Value c = cond->eval(e);
    bool truthy = !(c->v_type == V_BOOL && !dynamic_cast<Boolean*>(c.get())->b);
    if (truthy) return conseq->eval(e);
    return alter->eval(e);
}

Value Cond::eval(Assoc &env) {
    for (auto &cl : clauses) {
        if (cl.empty()) continue;
        // else clause
        if (auto v0 = cl[0]->eval(env); !(v0->v_type == V_BOOL && !dynamic_cast<Boolean*>(v0.get())->b)) {
            Value last = v0;
            for (size_t i = 1; i < cl.size(); ++i) last = cl[i]->eval(env);
            return last;
        }
    }
    return VoidV();
}

Value Lambda::eval(Assoc &env) {
    return ProcedureV(x, e, env);
}

Value Apply::eval(Assoc &e) {
    Value op = rator->eval(e);
    if (op->v_type != V_PROC) {throw RuntimeError("Attempt to apply a non-procedure");}
    Procedure* clos_ptr = dynamic_cast<Procedure*>(op.get());

    std::vector<Value> args;
    for (auto &a : rand) args.push_back(a->eval(e));
    if (args.size() != clos_ptr->parameters.size()) throw RuntimeError("Wrong number of arguments");

    Assoc new_env = clos_ptr->env;
    for (size_t i = 0; i < clos_ptr->parameters.size(); ++i) {
        new_env = extend(clos_ptr->parameters[i], args[i], new_env);
    }
    return clos_ptr->e->eval(new_env);
}

Value Define::eval(Assoc &env) {
    // allow redefine; evaluate e first
    Value val = e->eval(env);
    Value existing = find(var, env);
    if (existing.get() == nullptr) {
        env = extend(var, val, env);
    } else {
        modify(var, val, env);
    }
    return SymbolV(var);
}

Value Let::eval(Assoc &env) {
    Assoc new_env = env;
    for (auto &bv : bind) {
        Value v = bv.second->eval(new_env);
        new_env = extend(bv.first, v, new_env);
    }
    return body->eval(new_env);
}

Value Letrec::eval(Assoc &env) {
    Assoc env1 = env;
    for (auto &bv : bind) {
        env1 = extend(bv.first, Value(nullptr), env1);
    }
    // evaluate values in env1
    std::vector<Value> vals;
    for (auto &bv : bind) {
        vals.push_back(bv.second->eval(env1));
    }
    Assoc env2 = env1;
    for (size_t i = 0; i < bind.size(); ++i) {
        modify(bind[i].first, vals[i], env2);
    }
    return body->eval(env2);
}

Value Set::eval(Assoc &env) {
    Value v = e->eval(env);
    Value existing = find(var, env);
    if (existing.get() == nullptr) throw RuntimeError("undefined");
    modify(var, v, env);
    return VoidV();
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }
    
    return VoidV();
}
