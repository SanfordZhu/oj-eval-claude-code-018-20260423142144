/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 * 
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    //TODO: check if the first element is a symbol
    //If not, use Apply function to package to a closure;
    //If so, find whether it's a variable or a keyword;
    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        std::vector<Expr> args;
        for (size_t i = 1; i < stxs.size(); ++i) args.push_back(stxs[i].parse(env));
        return Expr(new Apply(stxs[0].parse(env), args));
    }else{
    string op = id->s;
    if (find(op, env).get() != nullptr) {
        std::vector<Expr> args;
        for (size_t i = 1; i < stxs.size(); ++i) args.push_back(stxs[i].parse(env));
        return Expr(new Apply(Expr(new Var(op)), args));
    }
    if (primitives.count(op) != 0) {
        vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); ++i) parameters.push_back(stxs[i].parse(env));
        ExprType op_type = primitives[op];
        if (op_type == E_PLUS) {
            if (parameters.size() == 2) return Expr(new Plus(parameters[0], parameters[1]));
            return Expr(new PlusVar(parameters));
        } else if (op_type == E_MINUS) {
            if (parameters.size() == 2) return Expr(new Minus(parameters[0], parameters[1]));
            return Expr(new MinusVar(parameters));
        } else if (op_type == E_MUL) {
            if (parameters.size() == 2) return Expr(new Mult(parameters[0], parameters[1]));
            return Expr(new MultVar(parameters));
        }  else if (op_type == E_DIV) {
            if (parameters.size() == 2) return Expr(new Div(parameters[0], parameters[1]));
            return Expr(new DivVar(parameters));
        } else if (op_type == E_MODULO) {
            if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for modulo");
            return Expr(new Modulo(parameters[0], parameters[1]));
        } else if (op_type == E_LIST) {
            return Expr(new ListFunc(parameters));
        } else if (op_type == E_CONS) {
            if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for cons");
            return Expr(new Cons(parameters[0], parameters[1]));
        } else if (op_type == E_CAR) {
            if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for car");
            return Expr(new Car(parameters[0]));
        } else if (op_type == E_CDR) {
            if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for cdr");
            return Expr(new Cdr(parameters[0]));
        } else if (op_type == E_SETCAR) {
            if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for set-car!");
            return Expr(new SetCar(parameters[0], parameters[1]));
        } else if (op_type == E_SETCDR) {
            if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for set-cdr!");
            return Expr(new SetCdr(parameters[0], parameters[1]));
        } else if (op_type == E_LT) {
            if (parameters.size() == 2) return Expr(new Less(parameters[0], parameters[1]));
            return Expr(new LessVar(parameters));
        } else if (op_type == E_LE) {
            if (parameters.size() == 2) return Expr(new LessEq(parameters[0], parameters[1]));
            return Expr(new LessEqVar(parameters));
        } else if (op_type == E_EQ) {
            if (parameters.size() == 2) return Expr(new Equal(parameters[0], parameters[1]));
            return Expr(new EqualVar(parameters));
        } else if (op_type == E_GE) {
            if (parameters.size() == 2) return Expr(new GreaterEq(parameters[0], parameters[1]));
            return Expr(new GreaterEqVar(parameters));
        } else if (op_type == E_GT) {
            if (parameters.size() == 2) return Expr(new Greater(parameters[0], parameters[1]));
            return Expr(new GreaterVar(parameters));
        } else if (op_type == E_AND) {
            return Expr(new AndVar(parameters));
        } else if (op_type == E_OR) {
            return Expr(new OrVar(parameters));
        } else if (op_type == E_NOT) {
            if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for not");
            return Expr(new Not(parameters[0]));
        } else if (op_type == E_EQQ) {
            if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for eq?");
            return Expr(new IsEq(parameters[0], parameters[1]));
        } else if (op_type == E_BOOLQ) {
            if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for boolean?");
            return Expr(new IsBoolean(parameters[0]));
        } else if (op_type == E_INTQ) {
            if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for number?");
            return Expr(new IsFixnum(parameters[0]));
        } else if (op_type == E_NULLQ) {
            if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for null?");
            return Expr(new IsNull(parameters[0]));
        } else if (op_type == E_PAIRQ) {
            if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for pair?");
            return Expr(new IsPair(parameters[0]));
        } else if (op_type == E_PROCQ) {
            if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for procedure?");
            return Expr(new IsProcedure(parameters[0]));
        } else if (op_type == E_SYMBOLQ) {
            if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for symbol?");
            return Expr(new IsSymbol(parameters[0]));
        } else if (op_type == E_LISTQ) {
            if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for list?");
            return Expr(new IsList(parameters[0]));
        } else if (op_type == E_STRINGQ) {
            if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for string?");
            return Expr(new IsString(parameters[0]));
        } else if (op_type == E_DISPLAY) {
            if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for display");
            return Expr(new Display(parameters[0]));
        } else if (op_type == E_VOID) {
            return Expr(new MakeVoid());
        } else if (op_type == E_EXIT) {
            return Expr(new Exit());
        }
    }

    if (reserved_words.count(op) != 0) {
    	switch (reserved_words[op]) {
			//TODO: TO COMPLETE THE reserve_words PARSER LOGIC
        	default:
            	throw RuntimeError("Unknown reserved word: " + op);
    	}
    }

    if (reserved_words.count(op) != 0) {
            switch (reserved_words[op]) {
                case E_BEGIN: {
                    std::vector<Expr> exprs;
                    for (size_t i = 1; i < stxs.size(); ++i) exprs.push_back(stxs[i].parse(env));
                    return Expr(new Begin(exprs));
                }
                case E_QUOTE: {
                    if (stxs.size() < 2) throw RuntimeError("quote needs an argument");
                    return Expr(new Quote(stxs[1]));
                }
                case E_IF: {
                    if (stxs.size() != 4) throw RuntimeError("if needs 3 arguments");
                    return Expr(new If(stxs[1].parse(env), stxs[2].parse(env), stxs[3].parse(env)));
                }
                case E_COND: {
                    std::vector<std::vector<Expr>> clauses;
                    for (size_t i = 1; i < stxs.size(); ++i) {
                        List* clause = dynamic_cast<List*>(stxs[i].get());
                        if (!clause) throw RuntimeError("cond clause must be list");
                        std::vector<Expr> ces;
                        for (auto &sx : clause->stxs) ces.push_back(sx.parse(env));
                        clauses.push_back(ces);
                    }
                    return Expr(new Cond(clauses));
                }
                case E_LAMBDA: {
                    List* params = dynamic_cast<List*>(stxs[1].get());
                    if (!params) throw RuntimeError("lambda params must be list");
                    std::vector<std::string> xs;
                    for (auto &sx : params->stxs) {
                        SymbolSyntax* sym = dynamic_cast<SymbolSyntax*>(sx.get());
                        if (!sym) throw RuntimeError("lambda param must be symbol");
                        xs.push_back(sym->s);
                    }
                    if (stxs.size() == 3) return Expr(new Lambda(xs, stxs[2].parse(env)));
                    std::vector<Expr> bodies;
                    for (size_t i = 2; i < stxs.size(); ++i) bodies.push_back(stxs[i].parse(env));
                    return Expr(new Lambda(xs, Expr(new Begin(bodies))));
                }
                case E_DEFINE: {
                    if (stxs.size() < 3) throw RuntimeError("define needs at least 2 args");
                    List* func = dynamic_cast<List*>(stxs[1].get());
                    if (func) {
                        if (func->stxs.empty()) throw RuntimeError("define function name missing");
                        SymbolSyntax* fname = dynamic_cast<SymbolSyntax*>(func->stxs[0].get());
                        if (!fname) throw RuntimeError("define function name must be symbol");
                        std::vector<std::string> xs;
                        for (size_t i = 1; i < func->stxs.size(); ++i) {
                            SymbolSyntax* sym = dynamic_cast<SymbolSyntax*>(func->stxs[i].get());
                            if (!sym) throw RuntimeError("define param must be symbol");
                            xs.push_back(sym->s);
                        }
                        std::vector<Expr> bodies;
                        for (size_t i = 2; i < stxs.size(); ++i) bodies.push_back(stxs[i].parse(env));
                        Expr lam = Expr(new Lambda(xs, bodies.size()==1? bodies[0] : Expr(new Begin(bodies))));
                        return Expr(new Define(fname->s, lam));
                    } else {
                        SymbolSyntax* sym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                        if (!sym) throw RuntimeError("define variable must be symbol");
                        Expr val = stxs[2].parse(env);
                        if (stxs.size() > 3) {
                            std::vector<Expr> bodies;
                            for (size_t i = 2; i < stxs.size(); ++i) bodies.push_back(stxs[i].parse(env));
                            val = Expr(new Begin(bodies));
                        }
                        return Expr(new Define(sym->s, val));
                    }
                }
                case E_LET: {
                    if (stxs.size() < 3) throw RuntimeError("let needs bindings and body");
                    List* binds = dynamic_cast<List*>(stxs[1].get());
                    if (!binds) throw RuntimeError("let bindings must be list");
                    std::vector<std::pair<std::string, Expr>> bvs;
                    for (auto &b : binds->stxs) {
                        List* pairl = dynamic_cast<List*>(b.get());
                        if (!pairl || pairl->stxs.size() != 2) throw RuntimeError("let binding must be (x e)");
                        SymbolSyntax* sx = dynamic_cast<SymbolSyntax*>(pairl->stxs[0].get());
                        if (!sx) throw RuntimeError("let binding name must be symbol");
                        bvs.push_back({sx->s, pairl->stxs[1].parse(env)});
                    }
                    std::vector<Expr> bodies;
                    for (size_t i = 2; i < stxs.size(); ++i) bodies.push_back(stxs[i].parse(env));
                    return Expr(new Let(bvs, bodies.size()==1? bodies[0] : Expr(new Begin(bodies))));
                }
                case E_LETREC: {
                    if (stxs.size() < 3) throw RuntimeError("letrec needs bindings and body");
                    List* binds = dynamic_cast<List*>(stxs[1].get());
                    if (!binds) throw RuntimeError("letrec bindings must be list");
                    std::vector<std::pair<std::string, Expr>> bvs;
                    for (auto &b : binds->stxs) {
                        List* pairl = dynamic_cast<List*>(b.get());
                        if (!pairl || pairl->stxs.size() != 2) throw RuntimeError("letrec binding must be (x e)");
                        SymbolSyntax* sx = dynamic_cast<SymbolSyntax*>(pairl->stxs[0].get());
                        if (!sx) throw RuntimeError("letrec binding name must be symbol");
                        bvs.push_back({sx->s, pairl->stxs[1].parse(env)});
                    }
                    std::vector<Expr> bodies;
                    for (size_t i = 2; i < stxs.size(); ++i) bodies.push_back(stxs[i].parse(env));
                    return Expr(new Letrec(bvs, bodies.size()==1? bodies[0] : Expr(new Begin(bodies))));
                }
                case E_SET: {
                    if (stxs.size() != 3) throw RuntimeError("set! needs 2 args");
                    SymbolSyntax* sx = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                    if (!sx) throw RuntimeError("set! target must be symbol");
                    return Expr(new Set(sx->s, stxs[2].parse(env)));
                }
                default:
                    throw RuntimeError("Unknown reserved word: " + op);
            }
    }

    std::vector<Expr> args;
    for (size_t i = 1; i < stxs.size(); ++i) args.push_back(stxs[i].parse(env));
    return Expr(new Apply(Expr(new Var(op)), args));
}
}
