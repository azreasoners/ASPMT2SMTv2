#!/usr/bin/env python3
"""
aspmt2smt.py  --  ASPMT -> SMT compiler  (re-implementation)

Paper: "System aspmt2smt: Computing ASPMT Theories by SMT Solvers"
       Michael Bartholomew & Joohyung Lee, JELIA 2014

Pipeline
========
  1. Parse ASPMT declarations (sorts / objects / constants / variables) and rules.
  2. Substitute user-supplied parameters  (-c name=val …).
  3. Expand sort domains  (e.g. "0..st" -> {0,1,2,3} when st=3).
  4. Ground rules: substitute ASP-variables (discrete sorts) with ground objects.
  5. Compute Clark completion  (tight-program assumption).
  6. Variable elimination: SMT value-variables -> function-application names.
  7. Emit SMT-LIB 2.6 (declare-const + assert + check-sat + get-model).
  8. Call Z3 and print the model.

Input syntax (ASPMT)
====================
  :- sorts
     step; astep.

  :- objects
     0..st   :: step;
     0..st-1 :: astep.

  :- constants
     speed(step)    :: real[0..ms];
     accel(astep)   :: boolean;
     duration(astep):: real[0..ms].

  :- variables
     S :: astep;
     X, Y, D :: real.

  {accel(S)=true}.
  speed(S+1)=Y <- accel(S)=true & speed(S)=X & duration(S)=D & Y=X+ar*D.
  <- not speed(0)=0.

  :- show
     speed/1; accel/1.

Usage
=====
  python aspmt2smt.py examples/car.aspmt -c st=3 -c ar=3 -c ms=4 -c l=10
  python aspmt2smt.py examples/bucket.aspmt -c st=5 -c cap=10 -c init=5 -c target=7
  python aspmt2smt.py examples/ball.aspmt -c st=4 -c g=9.8 -c r=95 -c h0=10
  python aspmt2smt.py examples/car.aspmt -c st=3 -c ar=3 -c ms=4 -c l=10 --show-smt --no-z3
"""

import re, sys, os, subprocess, argparse
from itertools import product
from collections import defaultdict
from typing import Any, Dict, List, Optional, Set, Tuple

# ════════════════════════════════════════════════════════════════════════════
# §1  Expression AST
#     All nodes are plain immutable tuples so they can be used as dict keys.
#
#   ('num',    value)          numeric literal  (int or float)
#   ('var',    name)           variable / free name
#   ('app',    fname, args)    function application  f(a1,…,an), args is tuple
#   ('binop',  op, lhs, rhs)   arithmetic: +  -  *  /
#   ('unary',  op,  operand)   unary minus
# ════════════════════════════════════════════════════════════════════════════

def Num(v):           return ('num', v)
def Var(n):           return ('var', n)
def App(f, a):        return ('app', f, tuple(a))
def BinOp(op, a, b):  return ('binop', op, a, b)
def UnOp(op, a):      return ('unary', op, a)


def expr_vars(e) -> Set[str]:
    """All variable names that appear (free) in expression e."""
    t = e[0]
    if t == 'num':    return set()
    if t == 'var':    return {e[1]}
    if t == 'app':    return set().union(*(expr_vars(a) for a in e[2]))
    if t == 'binop':  return expr_vars(e[2]) | expr_vars(e[3])
    if t == 'unary':  return expr_vars(e[2])
    return set()


def expr_subst(e, env: Dict[str, Any]):
    """Replace variables in e using env  {name → number | expr-tuple}."""
    t = e[0]
    if t == 'num':   return e
    if t == 'var':
        n = e[1]
        if n in env:
            v = env[n]
            return Num(v) if isinstance(v, (int, float)) else v
        return e
    if t == 'app':
        return App(e[1], [expr_subst(a, env) for a in e[2]])
    if t == 'binop':
        return BinOp(e[1], expr_subst(e[2], env), expr_subst(e[3], env))
    if t == 'unary':
        return UnOp(e[1], expr_subst(e[2], env))
    return e


def expr_simplify(e):
    """Constant-fold all-numeric sub-expressions.

    After substituting ground values, expressions like BinOp('+', Num(0), Num(1))
    should be reduced to Num(1) so they can be used as dict keys / ground args.
    """
    t = e[0]
    if t == 'num':    return e
    if t == 'var':    return e
    if t == 'app':
        new_args = [expr_simplify(a) for a in e[2]]
        return App(e[1], new_args)
    if t == 'binop':
        l = expr_simplify(e[2])
        r = expr_simplify(e[3])
        if l[0] == 'num' and r[0] == 'num':
            lv, rv, op = l[1], r[1], e[1]
            if op == '+': return Num(lv + rv)
            if op == '-': return Num(lv - rv)
            if op == '*': return Num(lv * rv)
            if op == '/' and rv != 0: return Num(lv / rv)
        return BinOp(e[1], l, r)
    if t == 'unary':
        v = expr_simplify(e[2])
        if e[1] == '-' and v[0] == 'num':
            return Num(-v[1])
        return UnOp(e[1], v)
    return e


def expr_eval(e, env: Dict[str, Any]):
    """Evaluate e to a number given variable bindings env.
    Raises ValueError if e cannot be reduced to a number."""
    t = e[0]
    if t == 'num':   return e[1]
    if t == 'var':
        n = e[1]
        if n in env:
            v = env[n]
            if isinstance(v, (int, float)): return v
            return expr_eval(v, env)
        raise ValueError(f"Unbound variable '{n}'")
    if t == 'app':
        fname = e[1]
        if fname in env:
            v = env[fname]
            if isinstance(v, (int, float)): return v
        raise ValueError(f"Cannot evaluate function application '{fname}'")
    if t == 'binop':
        op = e[1]
        l = expr_eval(e[2], env)
        r = expr_eval(e[3], env)
        if op == '+': return l + r
        if op == '-': return l - r
        if op == '*': return l * r
        if op == '/': return l / r
    if t == 'unary':
        v = expr_eval(e[2], env)
        if e[1] == '-': return -v
        return v
    raise ValueError(f"Cannot evaluate: {e}")


def expr_to_smt(e, gc: Dict, params: Dict) -> str:
    """Convert expression e to an SMT-LIB 2 string.

    gc     — maps (fname, ground_args_tuple) → smt_variable_name
    params — numeric parameters  {name → number}
    """
    t = e[0]
    if t == 'num':
        v = e[1]
        # Use real literals when in a real context; keep ints as ints
        if isinstance(v, float):
            return f"{v}" if v != int(v) else f"{int(v)}.0"
        return str(v)
    if t == 'var':
        n = e[1]
        if n in params:
            v = params[n]
            if isinstance(v, float):
                return f"{v}" if v != int(v) else f"{int(v)}.0"
            return str(v)
        return n   # leave unknown names as-is (should not happen after grounding)
    if t == 'app':
        fname, args = e[1], e[2]
        try:
            gargs = tuple(int(expr_eval(a, params)) for a in args)
            key = (fname, gargs)
            if key in gc:
                return gc[key]
        except ValueError:
            pass
        # Fallback: inline
        arg_smts = [expr_to_smt(a, gc, params) for a in args]
        return fname + '_' + '_'.join(arg_smts) + '_'
    if t == 'binop':
        op, l, r = e[1], e[2], e[3]
        ls = expr_to_smt(l, gc, params)
        rs = expr_to_smt(r, gc, params)
        return f"({op} {ls} {rs})"
    if t == 'unary':
        op, v = e[1], e[2]
        vs = expr_to_smt(v, gc, params)
        if op == '-': return f"(- {vs})"
        return vs
    raise ValueError(f"Cannot convert to SMT: {e}")


# ════════════════════════════════════════════════════════════════════════════
# §2  Tokenizer
# ════════════════════════════════════════════════════════════════════════════

_TOK_RE = re.compile(
    # IMPORTANT: float literals MUST require digits on both sides of '.'
    # so that '0..st' is not tokenized as float '0.' + dot + identifier.
    r'(\d+\.\d+|\.\d+|\d+)'                             # NUM  (float needs digits after '.')
    r'|([A-Z_][A-Za-z0-9_]*)'                           # VAR  (uppercase first)
    r'|([a-z_][A-Za-z0-9_]*)'                           # ID   (lowercase / keyword)
    r'|(::|\.\.|->|<-|>=|<=|!=|[+\-*/^().,;:{}<>=!&|@#\\\[\]])'  # OP ('::' and '[',']' included)
    r'|(%[^\n]*)'                                        # % comment (skip)
    r'|(\s+)',                                           # whitespace (skip)
    re.DOTALL
)


def tokenize(s: str) -> List[Tuple[str, str]]:
    toks: List[Tuple[str, str]] = []
    for m in _TOK_RE.finditer(s):
        num, var_, ident, op, cmt, ws = m.groups()
        if ws or cmt:
            continue
        if num:
            toks.append(('NUM', num))
        elif var_:
            toks.append(('VAR', var_))
        elif ident:
            toks.append(('ID', ident))
        elif op:
            toks.append(('OP', op))
    toks.append(('EOF', ''))
    return toks


class Scan:
    """Simple token stream cursor."""
    def __init__(self, toks: List[Tuple[str, str]]):
        self.t = toks
        self.i = 0

    def peek(self, ahead: int = 0) -> Tuple[str, str]:
        j = self.i + ahead
        return self.t[j] if j < len(self.t) else ('EOF', '')

    def consume(self, v: str = None) -> Tuple[str, str]:
        tok = self.t[self.i]
        if v is not None and tok[1] != v:
            raise SyntaxError(
                f"Expected {v!r} but got {tok[1]!r}  (token #{self.i})"
            )
        self.i += 1
        return tok

    def match(self, v: str) -> bool:
        if self.peek()[1] == v:
            self.consume()
            return True
        return False

    def match_type(self, tp: str) -> Optional[Tuple[str, str]]:
        if self.peek()[0] == tp:
            return self.consume()
        return None


# ════════════════════════════════════════════════════════════════════════════
# §3  Expression parser   (arithmetic, function applications)
# ════════════════════════════════════════════════════════════════════════════

class ExprP:
    """Recursive-descent arithmetic expression parser."""

    def __init__(self, sc: Scan):
        self.sc = sc

    def parse(self):
        return self._add()

    def _add(self):
        n = self._mul()
        while self.sc.peek()[1] in ('+', '-') and self.sc.peek()[0] == 'OP':
            op = self.sc.consume()[1]
            r = self._mul()
            n = BinOp(op, n, r)
        return n

    def _mul(self):
        n = self._unary()
        while self.sc.peek()[1] in ('*', '/') and self.sc.peek()[0] == 'OP':
            op = self.sc.consume()[1]
            r = self._unary()
            n = BinOp(op, n, r)
        return n

    def _unary(self):
        if self.sc.peek() == ('OP', '-'):
            self.sc.consume()
            return UnOp('-', self._atom())
        self.sc.match('+')
        return self._atom()

    def _atom(self):
        t = self.sc.peek()
        if t[0] == 'NUM':
            self.sc.consume()
            v = t[1]
            return Num(float(v) if '.' in v else int(v))
        if t[0] in ('ID', 'VAR'):
            name = self.sc.consume()[1]
            if self.sc.peek()[1] == '(':
                self.sc.consume('(')
                args = []
                if self.sc.peek()[1] != ')':
                    args.append(self.parse())
                    while self.sc.match(','):
                        args.append(self.parse())
                self.sc.consume(')')
                return App(name, args)
            return Var(name)
        if self.sc.peek() == ('OP', '('):
            self.sc.consume()
            e = self.parse()
            self.sc.consume(')')
            return e
        raise SyntaxError(f"Unexpected token in expression: {t!r}")


def parse_expr_sc(sc: Scan):
    return ExprP(sc).parse()


# ════════════════════════════════════════════════════════════════════════════
# §4  Atom parser   f(args) = value  or  f(args)  (= f(args)=true)
#     Returns a dict  { 'func': str, 'args': [expr], 'value': expr,
#                       'negated': bool }
# ════════════════════════════════════════════════════════════════════════════

def parse_atom_sc(sc: Scan, const_names: Set[str]) -> dict:
    """Parse one body / head atom from the scanner.

    An atom is one of:
      f(t1,...,tn) = v      function assignment
      f(t1,...,tn)          shorthand for f(t1,...,tn) = true
      t1 = t2               pure arithmetic equality (when t1 is not a const name)
      not <atom>            negation
    """
    negated = False
    if sc.peek() == ('ID', 'not'):
        sc.consume()
        negated = True

    # Parse left-hand side expression
    lhs = parse_expr_sc(sc)

    # Now check for '='
    if sc.peek()[1] == '=':
        sc.consume()
        rhs = parse_expr_sc(sc)
    else:
        # No '=': treat as f(args) = true
        rhs = Var('true')

    return {'func_expr': lhs, 'value': rhs, 'negated': negated}


# ════════════════════════════════════════════════════════════════════════════
# §5  Rule / Program parser
# ════════════════════════════════════════════════════════════════════════════

class Program:
    """Holds all parsed declarations and rules."""

    def __init__(self):
        self.sorts: Dict[str, List] = {}          # sort_name → [objects]
        self.const_decls: Dict[str, dict] = {}    # const_name → {arg_sorts, val_sort, bounds}
        self.var_decls: Dict[str, str] = {}       # var_name → sort
        self.rules: List[dict] = []               # see parse_rule for schema
        self.show: List[str] = []                 # const names to display


def _parse_sort_list(sc: Scan) -> List[str]:
    """Parse  'sort1; sort2; ...' stopping before '.'"""
    sorts = []
    while True:
        t = sc.match_type('ID')
        if t:
            sorts.append(t[1])
        if not sc.match(';'):
            break
    return sorts


def _parse_range_expr(sc: Scan, params: Dict[str, Any]):
    """Parse a range spec like  '0..st-1'  or  '0..st'  → (lo_expr, hi_expr)"""
    lo = parse_expr_sc(sc)
    sc.consume('..')
    hi = parse_expr_sc(sc)
    return lo, hi


def _parse_object_list(sc: Scan, params: Dict[str, Any]) -> Tuple[List, str]:
    """Parse  'range_or_list :: sortname'  →  (objects, sortname)"""
    # collect comma-separated items until '::'
    # Items may be ranges or plain names
    items_lo = []
    items_hi = []
    is_range = False

    first_expr = parse_expr_sc(sc)
    if sc.peek() == ('OP', '..'):
        sc.consume()
        second_expr = parse_expr_sc(sc)
        is_range = True
        items_lo = [first_expr]
        items_hi = [second_expr]
    else:
        items_lo = [first_expr]
        items_hi = [None]
        while sc.match(','):
            items_lo.append(parse_expr_sc(sc))
            items_hi.append(None)

    sc.consume('::')
    sort_name = sc.consume()[1]

    objects = []
    for lo_e, hi_e in zip(items_lo, items_hi):
        try:
            lo_v = int(expr_eval(lo_e, params))
        except ValueError:
            lo_v = lo_e
        if hi_e is not None:
            try:
                hi_v = int(expr_eval(hi_e, params))
                objects.extend(range(lo_v, hi_v + 1))
            except (ValueError, TypeError):
                raise ValueError(
                    f"Could not evaluate range hi bound: {hi_e}"
                )
        else:
            objects.append(lo_v)

    return objects, sort_name


def _parse_val_sort(sc: Scan) -> Tuple[str, Optional[Any], Optional[Any]]:
    """Parse  'boolean' | 'integer' | 'real' | 'real[lo..hi]' | sort_name
    Returns  (base_sort, lo_bound, hi_bound)."""
    name = sc.consume()[1]          # ID: boolean / integer / real / sort_name
    lo, hi = None, None
    if sc.peek() == ('OP', '['):
        sc.consume()
        lo = parse_expr_sc(sc)
        sc.consume('..')
        hi = parse_expr_sc(sc)
        sc.consume(']')
    return name, lo, hi


def parse_program(text: str, params: Dict[str, Any]) -> Program:
    """Parse the full ASPMT program text and return a Program object."""

    prog = Program()
    toks = tokenize(text)
    sc = Scan(toks)

    while sc.peek()[0] != 'EOF':
        # ── directive  :- keyword ... .  ────────────────────────────
        if sc.peek() == ('OP', ':') and sc.peek(1) == ('OP', '-'):
            sc.consume(); sc.consume()
            kw = sc.consume()[1]    # sorts / objects / constants / variables / show

            if kw == 'sorts':
                names = _parse_sort_list(sc)
                for n in names:
                    prog.sorts[n] = []

            elif kw == 'objects':
                while True:
                    objs, sname = _parse_object_list(sc, params)
                    if sname not in prog.sorts:
                        prog.sorts[sname] = []
                    prog.sorts[sname].extend(objs)
                    if not sc.match(';'):
                        break

            elif kw == 'constants':
                while True:
                    cname = sc.consume()[1]   # constant name
                    # optional argument sorts
                    arg_sorts: List[str] = []
                    if sc.peek()[1] == '(':
                        sc.consume()
                        if sc.peek()[1] != ')':
                            arg_sorts.append(sc.consume()[1])
                            while sc.match(','):
                                arg_sorts.append(sc.consume()[1])
                        sc.consume(')')
                    sc.consume('::')
                    val_sort, lo, hi = _parse_val_sort(sc)
                    prog.const_decls[cname] = {
                        'arg_sorts': arg_sorts,
                        'val_sort': val_sort,
                        'lo': lo, 'hi': hi
                    }
                    if not sc.match(';'):
                        break

            elif kw == 'variables':
                while True:
                    # one or more var names, then :: sort
                    vnames = [sc.consume()[1]]
                    while sc.match(','):
                        vnames.append(sc.consume()[1])
                    sc.consume('::')
                    vsort = sc.consume()[1]
                    for vn in vnames:
                        prog.var_decls[vn] = vsort
                    if not sc.match(';'):
                        break

            elif kw == 'show':
                while True:
                    cname = sc.consume()[1]
                    sc.consume('/')
                    _arity = sc.consume()[1]
                    prog.show.append(cname)
                    if not sc.match(';'):
                        break

            else:
                # skip unknown directive body
                while sc.peek()[1] not in ('.', '') and sc.peek()[0] != 'EOF':
                    sc.consume()

            sc.match('.')   # consume trailing dot if present

        # ── Choice rule  {head}.  ───────────────────────────────────
        elif sc.peek() == ('OP', '{'):
            sc.consume()
            head_tok, body_toks = _split_rule_tokens(sc, prog.const_decls)
            sc.consume('}')
            sc.consume('.')
            rule = _build_rule(head_tok, [], True, prog.const_decls)
            prog.rules.append(rule)

        # ── Integrity constraint  :- B.  (leading '<-')  ───────────
        elif sc.peek() == ('OP', '<-') or (
            sc.peek() == ('OP', ':') and sc.peek(1) == ('OP', '-')
        ):
            # integrity constraint syntax varies; handle '<- B.'
            if sc.peek() == ('OP', '<-'):
                sc.consume()
            else:
                sc.consume(); sc.consume()  # ':' '-'
            body_atoms = _parse_body(sc, prog.const_decls)
            sc.match('.')
            prog.rules.append({
                'head': None,          # constraint: head is False (⊥)
                'body': body_atoms,
                'is_choice': False,
                'is_constraint': True
            })

        # ── Normal rule  Head <- Body.  or  Head.  ──────────────────
        elif sc.peek()[0] in ('ID', 'VAR') or (
            sc.peek() == ('OP', 'not')
        ):
            # Parse up to '.' collecting tokens
            rule_toks = _collect_rule_tokens(sc)
            rule = _parse_rule_from_tokens(rule_toks, prog.const_decls)
            prog.rules.append(rule)

        else:
            # skip unexpected tokens
            sc.consume()

    return prog


# ── Helpers for rule parsing ─────────────────────────────────────────────────

def _collect_rule_tokens(sc: Scan) -> List[Tuple[str, str]]:
    """Collect tokens up to and including the terminating '.'"""
    toks = []
    depth = 0
    while True:
        t = sc.peek()
        if t[0] == 'EOF':
            break
        if t[1] == '(':
            depth += 1
        elif t[1] == ')':
            depth -= 1
        if t[1] == '.' and depth == 0:
            sc.consume()
            break
        toks.append(sc.consume())
    toks.append(('EOF', ''))
    return toks


def _split_rule_tokens(sc: Scan, const_decls: dict):
    """Read tokens inside a choice rule {}; return head tokens only (body empty)."""
    toks = []
    depth = 0
    while True:
        t = sc.peek()
        if t[0] == 'EOF' or (t[1] == '}' and depth == 0):
            break
        if t[1] == '(':
            depth += 1
        elif t[1] == ')':
            depth -= 1
        toks.append(sc.consume())
    toks.append(('EOF', ''))
    return toks, []


def _parse_rule_from_tokens(
    toks: List[Tuple[str, str]],
    const_decls: dict
) -> dict:
    """Given a token list for a rule (without trailing '.'), parse it."""
    sc = Scan(toks)

    # Find '<-' to split head/body
    arrow_pos = None
    depth = 0
    for i, tok in enumerate(toks):
        if tok[1] == '(':
            depth += 1
        elif tok[1] == ')':
            depth -= 1
        elif tok[1] == '<-' and depth == 0:
            arrow_pos = i
            break

    if arrow_pos is not None:
        head_toks = toks[:arrow_pos] + [('EOF', '')]
        body_toks = toks[arrow_pos + 1:]
        head_sc = Scan(head_toks)
        body_sc = Scan(body_toks)
        head_atom = _parse_single_atom(head_sc, const_decls)
        body_atoms = _parse_body(body_sc, const_decls)
    else:
        # Fact: Head only
        head_atom = _parse_single_atom(sc, const_decls)
        body_atoms = []

    return _build_rule(None, body_atoms, False, const_decls,
                       head_atom=head_atom)


def _build_rule(head_toks, body_atoms, is_choice, const_decls,
                head_atom=None):
    if head_toks is not None and head_atom is None:
        sc2 = Scan(head_toks)
        head_atom = _parse_single_atom(sc2, const_decls)
    return {
        'head': head_atom,
        'body': body_atoms,
        'is_choice': is_choice,
        'is_constraint': False
    }


def _parse_single_atom(sc: Scan, const_decls: dict) -> dict:
    """Parse one atom from the scanner (head or body, no negation at top level here)."""
    lhs = parse_expr_sc(sc)
    cmp_op = '='
    if sc.peek()[1] in _CMP_OPS:
        cmp_op = sc.consume()[1]
        rhs = parse_expr_sc(sc)
    else:
        rhs = Var('true')
    return {'lhs': lhs, 'rhs': rhs, 'cmp': cmp_op, 'negated': False}


_CMP_OPS = {'=', '!=', '>=', '<=', '>', '<'}


def _parse_body(sc: Scan, const_decls: dict) -> List[dict]:
    """Parse  atom1 & atom2 & ... from sc.

    Each atom has the form:
      [not]  expr  [cmp_op  expr]
    where cmp_op ∈ {=, !=, >=, <=, >, <}.
    If no cmp_op follows, the value defaults to 'true'.
    """
    atoms = []
    while sc.peek()[0] != 'EOF':
        negated = False
        if sc.peek() == ('ID', 'not'):
            sc.consume()
            negated = True
        lhs = parse_expr_sc(sc)
        cmp_op = '='
        if sc.peek()[1] in _CMP_OPS:
            cmp_op = sc.consume()[1]
            rhs = parse_expr_sc(sc)
        else:
            rhs = Var('true')
        atoms.append({'lhs': lhs, 'rhs': rhs, 'cmp': cmp_op, 'negated': negated})
        if not sc.match('&'):
            break
    return atoms


def _make_atom(lhs, rhs, cmp='=', negated=False):
    return {'lhs': lhs, 'rhs': rhs, 'cmp': cmp, 'negated': negated}


# ════════════════════════════════════════════════════════════════════════════
# §6  Grounding
#     Replace all "ASP variables" (those with discrete / integer-range sorts)
#     with concrete ground values.  SMT variables (real / integer sorts)
#     remain symbolic.
# ════════════════════════════════════════════════════════════════════════════

_SMT_SORTS = {'real', 'integer', 'int'}


def is_smt_sort(sort: str) -> bool:
    return sort.lower() in _SMT_SORTS


def ground_program(prog: Program, params: Dict[str, Any]) -> List[dict]:
    """Return a flat list of ground rules.

    ASP variables (those with discrete / integer-range sorts) are
    substituted with all possible ground values.  SMT variables (real /
    integer sorts) remain symbolic.  Numeric parameters (st, ar, …) are
    also substituted in every rule.
    """
    ground_rules: List[dict] = []

    for rule in prog.rules:
        # Collect ASP variables declared in this program
        asp_vars: Dict[str, List] = {}
        for vn, vsort in prog.var_decls.items():
            if not is_smt_sort(vsort):
                if vsort in prog.sorts:
                    asp_vars[vn] = prog.sorts[vsort]

        # Find which ASP variables actually appear in this rule
        rule_asp_vars = _rule_asp_vars(rule, asp_vars)

        if not rule_asp_vars:
            # No ASP variables — still substitute numeric params
            env = dict(params)
            g_rule = _ground_rule(rule, env)
            if g_rule is not None:
                ground_rules.append(g_rule)
        else:
            # Enumerate all combinations of ASP variable values
            vnames = list(rule_asp_vars.keys())
            domains = [rule_asp_vars[v] for v in vnames]
            for combo in product(*domains):
                env = dict(zip(vnames, combo))
                env.update(params)          # also substitute numeric params
                g_rule = _ground_rule(rule, env)
                if g_rule is not None:
                    ground_rules.append(g_rule)

    return ground_rules


def _rule_asp_vars(rule: dict, asp_vars: Dict) -> Dict:
    """Find which ASP variables appear in the rule's atoms."""
    used: Set[str] = set()
    if rule['head']:
        used |= _atom_vars(rule['head'])
    for atom in rule['body']:
        used |= _atom_vars(atom)
    return {v: asp_vars[v] for v in used if v in asp_vars}


def _atom_vars(atom: dict) -> Set[str]:
    return expr_vars(atom['lhs']) | expr_vars(atom['rhs'])


def _ground_rule(rule: dict, env: Dict) -> Optional[dict]:
    """Apply substitution env to all expressions in rule."""
    head = _ground_atom(rule['head'], env) if rule['head'] else None
    body = [_ground_atom(a, env) for a in rule['body']]
    # Filter out trivially-true arithmetic equalities (e.g. 0=0)
    filtered = []
    for a in body:
        if _is_trivially_true(a):
            continue
        if _is_trivially_false(a):
            return None   # rule is impossible
        filtered.append(a)
    return {
        'head': head,
        'body': filtered,
        'is_choice': rule.get('is_choice', False),
        'is_constraint': rule.get('is_constraint', False)
    }


def _ground_atom(atom: dict, env: Dict) -> dict:
    return {
        'lhs': expr_simplify(expr_subst(atom['lhs'], env)),
        'rhs': expr_simplify(expr_subst(atom['rhs'], env)),
        'cmp': atom.get('cmp', '='),
        'negated': atom['negated']
    }


def _is_trivially_true(atom: dict) -> bool:
    """Returns True if atom is trivially true, e.g. non-negated  3 = 3."""
    if atom['negated']:
        return False
    cmp = atom.get('cmp', '=')
    lhs, rhs = atom['lhs'], atom['rhs']
    if lhs[0] == 'num' and rhs[0] == 'num':
        l, r = lhs[1], rhs[1]
        return {
            '=':  l == r, '!=': l != r,
            '>=': l >= r, '<=': l <= r,
            '>':  l > r,  '<':  l < r,
        }.get(cmp, False)
    return False


def _is_trivially_false(atom: dict) -> bool:
    """Returns True if atom is trivially false, e.g.  3 = 4."""
    cmp = atom.get('cmp', '=')
    lhs, rhs = atom['lhs'], atom['rhs']
    if lhs[0] == 'num' and rhs[0] == 'num':
        l, r = lhs[1], rhs[1]
        sat = {
            '=':  l == r, '!=': l != r,
            '>=': l >= r, '<=': l <= r,
            '>':  l > r,  '<':  l < r,
        }.get(cmp, True)
        return (not sat) if not atom['negated'] else sat
    return False


# ════════════════════════════════════════════════════════════════════════════
# §7  Naming of ground SMT variables
#     Naming convention:  func_arg1_arg2_..._argN_
#     e.g. speed(1) → speed_1_  ;  accel(2) → accel_2_
# ════════════════════════════════════════════════════════════════════════════

def smt_var_name(fname: str, args: Tuple) -> str:
    """Return the SMT variable name for ground function  fname(args)."""
    if not args:
        return fname + '_'
    def fmt(a):
        if isinstance(a, float) and a == int(a):
            return str(int(a))
        if isinstance(a, float):
            return str(a).replace('.', 'p').replace('-', 'n')
        if isinstance(a, int) and a < 0:
            return 'n' + str(-a)
        return str(a)
    return fname + '_' + '_'.join(fmt(a) for a in args) + '_'


def extract_func_app(expr) -> Optional[Tuple[str, Tuple]]:
    """If expr is a fully-ground function application App(f, [Num(v),...]),
    return  (fname, (v1, v2, ...))  else None.

    Num values that are whole floats are normalised to int so that
    step-arithmetic like S+1 (evaluated to 1.0 or 1) produces the same key.
    """
    if expr[0] == 'app':
        fname = expr[1]
        args = expr[2]
        ground_args = []
        for a in args:
            if a[0] == 'num':
                v = a[1]
                # normalise 1.0 → 1 so hash keys are consistent
                if isinstance(v, float) and v == int(v):
                    v = int(v)
                ground_args.append(v)
            else:
                return None
        return fname, tuple(ground_args)
    return None


def atom_is_func_assignment(atom: dict, const_decls: dict) -> Optional[Tuple[str, Tuple]]:
    """Returns (fname, ground_args) if lhs is a known constant application."""
    fa = extract_func_app(atom['lhs'])
    if fa and fa[0] in const_decls:
        return fa
    return None


# ════════════════════════════════════════════════════════════════════════════
# §8  Clark Completion & Variable Elimination
#
#     For each ground constant  f(n1,…,nk)  collect all rules that define it,
#     then produce the SMT assertion.
#
#     Each rule body (after grounding) has:
#       • "binding atoms"    g(t)=X   where X is an SMT variable → X binds to smt_var(g,t)
#       • "condition atoms"  g(t)=c   where c is concrete (true/false/num) → keep as is
#       • "arithmetic equalities"  Y=expr  → used to determine value of head variable
#       • negated atoms  not g(t)=c  → keep as is
#
#     Variable elimination:
#       1. Collect bindings: X → smt_var_name(g, args)
#       2. Find the equality  Y=expr  or  Y appears in head rhs
#       3. Substitute into the full body and head rhs to get concrete SMT
# ════════════════════════════════════════════════════════════════════════════

def compute_completion(ground_rules: List[dict],
                       const_decls: dict,
                       params: Dict) -> Tuple[dict, List[dict]]:
    """Group ground rules by head constant; return (completion_dict, constraint_list).

    completion_dict: {(fname, args_tuple) → [body_formula]}
                     each body_formula is a list of ground atoms (dict)
    constraint_list: list of body-only rules (integrity constraints)
    """
    completion: Dict[Tuple, List[List[dict]]] = defaultdict(list)
    constraints: List[dict] = []
    exogenous: Set[Tuple] = set()   # constants with choice rules

    for rule in ground_rules:
        if rule.get('is_constraint') or rule['head'] is None:
            constraints.append(rule)
            continue

        fa = atom_is_func_assignment(rule['head'], const_decls)
        if fa is None:
            # Head is not a known constant — treat as integrity constraint
            # or skip
            continue

        if rule.get('is_choice'):
            exogenous.add(fa)
            # Choice rules → constant is exogenous (unconstrained), skip completion
            continue

        completion[fa].append(rule['body'])

    return completion, constraints, exogenous


# ════════════════════════════════════════════════════════════════════════════
# §9  SMT-LIB 2 Emitter
# ════════════════════════════════════════════════════════════════════════════

def smt_sort(val_sort: str) -> str:
    vs = val_sort.lower()
    if vs == 'boolean': return 'Bool'
    if vs in ('real',):  return 'Real'
    if vs in ('integer', 'int'): return 'Int'
    return 'Real'   # default


def build_ground_consts(const_decls: dict,
                        sorts: Dict[str, List],
                        params: Dict) -> Dict[Tuple, str]:
    """Build mapping  (fname, (a1,...,an)) → smt_variable_name
    for every ground instance of every declared constant."""
    gc: Dict[Tuple, str] = {}
    for cname, cdecl in const_decls.items():
        arg_sorts = cdecl['arg_sorts']
        if not arg_sorts:
            gc[(cname, ())] = smt_var_name(cname, ())
        else:
            domains = []
            for s in arg_sorts:
                if s in sorts:
                    domains.append(sorts[s])
                else:
                    domains.append([0])   # fallback
            for combo in product(*domains):
                gc[(cname, tuple(combo))] = smt_var_name(cname, tuple(combo))
    return gc


def emit_smt(
    prog: Program,
    completion: dict,
    constraints: List[dict],
    exogenous: Set[Tuple],
    gc: Dict[Tuple, str],
    params: Dict,
    show: List[str]
) -> str:
    lines: List[str] = []
    lines.append('; SMT-LIB 2 generated by aspmt2smt.py')
    lines.append('; (re-implementation of Bartholomew & Lee, JELIA 2014)')
    lines.append('; (set-option :produce-models true)')
    lines.append('')

    # ── Declare SMT variables ─────────────────────────────────────────
    lines.append('; -- Variable declarations -----------------------------')
    declared: Set[str] = set()
    for (fname, args), smt_name in sorted(gc.items()):
        if smt_name in declared:
            continue
        declared.add(smt_name)
        cdecl = prog.const_decls.get(fname, {})
        vs = smt_sort(cdecl.get('val_sort', 'real'))
        lines.append(f'(declare-const {smt_name} {vs})')

        # Bounded range assertion
        lo = cdecl.get('lo')
        hi = cdecl.get('hi')
        if lo is not None:
            lo_s = expr_to_smt(lo, gc, params)
            lines.append(f'(assert (<= {lo_s} {smt_name}))')
        if hi is not None:
            hi_s = expr_to_smt(hi, gc, params)
            lines.append(f'(assert (<= {smt_name} {hi_s}))')

    lines.append('')

    # ── Completion assertions ──────────────────────────────────────────
    lines.append('; -- Completion (one assertion per ground constant) ---')
    for (fname, args), body_list in sorted(completion.items()):
        smt_head = gc.get((fname, args), smt_var_name(fname, args))
        # Each body_list[i] is a list of atoms for one rule
        branch_smts: List[str] = []
        for body_atoms in body_list:
            branch = _emit_body(body_atoms, smt_head, fname, args,
                                prog, gc, params)
            if branch:
                branch_smts.append(branch)
        if not branch_smts:
            continue
        if len(branch_smts) == 1:
            assertion = branch_smts[0]
        else:
            inner = '\n       '.join(branch_smts)
            assertion = f'(or {inner})'
        lines.append(f'; completion for {smt_head}')
        lines.append(f'(assert {assertion})')
    lines.append('')

    # ── Integrity constraints  ('<- B' becomes 'not B') ───────────────
    lines.append('; -- Integrity constraints ----------------------------')
    for rule in constraints:
        body_atoms = rule['body']
        neg_body = _emit_body_constraint(body_atoms, gc, params)
        if neg_body:
            lines.append(f'(assert {neg_body})')
    lines.append('')

    lines.append('(check-sat)')
    lines.append('(get-model)')
    return '\n'.join(lines)


def _emit_body(
    body_atoms: List[dict],
    smt_head: str,
    fname: str,
    head_args: Tuple,
    prog: Program,
    gc: Dict[Tuple, str],
    params: Dict
) -> str:
    """Convert one rule body to an SMT-LIB conjunct for the completion.

    Steps:
      1. Identify binding atoms:   g(t) = VAR  → VAR binds to smt_var(g,t)
      2. Identify the value equality:  HEAD_VAR = arithmetic_expr
      3. Substitute all bindings + (HEAD_VAR → smt_head) into every atom
      4. Emit remaining condition atoms as SMT conjuncts
    """
    # 1. Determine the head value variable (rhs of head assignment)
    #    We know the head is fname(head_args) = VAR; VAR is the value var.
    #    In the rule we stored it in the body as an equality Y = expr.
    #    We need to find the head variable from the original rule's head.
    #    But after grounding, the head variable is replaced.  Instead we
    #    look for arithmetic equalities involving a free variable name.
    #
    #    The "value variable" strategy:
    #    - Any body atom of the form f(t) = VAR where VAR is an uppercase var
    #      AND (f,t) is a known constant → binding: VAR → smt_var(f,t)
    #    - Any body atom of the form VAR = expr or expr = VAR where VAR is
    #      not yet bound → candidate for head value var
    #    - We identify the head value variable as the one that appears in
    #      the head rhs, then substitute smt_head for it.

    bindings: Dict[str, str] = {}   # var_name → smt_var_name
    conditions: List[dict] = []
    arith_eqs: List[dict] = []      # pure arithmetic equalities

    for atom in body_atoms:
        cmp = atom.get('cmp', '=')
        fa = atom_is_func_assignment(atom, prog.const_decls)
        if fa is not None and cmp == '=' and not atom['negated']:
            # It's a constant assignment g(t) = rhs (equality, non-negated)
            g_smt = gc.get(fa, smt_var_name(fa[0], fa[1]))
            rhs = atom['rhs']
            if rhs[0] == 'var' and rhs[1][0].isupper():
                # Binding: VAR binds to the value of g(t)
                bindings[rhs[1]] = g_smt
            else:
                # Condition: g(t) = concrete_value
                conditions.append(atom)
        elif fa is not None:
            # Negated assignment or comparison operator  — treat as condition
            conditions.append(atom)
        else:
            # Pure arithmetic or comparison
            lhs, rhs = atom['lhs'], atom['rhs']
            if (cmp == '=' and not atom['negated'] and
                    lhs[0] == 'var' and lhs[1][0].isupper()):
                # Arithmetic equality: VAR = expr  (value binding)
                arith_eqs.append(atom)
            elif (cmp == '=' and not atom['negated'] and
                    rhs[0] == 'var' and rhs[1][0].isupper()):
                # Swap: normalize to  VAR = expr
                arith_eqs.append({
                    'lhs': rhs, 'rhs': lhs, 'cmp': '=', 'negated': False
                })
            else:
                # Comparison or negated equality — keep as condition
                conditions.append(atom)

    # 2. Resolve arithmetic equalities in dependency order
    def resolve_expr(e):
        if e[0] == 'var':
            n = e[1]
            if n in bindings:
                return Var(bindings[n])
        if e[0] == 'app':
            fa2 = extract_func_app(e)
            if fa2 and fa2 in gc:
                return Var(gc[fa2])
        return e

    # Iteratively resolve arith_eqs (substitute known bindings)
    max_iter = len(arith_eqs) + 1
    for _ in range(max_iter):
        changed = False
        still_pending = []
        for aeq in arith_eqs:
            vname = aeq['lhs'][1]
            rhs_sub = expr_subst(aeq['rhs'],
                                  {k: Var(v) for k, v in bindings.items()})
            # Check if RHS is fully resolved (no more uppercase vars)
            remaining = {x for x in expr_vars(rhs_sub)
                         if x[0].isupper() and x not in bindings}
            if not remaining:
                bindings[vname] = _expr_to_smt_str(rhs_sub, gc, params, bindings)
                changed = True
            else:
                still_pending.append(aeq)
        arith_eqs = still_pending
        if not changed:
            break

    # 3. Build condition SMT parts
    parts: List[str] = []

    for atom in conditions:
        cond_smt = _atom_to_smt(atom, gc, params, bindings)
        if cond_smt:
            parts.append(cond_smt)

    # 4. Build head value equality:  (= smt_head  expr_of_value_var)
    #    Find which variable was the head's value variable.
    #    We look for an arith_eq whose variable is the head rhs var.
    #    Actually the head value variable is whatever was in the
    #    rule head's rhs — it's an uppercase var that we need to
    #    identify.  After grounding, we find it in bindings:
    #    it's the binding var that equals the value expression.
    #
    #    Strategy: if there's a binding like HEAD_VAR → smt_expr,
    #    then emit (= smt_head smt_expr).
    #    We identify HEAD_VAR as the var used as rhs of the head.
    #    But we don't have direct access to the head rhs var here.
    #    Workaround: look for uppercase vars in bindings that are NOT
    #    bound by any body constant assignment, i.e. they come from
    #    arith_eqs.  That's the value variable.

    # Actually: bindings contains BOTH constant-bound vars (from f(t)=X)
    # and arith-eq-bound vars (from Y=expr).  The head value var is the
    # one that corresponds to the head's rhs.  Let's emit an equality
    # for every arith-eq-bound var that appears "free" (not bound by
    # a constant assignment in the original body).

    # Simpler heuristic: emit (= smt_head <binding>) for the arith-eq
    # bindings, but we need to know which var is the HEAD value var.
    # We detect it: it's the only var that is
    # (a) bound by an arith-eq,  AND
    # (b) used nowhere else (it's only the value var for this constant).
    #
    # Even simpler:  after the substitution, there should be exactly one
    # "residual" equality of the form (= smt_head expr).  We emit it.

    # Find the arith-bound vars (from arith_eqs that were resolved)
    const_bound_vars: Set[str] = set()
    for atom in body_atoms:
        fa3 = atom_is_func_assignment(atom, prog.const_decls)
        if fa3 and not atom['negated']:
            rhs2 = atom['rhs']
            if rhs2[0] == 'var' and rhs2[1][0].isupper():
                const_bound_vars.add(rhs2[1])

    arith_bound_vars = {k for k in bindings if k not in const_bound_vars}

    for vn in arith_bound_vars:
        # This var was resolved from an arith equality; its value is the
        # head value.
        head_val_smt = bindings[vn]
        if isinstance(head_val_smt, str):
            parts.append(f'(= {smt_head} {head_val_smt})')
        break    # typically only one value variable per rule

    # Edge case: inertia-style rule  speed(n+1) = Y <- not ... & speed(n)=Y
    # Here Y is both bound by speed(n)=Y AND is the head value variable.
    # The completion should give  (= speed_{n+1}_ speed_{n}_).
    # We handle this: if smt_head equality wasn't added yet, check if
    # a const-bound var also matches what the head should be.
    if not arith_bound_vars:
        # All vars are const-bound; find any var that should map to head
        for atom in body_atoms:
            fa4 = atom_is_func_assignment(atom, prog.const_decls)
            if fa4:
                g_smt2 = gc.get(fa4, smt_var_name(fa4[0], fa4[1]))
                rhs3 = atom['rhs']
                if rhs3[0] == 'var' and rhs3[1][0].isupper():
                    vn = rhs3[1]
                    # Is this var also the head value var?
                    # Heuristic: if this var doesn't appear in any condition
                    # atom's lhs (non-func-app atoms), it's the value var.
                    used_in_cond = False
                    for ca in conditions:
                        if vn in expr_vars(ca['lhs']) or vn in expr_vars(ca['rhs']):
                            used_in_cond = True
                            break
                    if not used_in_cond:
                        # This binding variable IS the head value variable
                        parts.append(f'(= {smt_head} {g_smt2})')
                        break

    if not parts:
        return 'true'
    if len(parts) == 1:
        return parts[0]
    inner = '\n         '.join(parts)
    return f'(and {inner})'


def _emit_body_constraint(
    body_atoms: List[dict],
    gc: Dict[Tuple, str],
    params: Dict
) -> str:
    """Emit the SMT assertion for an integrity constraint  '<- body'.

    Semantics: assert (not body).
    Special case: if body is a single negated atom  '<- not A',
    that becomes  assert A  (double negation eliminated).
    """
    bindings: Dict[str, str] = {}

    # First, substitute params into atom expressions (do simple grounding)
    subst_atoms = []
    for atom in body_atoms:
        subst_atoms.append({
            'lhs': expr_subst(atom['lhs'], params),
            'rhs': expr_subst(atom['rhs'], params),
            'cmp': atom.get('cmp', '='),
            'negated': atom['negated']
        })

    if len(subst_atoms) == 1:
        atom = subst_atoms[0]
        if atom['negated']:
            # '<- not A'  →  assert A
            pos = dict(atom, negated=False)
            s = _atom_to_smt(pos, gc, params, bindings)
            return s
        else:
            # '<- A'  →  assert (not A)
            s = _atom_to_smt(atom, gc, params, bindings)
            return f'(not {s})'
    else:
        parts = [_atom_to_smt(a, gc, params, bindings) for a in subst_atoms]
        parts = [p for p in parts if p and p != 'true']
        if not parts:
            return ''
        body_smt = ('(and ' + '\n       '.join(parts) + ')') if len(parts) > 1 else parts[0]
        return f'(not {body_smt})'


def _expr_to_smt_str(e, gc: Dict, params: Dict, bindings: Dict) -> str:
    """Convert expression e to SMT-LIB, using both gc and var bindings."""
    combined_params = dict(params)
    # Add bindings as Var → string (we pass as params since they are ground values)
    # Actually we pass them through the gc map.
    # Build a temporary gc that also maps var names.
    def _conv(expr):
        t = expr[0]
        if t == 'num':
            v = expr[1]
            if isinstance(v, float):
                return f"{v}" if v != int(v) else f"{int(v)}.0"
            return str(v)
        if t == 'var':
            n = expr[1]
            if n in bindings:
                b = bindings[n]
                if isinstance(b, str):
                    return b
            if n in params:
                v = params[n]
                if isinstance(v, float):
                    return f"{v}" if v != int(v) else f"{int(v)}.0"
                return str(v)
            return n
        if t == 'app':
            fa = extract_func_app(expr)
            if fa and fa in gc:
                return gc[fa]
            return expr_to_smt(expr, gc, params)
        if t == 'binop':
            op, l, r = expr[1], expr[2], expr[3]
            return f'({op} {_conv(l)} {_conv(r)})'
        if t == 'unary':
            op, v2 = expr[1], expr[2]
            vs = _conv(v2)
            return f'(- {vs})' if op == '-' else vs
        return str(expr)
    return _conv(e)


_SMT_CMP = {'=': '=', '!=': 'distinct', '>=': '>=', '<=': '<=', '>': '>', '<': '<'}


def _atom_to_smt(
    atom: dict,
    gc: Dict[Tuple, str],
    params: Dict,
    bindings: Dict[str, str]
) -> str:
    """Convert a single atom to an SMT-LIB string."""
    lhs = atom['lhs']
    rhs = atom['rhs']
    negated = atom['negated']
    cmp_op = atom.get('cmp', '=')

    lhs_s = _expr_to_smt_str(lhs, gc, params, bindings)
    rhs_s = _expr_to_smt_str(rhs, gc, params, bindings)

    smt_op = _SMT_CMP.get(cmp_op, cmp_op)

    if smt_op == 'distinct':
        core = f'(not (= {lhs_s} {rhs_s}))'
    else:
        core = f'({smt_op} {lhs_s} {rhs_s})'

    if negated:
        return f'(not {core})'
    return core


# ════════════════════════════════════════════════════════════════════════════
# §10  Z3 runner
# ════════════════════════════════════════════════════════════════════════════

def run_z3(smt_text: str, z3_path: str = 'z3') -> Tuple[str, str]:
    """Run Z3 on smt_text.

    First tries the z3 executable at z3_path; if that fails, falls back to
    the z3-solver Python API (pip install z3-solver).

    Returns (stdout_str, stderr_str).
    """
    import tempfile

    # ── Try subprocess z3 executable ───────────────────────────────
    try:
        with tempfile.NamedTemporaryFile(
                suffix='.smt2', mode='w', delete=False, encoding='utf-8') as f:
            f.write(smt_text)
            fname = f.name
        result = subprocess.run(
            [z3_path, fname],
            capture_output=True, text=True, timeout=60
        )
        os.unlink(fname)
        return result.stdout, result.stderr
    except FileNotFoundError:
        pass   # fall through to Python API
    except subprocess.TimeoutExpired:
        try: os.unlink(fname)
        except: pass
        return '', 'Z3 timed out (60 s).'

    # ── Fall back to z3 Python API ──────────────────────────────────
    try:
        import z3 as z3mod
        ctx = z3mod.Context()
        solver = z3mod.Solver(ctx=ctx)

        # Parse the SMT-LIB text (strip get-model / check-sat for parse)
        smt_clean = smt_text
        solver.from_string(smt_clean)

        result = solver.check()
        if result == z3mod.sat:
            model = solver.model()
            lines = ['sat', '(model']
            for d in model:
                name = str(d)
                val = model[d]
                sort = d.range()
                lines.append(
                    f'  (define-fun {name} () {sort} {val})'
                )
            lines.append(')')
            return '\n'.join(lines), ''
        elif result == z3mod.unsat:
            return 'unsat\n', ''
        else:
            return 'unknown\n', ''
    except Exception as e:
        return '', f'Z3 Python API error: {e}'


def parse_z3_model(output: str, gc: Dict[Tuple, str],
                   show: List[str]) -> Dict[str, str]:
    """Parse Z3 get-model output into  {smt_var_name → value}."""
    model: Dict[str, str] = {}
    # Pattern: (define-fun var_name () Type value)
    pat = re.compile(
        r'\(define-fun\s+(\S+)\s+\(\)\s+\S+\s+(.*?)\)',
        re.DOTALL
    )
    for m in pat.finditer(output):
        var_name = m.group(1).strip()
        value = m.group(2).strip()
        # Clean up Z3 rational fractions like (/ 1.0 3.0)
        model[var_name] = value
    return model


def display_model(model: Dict[str, str],
                  gc: Dict[Tuple, str],
                  show: List[str],
                  params: Dict) -> None:
    """Pretty-print the Z3 model."""
    if not show:
        show = list({fa[0] for fa in gc})

    print('\n=== Model ===')
    for fname in sorted(show):
        entries = sorted(
            [(fa, sn) for fa, sn in gc.items() if fa[0] == fname],
            key=lambda x: x[0][1]
        )
        for (fn, args), smt_name in entries:
            val = model.get(smt_name, '?')
            arg_str = ', '.join(str(a) for a in args)
            print(f'  {fn}({arg_str}) = {val}')


# ════════════════════════════════════════════════════════════════════════════
# §11  Main
# ════════════════════════════════════════════════════════════════════════════

def main():
    ap = argparse.ArgumentParser(
        description='aspmt2smt: ASPMT -> SMT compiler (re-implementation of '
                    'Bartholomew & Lee, JELIA 2014)',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__.split('Usage\n=====')[1].strip()
    )
    ap.add_argument('file', help='ASPMT input file (*.aspmt)')
    ap.add_argument('-c', '--const', action='append', default=[],
                    metavar='name=value',
                    help='Set a numeric parameter, e.g. -c st=3 -c ar=3')
    ap.add_argument('--show-smt', action='store_true',
                    help='Print the generated SMT-LIB 2 code')
    ap.add_argument('--no-z3', action='store_true',
                    help='Do not run Z3 (only generate SMT-LIB)')
    ap.add_argument('--z3', default='z3',
                    help='Path to z3 executable (default: z3)')
    args = ap.parse_args()

    # ── Load source ──────────────────────────────────────────────────
    with open(args.file, encoding='utf-8') as f:
        source = f.read()

    # ── Build params dict ────────────────────────────────────────────
    params: Dict[str, Any] = {}
    for spec in args.const:
        if '=' not in spec:
            ap.error(f'Bad -c spec: {spec!r}  (expected name=value)')
        k, v = spec.split('=', 1)
        try:
            params[k.strip()] = int(v.strip())
        except ValueError:
            try:
                params[k.strip()] = float(v.strip())
            except ValueError:
                params[k.strip()] = v.strip()

    print(f'[aspmt2smt] Parsing {args.file} ...')
    prog = parse_program(source, params)

    print(f'[aspmt2smt] Sorts: {list(prog.sorts.keys())}')
    print(f'[aspmt2smt] Constants: {list(prog.const_decls.keys())}')
    print(f'[aspmt2smt] Rules: {len(prog.rules)}')

    # ── Build ground constant map ────────────────────────────────────
    gc = build_ground_consts(prog.const_decls, prog.sorts, params)
    print(f'[aspmt2smt] Ground constants: {len(gc)}')

    # ── Ground rules ─────────────────────────────────────────────────
    ground_rules = ground_program(prog, params)
    print(f'[aspmt2smt] Ground rules: {len(ground_rules)}')

    # ── Completion ───────────────────────────────────────────────────
    completion, constraints, exogenous = compute_completion(
        ground_rules, prog.const_decls, params
    )
    print(f'[aspmt2smt] Completion groups: {len(completion)}'
          f', Constraints: {len(constraints)}'
          f', Exogenous: {len(exogenous)}')

    # ── Emit SMT-LIB 2 ──────────────────────────────────────────────
    smt_text = emit_smt(
        prog, completion, constraints, exogenous,
        gc, params, prog.show
    )

    if args.show_smt or args.no_z3:
        print('\n' + '-' * 60)
        print(smt_text)
        print('-' * 60)

    if args.no_z3:
        return

    # ── Run Z3 ──────────────────────────────────────────────────────
    print(f'\n[aspmt2smt] Running Z3 ...')
    stdout, stderr = run_z3(smt_text, args.z3)

    if stderr:
        print('[Z3 stderr]', stderr.strip())

    if stdout.startswith('unsat'):
        print('[aspmt2smt] UNSAT -- no stable model exists.')
    elif stdout.startswith('sat'):
        print('[aspmt2smt] SAT')
        model = parse_z3_model(stdout, gc, prog.show)
        display_model(model, gc, prog.show, params)
        print()
        print('[Z3 raw output]')
        print(stdout[:2000])
    else:
        print('[Z3 output]')
        print(stdout[:2000])
        if stderr:
            print('[Z3 errors]', stderr[:500])


if __name__ == '__main__':
    main()
