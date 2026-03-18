# aspmt2smt — ASPMT to SMT Compiler (re-implementation)

A Python re-implementation of the **aspmt2smt** system described in:

> "System aspmt2smt: Computing ASPMT Theories by SMT Solvers"
> Michael Bartholomew & Joohyung Lee, JELIA 2014
> https://arxiv.org/abs/2506.10708

---

## What is ASPMT?

**Answer Set Programming Modulo Theories (ASPMT)** combines the non-monotonic reasoning power of ASP with the continuous-domain expressiveness of SMT (Satisfiability Modulo Theories).

Traditional ASP requires grounding all variables over finite domains — which is infeasible for real-number variables. ASPMT solves this by:
- Grounding only "ASP variables" (those ranging over discrete sorts)
- Leaving "SMT variables" (reals, integers) as symbolic
- Translating the resulting formula to SMT-LIB 2 for Z3 to solve

---

## Pipeline

```
ASPMT input
    |
    v  1. Parse  (sorts, objects, constants, variables, rules)
    |  2. Ground  (ASP variables -> concrete values; params substituted)
    |  3. Clark Completion  (tight-program assumption)
    |  4. Variable Elimination  (SMT value-variables -> function names)
    v
SMT-LIB 2 output
    |
    v  Z3 solver
    |
    v
Stable Model (values for all declared constants)
```

---

## Requirements

```bash
pip install z3-solver
```

Python 3.8+ required. No other dependencies.

---

## Usage

```bash
python aspmt2smt.py <file.aspmt> -c name=value ... [options]
```

### Options

| Flag | Description |
|------|-------------|
| `-c name=value` | Set numeric parameter (repeatable) |
| `--show-smt` | Print the generated SMT-LIB 2 code |
| `--no-z3` | Generate SMT-LIB only, do not run Z3 |
| `--z3 PATH` | Path to z3 executable (defaults to Python API) |

---

## Examples

### 1. Car Planning (`examples/car.aspmt`)

A car on a road of length `l`. Actions: accelerate / decelerate / coast.
Goal: reach the other end at rest.

```bash
python aspmt2smt.py examples/car.aspmt -c st=3 -c ar=3 -c ms=4 -c l=10
```

**Parameters:**  `st` = number of time steps,  `ar` = acceleration rate,
`ms` = max speed,  `l` = road length

**Output:**
```
=== Model ===
  accel(0) = True
  accel(1) = False
  accel(2) = False
  decel(0) = False
  decel(1) = False
  decel(2) = True
  duration(0) = 1
  duration(1) = 7/3
  duration(2) = 1
  pos(0) = 0
  pos(1) = 3/2
  pos(2) = 17/2
  pos(3) = 10
  speed(0) = 0
  speed(1) = 3
  speed(2) = 3
  speed(3) = 0
```

This represents: accelerate for 1 s → coast for 7/3 s → brake for 1 s.
The durations are **real-valued** — impossible for standard ASP grounding!

### 2. Leaking Bucket (`examples/bucket.aspmt`)

A bucket with capacity `cap` that leaks 1 unit/step. Action: `fill` to cap.

```bash
python aspmt2smt.py examples/bucket.aspmt -c st=5 -c cap=10 -c init=5 -c target=7
```

**Output:**
```
  fill(0) = True     level(0) = 5
  fill(1) = True     level(1) = 10
  fill(2) = False    level(2) = 10
  fill(3) = False    level(3) = 9
  fill(4) = False    level(4) = 8
                     level(5) = 7
```

### 3. View generated SMT-LIB

```bash
python aspmt2smt.py examples/car.aspmt -c st=3 -c ar=3 -c ms=4 -c l=10 --show-smt --no-z3
```

Produces standard SMT-LIB 2 that can be fed to any compatible solver.

---

## Input Language

```
:- sorts
   step; astep.                      % sort declarations

:- objects
   0..st     :: step;                % range expansion (0..3 when st=3)
   0..st-1   :: astep.

:- constants
   speed(step)     :: real[0..ms];   % real-valued, bounded
   accel(astep)    :: boolean;       % Boolean
   pos(step)       :: real[0..l].

:- variables
   S       :: astep;                 % ASP variable (grounded)
   X, Y, D :: real.                  % SMT variables (symbolic)

% Choice rule: constant is freely chosen (exogenous)
{accel(S)=true}.

% Rule with arithmetic in body
speed(S+1)=Y <- accel(S)=true & speed(S)=X & duration(S)=D & Y = X+ar*D.

% Inertia rule
speed(S+1)=Y <- not accel(S)=true & not decel(S)=true & speed(S)=Y.

% Integrity constraint (becomes: assert not body)
<- not speed(0)=0.
<- not pos(st)=l.

:- show
   speed/1; accel/1; pos/1.
```

### Sorts
- **User-defined sorts** (e.g., `step`, `astep`): discrete, finite — ASP variables ranging over these are **grounded away**
- **`real`** / **`integer`**: continuous — variables of these sorts become **free SMT variables**

### Constant declarations
- `f(arg_sort) :: boolean` — Boolean-valued function constant
- `f(arg_sort) :: real` — Real-valued
- `f(arg_sort) :: real[lo..hi]` — Real-valued with bounds

### Rules
- `H <- B1 & B2 & ... & Bn.` — implication rule
- `{H}.` — choice / exogenous rule (value unconstrained)
- `<- B.` — integrity constraint (body must be false)

### Operators in body
- `&` conjunction, `not` default negation
- `=`, `!=`, `>=`, `<=`, `>`, `<` — comparisons
- `+`, `-`, `*`, `/` — arithmetic

---

## Translation Details

### Tightness Assumption
The system assumes the program is **tight** (no cyclic positive dependencies),
so Clark's completion gives all stable models.

### Clark Completion
For each ground constant `f(n)`, collect rules `f(n)=Y <- Body_i`:

```
f(n)=Y  <->  Body1(Y) | Body2(Y) | ...
```

After **variable elimination** (substituting SMT variable bindings):

```smt2
(assert (or
  (and cond1 (= f_n_ expr1))
  (and cond2 (= f_n_ expr2))
  ...))
```

### Variable Elimination
Body atoms of the form `g(t)=X` where `X` is an SMT variable
contribute the binding `X -> smt_var(g,t)`.
Arithmetic equalities `Y = expr(X1,...,Xk)` then give the head value.

---

## Comparison with Traditional ASP

| | Traditional ASP | aspmt2smt |
|---|---|---|
| **Real numbers** | Discretisation required | Native |
| **Irrational solutions** | Impossible | Handled by Z3 |
| **Large integer domains** | Grounding explosion | SMT variable |
| **Non-monotonic reasoning** | Yes | Yes |
| **Tightness required** | No | Yes (for completeness) |

---

## File Structure

```
aspmt2smt/
    aspmt2smt.py          Main compiler script
    examples/
        car.aspmt         Car planning (continuous time)
        ball.aspmt        Bouncing ball (Newton's law)
        bucket.aspmt      Leaking bucket (integer planning)
    README.md
```

---

## References

- Bartholomew, M. & Lee, J. (2014). *System aspmt2smt: Computing ASPMT Theories by SMT Solvers*. JELIA 2014. [arXiv:2506.10708](https://arxiv.org/abs/2506.10708)
- Lee, J. & Meng, Y. (2013). *Functional Stable Model Semantics and Answer Set Programming Modulo Theories*. IJCAI 2013.
