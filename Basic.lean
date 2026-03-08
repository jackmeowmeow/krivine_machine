--! This file defines a simple expression language and implements the Krivine machine to evaluate expressions in that language. The language includes basic arithmetic operations, boolean operations, and function application.

inductive Exp where
  | nil
  | int      : Int → Exp
  | bool     : Bool → Exp
  | var      : String → Exp
  | abs      : String → Exp → Exp
  | app      : Exp → Exp → Exp
  | absolute : Exp → Exp
  | not      : Exp → Exp
  | add      : Exp → Exp → Exp
  | sub      : Exp → Exp → Exp
  | div      : Exp → Exp → Exp
  | mul      : Exp → Exp → Exp
  | mod      : Exp → Exp → Exp
  | exp      : Exp → Exp → Exp
  | and      : Exp → Exp → Exp
  | or       : Exp → Exp → Exp
  | imp      : Exp → Exp → Exp
  | equ      : Exp → Exp → Exp
  | gtequ    : Exp → Exp → Exp
  | ltequ    : Exp → Exp → Exp
  | grt      : Exp → Exp → Exp
  | lst      : Exp → Exp → Exp
  | ifthenelse : Exp → Exp → Exp → Exp
  deriving Repr, DecidableEq

inductive Opcode where
  | NIL
  | INT    : Int → Opcode
  | BOOL   : Bool → Opcode
  | LOOKUP : String → Opcode
  | CLOS   : String → List Opcode → Opcode
  | CALL
  | RET
  | ADD
  deriving Repr

inductive Answer where
  | i     : Int → Answer
  | b     : Bool → Answer
  | vclos : List (String × Answer) → String → List Opcode → Answer
  deriving Repr

abbrev Table       := List (String × Answer)
abbrev Stack       := List Answer
abbrev Environment := Table
abbrev Control     := List Opcode
abbrev Dump        := Stack × Environment × Control
abbrev Program     := List Exp

inductive Closure where
  | cltype : Exp → List (Exp × Closure) → Closure
  deriving Repr

abbrev EnvironmentCLOS := List (Exp × Closure)
abbrev StackCLOS       := List Closure

def power : Int → Nat → Int
  | _, 0     => 1
  | a, n + 1 => a * power a n

def impBool (a b : Bool) : Bool :=
  match a, b with
  | true, false => false
  | _, _        => true

partial def lookup (e : Exp) (env : EnvironmentCLOS) : Except String Closure :=
  match env with
  | [] => .error "Variable_not_initialized"
  | (e1, cl) :: rest =>
      if e1 ≠ e then
        lookup e rest
      else
        match cl with
        | .cltype (.abs x x1) env' =>
            .ok (.cltype (.abs x x1) ((e1, cl) :: env'))
        | _ =>
            .ok cl

def absApplied (cl : Closure) (s : StackCLOS) : Except String (Closure × StackCLOS) :=
  match cl, s with
  | .cltype (.abs x e) env, c :: cs =>
      .ok (.cltype e ((.var x, c) :: env), cs)
  | _, [] =>
      .error "InvalidOperation"
  | _, _ =>
      .error "InvalidOperation"

def add (a1 a2 : Closure) : Except String Closure :=
  match a1, a2 with
  | .cltype (.int i1) _, .cltype (.int i2) _ => .ok (.cltype (.int (i1 + i2)) [])
  | _, _ => .error "InvalidOperation"

def mul (a1 a2 : Closure) : Except String Closure :=
  match a1, a2 with
  | .cltype (.int i1) _, .cltype (.int i2) _ => .ok (.cltype (.int (i1 * i2)) [])
  | _, _ => .error "InvalidOperation"

def sub (a1 a2 : Closure) : Except String Closure :=
  match a1, a2 with
  | .cltype (.int i1) _, .cltype (.int i2) _ => .ok (.cltype (.int (i1 - i2)) [])
  | _, _ => .error "InvalidOperation"

def divC (a1 a2 : Closure) : Except String Closure :=
  match a1, a2 with
  | .cltype (.int i1) _, .cltype (.int i2) _ =>
      if i2 = 0 then
        .error "Division by zero"
      else
        .ok (.cltype (.int (i1 / i2)) [])
  | _, _ => .error "InvalidOperation"

def exponential (a1 a2 : Closure) : Except String Closure :=
  match a1, a2 with
  | .cltype (.int i1) _, .cltype (.int i2) _ =>
      if i2 < 0 then
        .error "Negative exponent not supported"
      else
        .ok (.cltype (.int (power i1 i2.toNat)) [])
  | _, _ => .error "InvalidOperation"

def modulus (a1 a2 : Closure) : Except String Closure :=
  match a1, a2 with
  | .cltype (.int i1) _, .cltype (.int i2) _ =>
      if i2 = 0 then
        .error "Modulo by zero"
      else
        .ok (.cltype (.int (i1 % i2)) [])
  | _, _ => .error "InvalidOperation"

def absolute (a1 : Closure) : Except String Closure :=
  match a1 with
  | .cltype (.int i1) _ => .ok (.cltype (.int (Int.natAbs i1)) [])
  | _ => .error "InvalidOperation"

def andop (a1 a2 : Closure) : Except String Closure :=
  match a1, a2 with
  | .cltype (.bool b1) _, .cltype (.bool b2) _ => .ok (.cltype (.bool (b1 && b2)) [])
  | _, _ => .error "InvalidOperation"

def orop (a1 a2 : Closure) : Except String Closure :=
  match a1, a2 with
  | .cltype (.bool b1) _, .cltype (.bool b2) _ => .ok (.cltype (.bool (b1 || b2)) [])
  | _, _ => .error "InvalidOperation"

def impOp (a1 a2 : Closure) : Except String Closure :=
  match a1, a2 with
  | .cltype (.bool b1) _, .cltype (.bool b2) _ => .ok (.cltype (.bool (impBool b1 b2)) [])
  | _, _ => .error "InvalidOperation"

def notop (a1 : Closure) : Except String Closure :=
  match a1 with
  | .cltype (.bool b1) _ => .ok (.cltype (.bool (!b1)) [])
  | _ => .error "InvalidOperation"

def equal (a1 a2 : Closure) : Except String Closure :=
  match a1, a2 with
  | .cltype (.int i1) _, .cltype (.int i2) _ => .ok (.cltype (.bool (i1 = i2)) [])
  | _, _ => .error "InvalidOperation"

def greaterthanorequal (a1 a2 : Closure) : Except String Closure :=
  match a1, a2 with
  | .cltype (.int i1) _, .cltype (.int i2) _ => .ok (.cltype (.bool (i1 ≥ i2)) [])
  | _, _ => .error "InvalidOperation"

def lessthanorequal (a1 a2 : Closure) : Except String Closure :=
  match a1, a2 with
  | .cltype (.int i1) _, .cltype (.int i2) _ => .ok (.cltype (.bool (i1 ≤ i2)) [])
  | _, _ => .error "InvalidOperation"

def greaterthan (a1 a2 : Closure) : Except String Closure :=
  match a1, a2 with
  | .cltype (.int i1) _, .cltype (.int i2) _ => .ok (.cltype (.bool (i1 > i2)) [])
  | _, _ => .error "InvalidOperation"

def lessthan (a1 a2 : Closure) : Except String Closure :=
  match a1, a2 with
  | .cltype (.int i1) _, .cltype (.int i2) _ => .ok (.cltype (.bool (i1 < i2)) [])
  | _, _ => .error "InvalidOperation"

partial def krivineMachine (cl : Closure) (s : StackCLOS) : Except String Closure := do
  match cl with
  | .cltype .nil env =>
      pure (.cltype .nil env)

  | .cltype (.int i) env =>
      pure (.cltype (.int i) env)

  | .cltype (.bool b) env =>
      pure (.cltype (.bool b) env)

  | .cltype (.var v) env =>
      let found ← lookup (.var v) env
      krivineMachine found s

  | .cltype (.abs x e) env =>
      let (cl', s') ← absApplied (.cltype (.abs x e) env) s
      krivineMachine cl' s'

  | .cltype (.app e1 e2) env =>
      krivineMachine (.cltype e1 env) (.cltype e2 env :: s)

  | .cltype (.add e1 e2) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let v2 ← krivineMachine (.cltype e2 env) []
      let r  ← add v1 v2
      krivineMachine r s

  | .cltype (.sub e1 e2) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let v2 ← krivineMachine (.cltype e2 env) []
      let r  ← sub v1 v2
      krivineMachine r s

  | .cltype (.mul e1 e2) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let v2 ← krivineMachine (.cltype e2 env) []
      let r  ← mul v1 v2
      krivineMachine r s

  | .cltype (.div e1 e2) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let v2 ← krivineMachine (.cltype e2 env) []
      let r  ← divC v1 v2
      krivineMachine r s

  | .cltype (.exp e1 e2) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let v2 ← krivineMachine (.cltype e2 env) []
      let r  ← exponential v1 v2
      krivineMachine r s

  | .cltype (.mod e1 e2) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let v2 ← krivineMachine (.cltype e2 env) []
      let r  ← modulus v1 v2
      krivineMachine r s

  | .cltype (.absolute e1) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let r  ← absolute v1
      krivineMachine r s

  | .cltype (.and e1 e2) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let v2 ← krivineMachine (.cltype e2 env) []
      let r  ← andop v1 v2
      krivineMachine r s

  | .cltype (.or e1 e2) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let v2 ← krivineMachine (.cltype e2 env) []
      let r  ← orop v1 v2
      krivineMachine r s

  | .cltype (.imp e1 e2) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let v2 ← krivineMachine (.cltype e2 env) []
      let r  ← impOp v1 v2
      krivineMachine r s

  | .cltype (.not e1) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let r  ← notop v1
      krivineMachine r s

  | .cltype (.equ e1 e2) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let v2 ← krivineMachine (.cltype e2 env) []
      let r  ← equal v1 v2
      krivineMachine r s

  | .cltype (.gtequ e1 e2) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let v2 ← krivineMachine (.cltype e2 env) []
      let r  ← greaterthanorequal v1 v2
      krivineMachine r s

  | .cltype (.ltequ e1 e2) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let v2 ← krivineMachine (.cltype e2 env) []
      let r  ← lessthanorequal v1 v2
      krivineMachine r s

  | .cltype (.grt e1 e2) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let v2 ← krivineMachine (.cltype e2 env) []
      let r  ← greaterthan v1 v2
      krivineMachine r s

  | .cltype (.lst e1 e2) env =>
      let v1 ← krivineMachine (.cltype e1 env) []
      let v2 ← krivineMachine (.cltype e2 env) []
      let r  ← lessthan v1 v2
      krivineMachine r s

  | .cltype (.ifthenelse e0 e1 e2) env =>
      let a0 ← krivineMachine (.cltype e0 env) []
      match a0 with
      | .cltype (.bool b) _ =>
          if b then
            krivineMachine (.cltype e1 env) s
          else
            krivineMachine (.cltype e2 env) s
      | _ =>
          .error "InvalidOperation"

partial def executeKrivine (prog : Program) (env : EnvironmentCLOS) : Except String Answer := do
  match prog with
  | [] =>
      .error "ReturnEmpty"
  | p :: prog' =>
      let cl ← krivineMachine (.cltype p env) []
      match cl with
      | .cltype .nil env' =>
          executeKrivine prog' env'
      | .cltype (.int i) _ =>
          pure (.i i)
      | .cltype (.bool b) _ =>
          pure (.b b)
      | _ =>
          .error "InvalidBigStepAnswerClosure"


def ex1 : Exp := Exp.add (Exp.int 2) (Exp.int 3)

#eval executeKrivine [ex1] []
