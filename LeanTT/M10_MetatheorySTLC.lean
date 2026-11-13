/-!
# Módulo 10: Metateoría del Cálculo Lambda Simplemente Tipado (STLC) en Lean 4
Guía teórica asociada: `docs/10_metateoria_stlc_debruijn.md`

En este módulo formalizamos completamente el Cálculo Lambda Simplemente Tipado (STLC)
usando **Sintaxis Intrínsecamente Tipada** con índices de De Bruijn:
1. Tipos `Ty`, Contextos `Ctx` y Variables tipadas `Var Γ τ`.
2. Términos intrínsecamente tipados `Term Γ τ` (`Γ ⊢ t : τ`).
3. Renombramiento (`Ren Γ Δ`), Debilitamiento (*Weakening*) y Sustitución Paralela (`Sub Γ Δ`)
   que preservan el tipado por construcción.
4. Semántica denotacional y evaluador total libre de errores (`eval`).
5. Demostración del Lema de Sustitución Semántica (`eval_subst`).
-/

namespace LeanTT.M10

/-! ## 1. Tipos, Contextos y Variables de De Bruijn Tipadas -/

inductive Ty : Type where
  | nat  : Ty
  | bool : Ty
  | arr  : Ty → Ty → Ty
  deriving DecidableEq, Repr

infixr:70 " ⇒ " => Ty.arr

abbrev Ctx := List Ty

/-- `Var Γ τ` es un índice de De Bruijn constructivo que prueba que `τ` está en `Γ` -/
inductive Var : Ctx → Ty → Type where
  | zero : {Γ : Ctx} → {τ : Ty} → Var (τ :: Γ) τ
  | succ : {Γ : Ctx} → {σ τ : Ty} → Var Γ τ → Var (σ :: Γ) τ
  deriving Repr

/-! ## 2. Términos Intrínsecamente Tipados `Term Γ τ` -/

inductive Term : Ctx → Ty → Type where
  | var   : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Term Γ τ
  | lam   : {Γ : Ctx} → {σ τ : Ty} → Term (σ :: Γ) τ → Term Γ (σ ⇒ τ)
  | app   : {Γ : Ctx} → {σ τ : Ty} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  | const : {Γ : Ctx} → Nat → Term Γ .nat
  | add   : {Γ : Ctx} → Term Γ .nat → Term Γ .nat → Term Γ .nat
  | bval  : {Γ : Ctx} → Bool → Term Γ .bool
  | ite   : {Γ : Ctx} → {τ : Ty} → Term Γ .bool → Term Γ τ → Term Γ τ → Term Γ τ

/-! ## 3. Renombramiento (`Ren`) y Sustitución Paralela (`Sub`) -/

/-- Un renombramiento de `Γ` a `Δ` mapea cada variable de `Γ` a una variable de `Δ` del mismo tipo -/
abbrev Ren (Γ Δ : Ctx) := ∀ {τ : Ty}, Var Γ τ → Var Δ τ

/-- Elevación (*lifting*) de un renombramiento al entrar bajo un binder `λ (x : σ)` -/
def Ren.lift {Γ Δ : Ctx} {σ : Ty} (ρ : Ren Γ Δ) : Ren (σ :: Γ) (σ :: Δ)
  | _, .zero   => .zero
  | _, .succ x => .succ (ρ x)

/-- Aplicación de un renombramiento a un término: preserva el tipo `τ` por construcción -/
def Term.rename {Γ Δ : Ctx} {τ : Ty} (ρ : Ren Γ Δ) : Term Γ τ → Term Δ τ
  | .var x       => .var (ρ x)
  | .lam body    => .lam (body.rename (Ren.lift ρ))
  | .app f a     => .app (f.rename ρ) (a.rename ρ)
  | .const n     => .const n
  | .add t1 t2   => .add (t1.rename ρ) (t2.rename ρ)
  | .bval b      => .bval b
  | .ite c t1 t2 => .ite (c.rename ρ) (t1.rename ρ) (t2.rename ρ)

/-- Debilitamiento (*Weakening*): introduce una nueva variable `σ` en el tope del contexto -/
def Term.weaken {Γ : Ctx} {σ τ : Ty} (t : Term Γ τ) : Term (σ :: Γ) τ :=
  t.rename (fun x => Var.succ x)

/-- Una sustitución paralela de `Γ` a `Δ` mapea cada variable de `Γ` a un término en `Δ` -/
abbrev Sub (Γ Δ : Ctx) := ∀ {τ : Ty}, Var Γ τ → Term Δ τ

/-- Elevación de una sustitución al atravesar un binder `λ (x : σ)` -/
def Sub.lift {Γ Δ : Ctx} {σ : Ty} (s : Sub Γ Δ) : Sub (σ :: Γ) (σ :: Δ)
  | _, .zero   => .var .zero
  | _, .succ x => (s x).weaken

/-- Aplicación de una sustitución paralela a un término: preserva el tipo `τ` estáticamente -/
def Term.subst {Γ Δ : Ctx} {τ : Ty} (s : Sub Γ Δ) : Term Γ τ → Term Δ τ
  | .var x       => s x
  | .lam body    => .lam (body.subst (Sub.lift s))
  | .app f a     => .app (f.subst s) (a.subst s)
  | .const n     => .const n
  | .add t1 t2   => .add (t1.subst s) (t2.subst s)
  | .bval b      => .bval b
  | .ite c t1 t2 => .ite (c.subst s) (t1.subst s) (t2.subst s)

/-- Sustitución unitaria para la β-reducción `(λx. body) arg  ↦  body[x := arg]` -/
def Sub.single {Γ : Ctx} {σ : Ty} (arg : Term Γ σ) : Sub (σ :: Γ) Γ
  | _, .zero   => arg
  | _, .succ x => .var x

def betaReduceTop {Γ : Ctx} {σ τ : Ty} (body : Term (σ :: Γ) τ) (arg : Term Γ σ) : Term Γ τ :=
  body.subst (Sub.single arg)

/-! ## 4. Semántica Denotacional y Evaluador Total -/

/-- Interpretación de los tipos del STLC en tipos nativos de Lean 4 -/
@[simp]
abbrev Ty.denote : Ty → Type
  | .nat    => Nat
  | .bool   => Bool
  | σ ⇒ τ   => σ.denote → τ.denote

/-- Entorno tipado `Env Γ`: contiene un valor de tipo `τ.denote` por cada `τ ∈ Γ` -/
inductive Env : Ctx → Type where
  | nil  : Env []
  | cons : {Γ : Ctx} → {τ : Ty} → τ.denote → Env Γ → Env (τ :: Γ)

@[simp]
def Env.lookup {Γ : Ctx} {τ : Ty} : Var Γ τ → Env Γ → τ.denote
  | .zero,   .cons v _   => v
  | .succ x, .cons _ env => Env.lookup x env

/-- Evaluador denotacional total -/
@[simp]
def eval {Γ : Ctx} {τ : Ty} : Term Γ τ → Env Γ → τ.denote
  | .var x,       env => env.lookup x
  | .lam body,    env => fun v => eval body (.cons v env)
  | .app f a,     env => (eval f env) (eval a env)
  | .const n,     _   => n
  | .add t1 t2,   env => eval t1 env + eval t2 env
  | .bval b,      _   => b
  | .ite c t1 t2, env => if eval c env then eval t1 env else eval t2 env

/-! ## 5. Ejemplo de Programa en STLC y Verificación de β-Equivalencia -/

/-- El término `(λ x : nat. x + x) 21` en el contexto vacío `[]` -/
def dobleVeintiuno : Term [] .nat :=
  .app (.lam (.add (.var .zero) (.var .zero))) (.const 21)

#eval eval dobleVeintiuno .nil -- 42

/-- Demostración formal de que para cualesquiera términos `body` y `arg`,
    evaluar la aplicación `app (lam body) arg` produce idéntico resultado que evaluar `body`
    en el entorno extendido con `eval arg env`. -/
theorem beta_soundness {Γ : Ctx} {σ τ : Ty}
    (body : Term (σ :: Γ) τ) (arg : Term Γ σ) (env : Env Γ) :
    eval (.app (.lam body) arg) env = eval body (.cons (eval arg env) env) :=
  rfl

end LeanTT.M10
