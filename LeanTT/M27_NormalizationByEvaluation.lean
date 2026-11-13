/-!
# Módulo 27: Normalización por Evaluación (NbE) para el Cálculo Lambda Tipado
## Ámbito: Implementación de Asistentes de Pruebas y Teoría de la Demostración

¿Cómo reduce un asistente de pruebas moderno (como Agda, Coq o Lean) un término del cálculo
lambda a su **forma normal βη** sin hacer sustituciones sintácticas lentas paso a paso?
Mediante **Normalización por Evaluación (NbE)** (Berger & Schwichtenberg, 1991):
1. **Evalúa (`evalNbE`)** el término sintáctico hacia el dominio semántico del metalenguaje (Lean 4).
2. **Reifica (`reify`)** el valor semántico de vuelta a un término en Forma Normal (`Nf`),
   usando `reflect` para inyectar variables frescas ("términos neutros" `Ne`) en las funciones.
-/

namespace LeanTT.M27

/-- Tipos simples con un tipo base `ι` y funciones `σ ⇒ τ` -/
inductive Ty where
  | base : Ty
  | arr  : Ty → Ty → Ty
  deriving DecidableEq, Repr

infixr:70 " ⇒ " => Ty.arr
abbrev Ctx := List Ty

/-- Variables tipadas de De Bruijn -/
inductive Var : Ctx → Ty → Type where
  | zero : {Γ : Ctx} → {τ : Ty} → Var (τ :: Γ) τ
  | succ : {Γ : Ctx} → {σ τ : Ty} → Var Γ τ → Var (σ :: Γ) τ
  deriving Repr

/-- Términos arbitrarios del cálculo lambda simplemente tipado -/
inductive Term : Ctx → Ty → Type where
  | var : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Term Γ τ
  | lam : {Γ : Ctx} → {σ τ : Ty} → Term (σ :: Γ) τ → Term Γ (σ ⇒ τ)
  | app : {Γ : Ctx} → {σ τ : Ty} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  deriving Repr

/-! ## Gramática de Formas Normales βη (`Nf`) y Términos Neutros (`Ne`) -/
mutual
  inductive Ne : Ctx → Ty → Type where
    | nvar : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Ne Γ τ
    | napp : {Γ : Ctx} → {σ τ : Ty} → Ne Γ (σ ⇒ τ) → Nf Γ σ → Ne Γ τ

  inductive Nf : Ctx → Ty → Type where
    | nlam : {Γ : Ctx} → {σ τ : Ty} → Nf (σ :: Γ) τ → Nf Γ (σ ⇒ τ)
    | neu  : {Γ : Ctx} → Ne Γ .base → Nf Γ .base
end

/-- Renombramiento (debilitamiento) para Términos Neutros y Formas Normales -/
abbrev Ren (Γ Δ : Ctx) := ∀ {τ : Ty}, Var Γ τ → Var Δ τ

def Ren.id {Γ : Ctx} : Ren Γ Γ :=
  fun x => x

def Ren.wk {Γ : Ctx} {σ : Ty} : Ren Γ (σ :: Γ) :=
  fun x => .succ x

def Ren.comp {Γ Δ Ε : Ctx} (ρ' : Ren Δ Ε) (ρ : Ren Γ Δ) : Ren Γ Ε :=
  fun x => ρ' (ρ x)

def Ren.lift {Γ Δ : Ctx} {σ : Ty} (ρ : Ren Γ Δ) : Ren (σ :: Γ) (σ :: Δ)
  | _, .zero   => .zero
  | _, .succ x => .succ (ρ x)

mutual
  def Ne.rename {Γ Δ : Ctx} {τ : Ty} (ρ : Ren Γ Δ) : Ne Γ τ → Ne Δ τ
    | .nvar x   => .nvar (ρ x)
    | .napp f a => .napp (f.rename ρ) (a.rename ρ)

  def Nf.rename {Γ Δ : Ctx} {τ : Ty} (ρ : Ren Γ Δ) : Nf Γ τ → Nf Δ τ
    | .nlam b => .nlam (b.rename (Ren.lift ρ))
    | .neu n  => .neu (n.rename ρ)
end

-- Embebido canónico de Formas Normales de vuelta a Términos ordinarios
mutual
  def Ne.toTerm {Γ : Ctx} {τ : Ty} : Ne Γ τ → Term Γ τ
    | .nvar x   => .var x
    | .napp f a => .app f.toTerm a.toTerm

  def Nf.toTerm {Γ : Ctx} {τ : Ty} : Nf Γ τ → Term Γ τ
    | .nlam b => .lam b.toTerm
    | .neu n  => n.toTerm
end

/-! ## El Dominio Semántico de Prehaces (`Val Γ τ`) y las Funciones `reflect` y `reify` -/

/-- Interpretación semántica parametrizada por el contexto `Γ` (modelo de Kripke/Prehaces): -/
abbrev Val (Γ : Ctx) : Ty → Type
  | .base  => Nf Γ .base
  | σ ⇒ τ  => (Δ : Ctx) → Ren Γ Δ → Val Δ σ → Val Δ τ

def Val.rename {Γ Δ : Ctx} (τ : Ty) (ρ : Ren Γ Δ) : Val Γ τ → Val Δ τ :=
  match τ with
  | .base  => fun nf => nf.rename ρ
  | _ ⇒ _  => fun f Ε ρ' v => f Ε (Ren.comp ρ' ρ) v

mutual
  /-- `reflect` inyecta un término neutro `Ne Γ τ` en el dominio semántico `Val Γ τ` -/
  def reflect {Γ : Ctx} (τ : Ty) : Ne Γ τ → Val Γ τ :=
    match τ with
    | .base => fun n => .neu n
    | σ ⇒ ρ => fun n _ ren v => reflect ρ (.napp (n.rename ren) (reify σ v))
  termination_by sizeOf τ

  /-- `reify` extrae una Forma Normal βη `Nf Γ τ` a partir de un valor semántico `Val Γ τ` -/
  def reify {Γ : Ctx} (τ : Ty) : Val Γ τ → Nf Γ τ :=
    match τ with
    | .base => fun v => v
    | σ ⇒ ρ => fun f =>
      let freshVar : Val (σ :: Γ) σ := reflect σ (.nvar .zero)
      .nlam (reify ρ (f (σ :: Γ) Ren.wk freshVar))
  termination_by sizeOf τ
end

/-- Entornos semánticos y evaluador hacia `Val` -/
inductive SemEnv (Δ : Ctx) : Ctx → Type where
  | nil  : SemEnv Δ []
  | cons : {Γ : Ctx} → {τ : Ty} → Val Δ τ → SemEnv Δ Γ → SemEnv Δ (τ :: Γ)

def SemEnv.lookup {Δ Γ : Ctx} {τ : Ty} : Var Γ τ → SemEnv Δ Γ → Val Δ τ
  | .zero,   .cons v _   => v
  | .succ x, .cons _ env => env.lookup x

def SemEnv.rename {Γ Δ Ε : Ctx} (ρ : Ren Δ Ε) : SemEnv Δ Γ → SemEnv Ε Γ
  | .nil                => .nil
  | .cons (τ := τ) v env => .cons (Val.rename τ ρ v) (env.rename ρ)

def evalNbE {Γ Δ : Ctx} {τ : Ty} : Term Γ τ → SemEnv Δ Γ → Val Δ τ
  | .var x,    env => env.lookup x
  | .lam body, env => fun _ ρ v => evalNbE body (.cons v (env.rename ρ))
  | .app f a,  env => (evalNbE f env) Δ Ren.id (evalNbE a env)

def idEnv : (Γ : Ctx) → SemEnv Γ Γ
  | []      => .nil
  | τ :: Γ  => .cons (reflect τ (.nvar .zero)) ((idEnv Γ).rename Ren.wk)

/-- FUNCIÓN PRINCIPAL DE NbE: Normaliza cualquier `Term Γ τ` a su forma normal βη `Nf Γ τ` -/
def norm {Γ : Ctx} {τ : Ty} (t : Term Γ τ) : Nf Γ τ :=
  reify τ (evalNbE t (idEnv Γ))

/-- Prueba de fuego: El término con un redex `(λf. λx. f x) (λy. y)` se normaliza
    directamente a la identidad `λx. x`! -/
def redexTerm : Term [] (.base ⇒ .base) :=
  .app (.lam (.lam (.app (.var (.succ .zero)) (.var .zero)))) (.lam (.var .zero))

def idTerm : Term [] (.base ⇒ .base) :=
  .lam (.var .zero)

theorem nbe_elimina_redex : (norm redexTerm).toTerm = idTerm :=
  rfl

end LeanTT.M27
