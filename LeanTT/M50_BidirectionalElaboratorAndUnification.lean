/-!
# Módulo 50 (Segundo Proyecto Cumbre): Elaboración Bidireccional (`synth` / `check`) y Sustitución de Metavariables
## Ámbito: Arquitectura Interna del Elaborador de Lean 4 (Complemento del Mini-Kernel `M40`)

En el **Módulo 40** construimos el **Kernel** de un asistente de pruebas, donde todas las
abstracciones $\lambda (x : A) \Rightarrow t$ llevan su tipo explícito.
Pero cuando el usuario escribe en Lean 4 `fun x => x` esperando el tipo `Nat → Nat`, ¿cómo
descubre Lean automáticamente que `x` tiene tipo `Nat`?

Gracias a dos mecanismos que viven en el **Elaborador** (antes de enviar el término al Kernel):
1. **Tipado Bidireccional (Pierce & Turner, 1998):** Divide el tipado en dos modos mutuamente recursivos:
   - **Modo Síntesis (`synth Γ e ⇒ τ`):** Deduce el tipo hacia arriba desde la expresión.
   - **Modo Comprobación (`check Γ e ⇐ τ`):** Empuja el tipo esperado `τ` hacia adentro, permitiendo
     elaborar `lamUnannot body` contra `σ ⇒ ρ` sin anotar el tipo de la variable ligada!
2. **Metavariables (`?m`) y Sustituciones de Tipos:** Representan incógnitas de tipo que se
   instancian algebraicamente durante la unificación.
-/

namespace LeanTT.M50

/-- Expresiones de Tipo con Metavariables de Unificación (`.mvar id`) -/
inductive MetaTy where
  | nat  : MetaTy
  | bool : MetaTy
  | mvar : Nat → MetaTy             -- Metavariable de tipo `?m_i`
  | arr  : MetaTy → MetaTy → MetaTy -- Tipo función `σ ⇒ τ`
  deriving Repr, DecidableEq

infixr:70 " ⇒ₘ " => MetaTy.arr

namespace MetaTy

/-- Una sustitución de metavariables `Subst` asigna a cada índice `?m_i` un `MetaTy` -/
abbrev Subst := Nat → MetaTy

/-- La sustitución identidad (deja cada metavariable `?m_i` intacta) -/
def idSubst : Subst :=
  fun i => .mvar i

/-- Aplica una sustitución `σ` recursivamente a todas las metavariables de un tipo `τ` -/
@[simp]
def applySubst (σ : Subst) : MetaTy → MetaTy
  | .nat       => .nat
  | .bool      => .bool
  | .mvar i    => σ i
  | .arr t1 t2 => .arr (applySubst σ t1) (applySubst σ t2)

/-- Composición algebraica de dos sustituciones de metavariables (`σ2 ∘ₛ σ1`) -/
def compSubst (σ2 σ1 : Subst) : Subst :=
  fun i => applySubst σ2 (σ1 i)

/-! ## 1. Leyes de Monoide de las Sustituciones de Metavariables -/

/-- TEOREMA 1: Aplicar la sustitución identidad `idSubst` a cualquier `τ` devuelve `τ` -/
@[simp]
theorem applySubst_id (τ : MetaTy) :
    applySubst idSubst τ = τ := by
  induction τ with
  | nat               => rfl
  | bool              => rfl
  | mvar i            => rfl
  | arr t1 t2 ih1 ih2 =>
    dsimp [applySubst]
    rw [ih1, ih2]

/-- TEOREMA 2 (Funtorialidad / Asociatividad de la Sustitución):
    Aplicar `σ1` y luego `σ2` es idéntico a aplicar de una sola vez `compSubst σ2 σ1`! -/
theorem applySubst_comp (σ2 σ1 : Subst) (τ : MetaTy) :
    applySubst σ2 (applySubst σ1 τ) = applySubst (compSubst σ2 σ1) τ := by
  induction τ with
  | nat               => rfl
  | bool              => rfl
  | mvar i            => rfl
  | arr t1 t2 ih1 ih2 =>
    dsimp [applySubst]
    rw [ih1, ih2]

end MetaTy

/-! ## 2. El Elaborador Bidireccional (`synth` ⇒ y `check` ⇐) con Términos sin Anotación -/

/-- Sintaxis de Superficie (`RawTerm`) donde las lambdas `lamUnannot` NO tienen anotación de tipo,
    exactamente como cuando escribimos `fun x => x` en el editor de Lean 4! -/
inductive RawTerm where
  | var        : Nat → RawTerm                 -- Variable de De Bruijn
  | litNat     : Nat → RawTerm                 -- Literal numérico
  | litBool    : Bool → RawTerm                -- Literal booleano
  | lamUnannot : RawTerm → RawTerm             -- `fun x => body` (¡SIN tipo en `x`!)
  | app        : RawTerm → RawTerm → RawTerm   -- Aplicación `f a`
  | annot      : RawTerm → MetaTy → RawTerm    -- Anotación explícita `(e : τ)`
  deriving Repr, DecidableEq

/-- Término del Kernel completamente elaborado (`CoreTerm`), donde toda lambda lleva ya su tipo -/
inductive CoreTerm where
  | var     : Nat → CoreTerm
  | litNat  : Nat → CoreTerm
  | litBool : Bool → CoreTerm
  | lam     : MetaTy → CoreTerm → CoreTerm     -- `fun (x : σ) => body` (¡CON tipo explícito!)
  | app     : CoreTerm → CoreTerm → CoreTerm
  deriving Repr, DecidableEq

abbrev ElabCtx := List MetaTy

/-- Búsqueda computable en el contexto de elaboración por índice de De Bruijn -/
@[simp]
def lookupElabCtx : ElabCtx → Nat → Option MetaTy
  | [],      _     => none
  | τ :: _,  0     => some τ
  | _ :: Γ,  i + 1 => lookupElabCtx Γ i

/-- Construcción simultánea por recursión estructural pura sobre `RawTerm` de:
    - Componente `.1` (`synth`): Modo Síntesis `Γ ⊢ e ⇒ (core, τ)`
    - Componente `.2` (`check`): Modo Comprobación `Γ ⊢ e ⇐ τ ⇝ core` -/
@[simp]
def synthCheck : RawTerm →
    (ElabCtx → Option (CoreTerm × MetaTy)) × (ElabCtx → MetaTy → Option CoreTerm)
  | .var i =>
    let s := fun Γ =>
      match lookupElabCtx Γ i with
      | some τ => some (.var i, τ)
      | none   => none
    (s, fun Γ expectedTy =>
      match s Γ with
      | some (eCore, inferredTy) => if inferredTy == expectedTy then some eCore else none
      | none => none)
  | .litNat n =>
    let s := fun _ : ElabCtx => some (CoreTerm.litNat n, MetaTy.nat)
    (s, fun _ expectedTy => if MetaTy.nat == expectedTy then some (.litNat n) else none)
  | .litBool b =>
    let s := fun _ : ElabCtx => some (CoreTerm.litBool b, MetaTy.bool)
    (s, fun _ expectedTy => if MetaTy.bool == expectedTy then some (.litBool b) else none)
  | .lamUnannot body =>
    let (_, checkBody) := synthCheck body
    ( fun _ => none -- Una lambda sin tipo no sintetiza por sí sola
    , fun Γ expectedTy =>
        match expectedTy with
        | .arr dom cod =>
          match checkBody (dom :: Γ) cod with
          | some bodyCore => some (.lam dom bodyCore)
          | none          => none
        | _ => none
    )
  | .app f a =>
    let (synthF, _) := synthCheck f
    let (_, checkA) := synthCheck a
    let s := fun Γ =>
      match synthF Γ with
      | some (fCore, .arr dom cod) =>
        match checkA Γ dom with
        | some aCore => some (.app fCore aCore, cod)
        | none       => none
      | _ => none
    (s, fun Γ expectedTy =>
      match s Γ with
      | some (eCore, inferredTy) => if inferredTy == expectedTy then some eCore else none
      | none => none)
  | .annot e τ =>
    let (_, checkE) := synthCheck e
    let s := fun Γ =>
      match checkE Γ τ with
      | some eCore => some (eCore, τ)
      | none       => none
    (s, fun Γ expectedTy =>
      match s Γ with
      | some (eCore, inferredTy) => if inferredTy == expectedTy then some eCore else none
      | none => none)

@[simp]
def synth (Γ : ElabCtx) (e : RawTerm) : Option (CoreTerm × MetaTy) :=
  (synthCheck e).1 Γ

@[simp]
def check (Γ : ElabCtx) (e : RawTerm) (τ : MetaTy) : Option CoreTerm :=
  (synthCheck e).2 Γ τ

/-- Ejemplo cumbre: El usuario escribe `((fun f => fun x => f x) : (Nat ⇒ Bool) ⇒ Nat ⇒ Bool)`
    sin anotar el tipo de `f` ni el de `x`. ¡El elaborador bidireccional rellena todos los tipos
    para el Kernel automáticamente! -/
def rawApply : RawTerm :=
  .annot (.lamUnannot (.lamUnannot (.app (.var 1) (.var 0))))
         ((.nat ⇒ₘ .bool) ⇒ₘ (.nat ⇒ₘ .bool))

theorem elab_bidirectional_fills_missing_lambda_types :
    synth [] rawApply =
      some (.lam (.nat ⇒ₘ .bool) (.lam .nat (.app (.var 1) (.var 0))),
            (.nat ⇒ₘ .bool) ⇒ₘ (.nat ⇒ₘ .bool)) :=
  rfl

end LeanTT.M50
