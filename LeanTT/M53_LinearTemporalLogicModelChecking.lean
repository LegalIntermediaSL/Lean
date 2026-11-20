/-!
# Módulo 53: Lógica Temporal Lineal (LTL) sobre Trazas Infinitas y Verificación de Invariantes
## Ámbito: *Model Checking*, Sistemas Reactivos y Especificación Formal (Estilo TLA+ / Spin)

Mientras que la lógica modal de Kripke (`M25`) razona sobre grafos generales de mundos posibles,
la **Lógica Temporal Lineal (LTL)** de Amir Pnueli (1977, Premio Turing 1996) razona sobre
**trazas infinitas de ejecución en el tiempo discreto** $\sigma : \mathbb{N} \to \text{State}$.

En este módulo:
1. Formalizamos trazas temporales `Trace σ`, el operador de desplazamiento temporal `dropTrace k τ`
   y los operadores modales de LTL:
   - `now P` (en el instante actual $t = 0$)
   - `next φ` ($\bigcirc \varphi$: en el instante siguiente $t = 1$)
   - `always φ` ($\Box \varphi$ / $G \varphi$: invariante en todo instante futuro $t \ge 0$)
   - `eventually φ` ($\Diamond \varphi$ / $F \varphi$: ocurre en algún instante futuro $t \ge 0$)
   - `untilLTL φ ψ` ($\varphi \;\mathcal{U}\; \psi$: $\varphi$ se mantiene hasta que se cumple $\psi$)
2. Demostramos la **Ecuación de Punto Fijo (Desplegado) de $\Box$**: $\Box \varphi \leftrightarrow (\varphi \land \bigcirc \Box \varphi)$.
3. Demostramos el **Principio de Inducción Temporal sobre Trazas**.
-/

namespace LeanTT.M53

/-- Una traza infinita de estados del sistema indexada por instantes discretos `t : Nat` -/
abbrev Trace (State : Type) := Nat → State

/-- Un predicado temporal (fórmula semántica de LTL) es una propiedad sobre trazas -/
abbrev LTLProp (State : Type) := Trace State → Prop

/-- Desplaza una traza `k` pasos hacia el futuro (`(dropTrace k τ) t = τ (k + t)`) -/
@[simp]
def dropTrace {State : Type} (k : Nat) (τ : Trace State) : Trace State :=
  fun t => τ (k + t)

/-- Lema algebraico de composición de desplazamientos temporales -/
@[simp]
theorem dropTrace_dropTrace {State : Type} (k1 k2 : Nat) (τ : Trace State) :
    dropTrace k1 (dropTrace k2 τ) = dropTrace (k2 + k1) τ := by
  funext t
  dsimp [dropTrace]
  ac_rfl

@[simp]
theorem dropTrace_zero {State : Type} (τ : Trace State) :
    dropTrace 0 τ = τ := by
  funext t
  dsimp [dropTrace]
  rw [Nat.zero_add]

/-! ## 1. Operadores Modales de la Lógica Temporal Lineal (LTL) -/

/-- Eleva un predicado de estado `P : State → Prop` al instante presente `t = 0` -/
@[simp]
def now {State : Type} (P : State → Prop) : LTLProp State :=
  fun τ => P (τ 0)

/-- Operador `Next` (`◯ φ` / `X φ`): la propiedad temporal `φ` se cumple a partir de `t = 1` -/
@[simp]
def next {State : Type} (φ : LTLProp State) : LTLProp State :=
  fun τ => φ (dropTrace 1 τ)

/-- Operador `Always` (`□ φ` / `G φ`): `φ` se cumple en todo desplazamiento futuro `k ≥ 0` -/
@[simp]
def always {State : Type} (φ : LTLProp State) : LTLProp State :=
  fun τ => ∀ k : Nat, φ (dropTrace k τ)

/-- Operador `Eventually` (`◇ φ` / `F φ`): existe algún instante futuro `k ≥ 0` donde vale `φ` -/
@[simp]
def eventually {State : Type} (φ : LTLProp State) : LTLProp State :=
  fun τ => ∃ k : Nat, φ (dropTrace k τ)

/-- Operador `Until` (`φ U ψ`): existe un instante `k` donde se cumple `ψ` y para todo `j < k` se mantiene `φ` -/
@[simp]
def untilLTL {State : Type} (φ ψ : LTLProp State) : LTLProp State :=
  fun τ => ∃ k : Nat, ψ (dropTrace k τ) ∧ ∀ j : Nat, j < k → φ (dropTrace j τ)

/-! ## 2. Teoremas Fundamentales de LTL y *Model Checking* -/

/-- TEOREMA 1 (Reflexividad de `Always`: `□ φ → φ`):
    Lo que vale siempre en el futuro vale en particular ahora mismo (`k = 0`). -/
theorem always_imp_self {State : Type} {φ : LTLProp State} (τ : Trace State)
    (h : always φ τ) : φ τ := by
  have h0 := h 0
  rwa [dropTrace_zero] at h0

/-- TEOREMA 2 (Invariancia bajo `Eventually`: `□ φ → ◇ φ`):
    Si `φ` vale en todo instante, entonces existe al menos un instante (`k = 0`) donde vale `φ`. -/
theorem always_imp_eventually {State : Type} {φ : LTLProp State} (τ : Trace State)
    (h : always φ τ) : eventually φ τ :=
  ⟨0, h 0⟩

/-- TEOREMA 3 (Ecuación de Desplegado en Punto Fijo de `Always`: `□ φ ↔ φ ∧ ◯(□ φ)`):
    Una propiedad `φ` se cumple en todo instante `k ≥ 0` si y solo si se cumple ahora (`k = 0`)
    y a partir del instante siguiente se cumple siempre! -/
theorem always_unfold_iff {State : Type} (φ : LTLProp State) (τ : Trace State) :
    always φ τ ↔ (φ τ ∧ next (always φ) τ) := by
  constructor
  · intro h
    refine ⟨always_imp_self τ h, ?_⟩
    intro k
    rw [dropTrace_dropTrace]
    exact h (1 + k)
  · rintro ⟨hNow, hNext⟩ k
    cases k with
    | zero =>
      rw [dropTrace_zero]
      exact hNow
    | succ k' =>
      have hk := hNext k'
      rw [dropTrace_dropTrace, Nat.add_comm 1 k'] at hk
      exact hk

/-- TEOREMA 4 (Principio de Inducción Temporal para Invariantes de Estado):
    Si un predicado de estado `Inv : State → Prop` vale en `τ 0` y es inductivo a lo largo de la traza
    (`∀ t, Inv (τ t) → Inv (τ (t + 1))`), entonces `always (now Inv) τ` se cumple en toda la traza! -/
theorem trace_invariant_induction {State : Type} (Inv : State → Prop) (τ : Trace State)
    (hInit : Inv (τ 0))
    (hStep : ∀ t : Nat, Inv (τ t) → Inv (τ (t + 1))) :
    always (now Inv) τ := by
  intro k
  dsimp [now, dropTrace]
  induction k with
  | zero      => exact hInit
  | succ k ih => exact hStep k ih

end LeanTT.M53
