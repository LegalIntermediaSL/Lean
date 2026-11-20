/-!
# Módulo 51: Transformación CPS (*Continuation-Passing Style*) y Preservación Semántica (Teorema de Plotkin)
## Ámbito: Compiladores Funcionales, Representaciones Intermedias y Semántica de Continuaciones

En los compiladores de lenguajes funcionales (como SML/NJ, Scheme o fases intermedias de Lean 4),
la transformación a **Estilo de Paso de Continuaciones (CPS)** hace explícito el flujo de control,
el orden de evaluación y el retorno de cada subexpresión pasando una **continuación** `k : Val → Ans`.

En este módulo:
1. Definimos un lenguaje de expresiones aritméticas y condicionales `Expr` y su evaluador directo `evalDirect`.
2. Definimos el evaluador en estilo de paso de continuaciones `evalCPS e k`.
3. Demostramos formalmente el **Teorema de Adecuación de Plotkin (1975)**: para toda expresión `e`
   y toda continuación `k`, `evalCPS e k = k (evalDirect e)`.
4. Deducimos como corolario que ejecutar `runCPS e` (con la continuación identidad) coincide
   exactamente con la evaluación directa `evalDirect e`.
-/

namespace LeanTT.M51

/-- Sintaxis de expresiones con constantes, suma, producto y condicional si-cero -/
inductive Expr where
  | lit   : Nat → Expr
  | add   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
  | ifPos : Expr → Expr → Expr → Expr
  deriving Repr, DecidableEq

/-- Semántica denotacional en Estilo Directo (`Direct Style`) -/
@[simp]
def evalDirect : Expr → Nat
  | .lit n        => n
  | .add e1 e2    => evalDirect e1 + evalDirect e2
  | .mul e1 e2    => evalDirect e1 * evalDirect e2
  | .ifPos c t f  => if evalDirect c > 0 then evalDirect t else evalDirect f

/-- Semántica en Estilo de Paso de Continuaciones (`Continuation-Passing Style`, CPS),
    polimórfica en el tipo de respuesta final `α`: -/
@[simp]
def evalCPS {α : Type} (e : Expr) (k : Nat → α) : α :=
  match e with
  | .lit n =>
    k n
  | .add e1 e2 =>
    evalCPS e1 (fun v1 =>
      evalCPS e2 (fun v2 =>
        k (v1 + v2)))
  | .mul e1 e2 =>
    evalCPS e1 (fun v1 =>
      evalCPS e2 (fun v2 =>
        k (v1 * v2)))
  | .ifPos c t f =>
    evalCPS c (fun vc =>
      if vc > 0 then evalCPS t k else evalCPS f k)

/-- Ejecución completa en CPS instanciando la continuación inicial con la identidad `id` -/
@[simp]
def runCPS (e : Expr) : Nat :=
  evalCPS e (fun v => v)

/-! ## 1. El Teorema Fundamental de Preservación Semántica CPS (Plotkin, 1975) -/

/-- TEOREMA 1 (Identidad Fundamental de CPS para Continuaciones Arbitrarias):
    Para toda expresión `e : Expr`, todo tipo de respuesta `α` y toda continuación `k : Nat → α`,
    evaluar `e` en CPS bajo `k` produce exactamente `k (evalDirect e)`. -/
@[simp]
theorem evalCPS_eq_k_evalDirect {α : Type} (e : Expr) (k : Nat → α) :
    evalCPS e k = k (evalDirect e) := by
  induction e generalizing k with
  | lit n =>
    rfl
  | add e1 e2 ih1 ih2 =>
    dsimp [evalCPS, evalDirect]
    rw [ih1, ih2]
  | mul e1 e2 ih1 ih2 =>
    dsimp [evalCPS, evalDirect]
    rw [ih1, ih2]
  | ifPos c t f ihc iht ihf =>
    dsimp [evalCPS, evalDirect]
    rw [ihc]
    split
    · exact iht k
    · exact ihf k

/-- COROLARIO 1 (Corrección Total de `runCPS`):
    Evaluar una expresión mediante CPS con la continuación identidad devuelve el mismo valor
    que el evaluador en estilo directo. -/
theorem runCPS_eq_evalDirect (e : Expr) :
    runCPS e = evalDirect e := by
  dsimp [runCPS]
  exact evalCPS_eq_k_evalDirect e (fun v => v)

/-- TEOREMA 2 (Naturalidad / Fusión de Continuaciones):
    Post-componer una función `f : α → β` después de `evalCPS e k` equivale a fusionar `f ∘ k`
    como una única continuación. -/
theorem map_evalCPS {α β : Type} (e : Expr) (k : Nat → α) (f : α → β) :
    f (evalCPS e k) = evalCPS e (fun v => f (k v)) := by
  rw [evalCPS_eq_k_evalDirect, evalCPS_eq_k_evalDirect]

end LeanTT.M51
