import Lean

/-!
# Módulo 12: Metaprogramación en Lean 4 — El AST `Expr`, Macros, DSLs y Tácticas Propias
Guía teórica asociada: `docs/12_metaprogramacion_y_kernel.md`

En este módulo exploramos:
1. Construcción manual de expresiones del kernel `Lean.Expr` (índices de De Bruijn `.bvar`,
   `.lam`, `.forallE`, `.app`, `.const`).
2. Macros higiénicas y sintaxis extensible (`syntax` + `macro_rules`).
3. Creación de un DSL embebido con su propia sintaxis en Lean 4.
4. Creación desde cero de tácticas personalizadas usando `macro` y `TacticM` (`elab`).
-/

namespace LeanTT.M12

open Lean Meta Elab Tactic

/-! ## 1. Construcción Directa de Términos `Lean.Expr` del Kernel -/

/-- Construimos manualmente la expresión del kernel para la función identidad
    `fun (x : Nat) => x` usando el constructor `Expr.lam` y el índice de De Bruijn `bvar 0`: -/
def exprIdentidadNat : Expr :=
  Expr.lam `x (Expr.const ``Nat []) (Expr.bvar 0) BinderInfo.default

/-- Construimos manualmente el Π-tipo `∀ (P : Prop), P → P` usando `Expr.forallE`:
    Observa que en `P → P`, el dominio es `bvar 0` y como `forallE` introduce un nuevo
    binder anónimo, dentro del codominio `P` pasa a ser `bvar 1`. -/
def exprPropIdType : Expr :=
  Expr.forallE `P (Expr.sort Level.zero)
    (Expr.forallE `_ (Expr.bvar 0) (Expr.bvar 1) BinderInfo.default)
    BinderInfo.default

/-- Un pequeño metaprograma en `MetaM` que verifica que `exprIdentidadNat` está bien tipada
    en el kernel e infiere su tipo (`Nat → Nat`). -/
def inspeccionarExpr : MetaM String := do
  let ty ← inferType exprIdentidadNat
  let fmtExpr ← ppExpr exprIdentidadNat
  let fmtTy   ← ppExpr ty
  return s!"Término: {fmtExpr}  |  Tipo inferido por el kernel: {fmtTy}"

#eval inspeccionarExpr

/-! ## 2. Sintaxis Extensible y Macros Higiénicas -/

/-- Creamos una notación estilo matemático en español `si_entonces_sino` mediante `macro` -/
macro "si " c:term " entonces " t:term " sino " e:term : term =>
  `(if $c then $t else $e)

#eval si 3 < 5 entonces "menor" sino "mayor o igual"

/-- Creación de un mini-DSL para lógica de conjuntos sobre predicados `α → Prop` -/
abbrev Conjunto (α : Type) := α → Prop

notation:50 x " ∈ₚ " S => S x
infixl:65 " ∪ₚ " => fun (A B : Conjunto _) x => A x ∨ B x
infixl:70 " ∩ₚ " => fun (A B : Conjunto _) x => A x ∧ B x

theorem interseccion_conmutativa {α : Type} (A B : Conjunto α) (x : α) :
    (x ∈ₚ (A ∩ₚ B)) ↔ (x ∈ₚ (B ∩ₚ A)) :=
  ⟨fun ⟨ha, hb⟩ => ⟨hb, ha⟩, fun ⟨hb, ha⟩ => ⟨ha, hb⟩⟩

/-! ## 3. Creación de Tácticas Propias -/

/-- 1. Táctica basada en macro (`desglosar_iff`):
    Introduce automáticamente ambas direcciones de un objetivo `_ ↔ _` nombrando la hipótesis. -/
macro "desglosar_iff " h:ident : tactic =>
  `(tactic| constructor <;> intro $h)

example (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  desglosar_iff h
  · exact ⟨h.2, h.1⟩
  · exact ⟨h.2, h.1⟩

/-- 2. Táctica programada en la mónada `TacticM` usando `elab`:
    `buscar_hipotesis` recorre todas las declaraciones del contexto local `Γ` del objetivo activo
    y, si encuentra una hipótesis cuyo tipo es definicionalmente igual (`isDefEq`) a la meta,
    cierra la demostración asignando esa variable a la metavariable del objetivo. -/
elab "buscar_hipotesis" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← getMainTarget
  let lctx ← getLCtx
  for decl in lctx do
    if !decl.isImplementationDetail then
      if ← isDefEq decl.type target then
        goal.assign decl.toExpr
        return
  throwError "buscar_hipotesis: No se encontró ninguna hipótesis en Γ cuyo tipo coincida con la meta {target}"

/-- Ponemos a prueba nuestra táctica escrita en `TacticM`: -/
theorem prueba_con_nuestra_tactica (P Q R : Prop) (hp : P) (hq : Q) (hr : R) : Q := by
  buscar_hipotesis

/-- Incluso funciona cuando los tipos requieren reducción β/δ (`isDefEq`) para coincidir: -/
theorem prueba_con_reduccion (h : (fun x : Nat => x + 1) 4 = 5) : 5 = 5 := by
  buscar_hipotesis

end LeanTT.M12
