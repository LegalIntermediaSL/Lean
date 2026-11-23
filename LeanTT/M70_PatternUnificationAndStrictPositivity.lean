/-!
# Módulo 70 (Cuarto Proyecto Cumbre): Positividad Estricta de Tipos Inductivos y Unificación de Patrones de Miller
## Ámbito: Seguridad Lógica del Kernel y Motor de Unificación de Lean 4 (Completando `M40` + `M50` + `M60` + `M70`)

Con este **Módulo 70** completamos la **Tetralogía de Arquitectura Interna de Lean 4**:
- **`M40`:** El Mini-Kernel de Tipos Dependientes ($\Pi$, $\lambda$, `whnf`, `inferType`).
- **`M50`:** El Elaborador Bidireccional (`synth` $\Rightarrow$ / `check` $\Leftarrow$) y sustituciones de metavariables.
- **`M60`:** La Jerarquía Polimórfica de Universos (`Sort u`, `imax`) y *Large Elimination* (`boolRec`).
- **`M70` (este módulo):** Los **dos algoritmos guardianes** del Kernel y del Elaborador:

1. **El Comprobador de Positividad Estricta del Kernel (`checkStrictPositivity`):**
   ¿Por qué rechaza Lean 4 una declaración inductiva como `inductive Bad where | mk : (Bad → False) → Bad`?
   Porque si un tipo inductivo $I$ aparece **a la izquierda de una flecha** (en posición negativa/contravariante)
   en el argumento de uno de sus propios constructores, podemos aplicar un término a sí mismo y
   demostrar `False` en 4 líneas (la Paradoja de Curry)!
   Aquí implementamos el comprobador del kernel `isStrictlyPositive target ty` y demostramos sus
   propiedades formales de seguridad.

2. **El Unificador de Orden Superior en el Fragmento de Patrones de Dale Miller (`solvePattern1`):**
   Cuando el elaborador necesita resolver $?m(x_{\text{id}}) \doteq rhs$, abstrae $x_{\text{id}}$ como la variable
   ligada de De Bruijn `#0` (fallando si en `rhs` aparece cualquier otra variable fuera del alcance
   de $?m$). Demostramos el **Teorema de Corrección de la Unificación de Patrones (`solvePattern1_sound`)**:
   toda solución devuelta por `solvePattern1`, al aplicarse e instanciarse sobre `x_id`, reproduce
   exactamente el término objetivo `rhs`!
-/

namespace LeanTT.M70

/-! ## Parte I: El Comprobador de Positividad Estricta de Tipos Inductivos en el Kernel -/

/-- Representación de tipos para el análisis de positividad estricta de los argumentos
    de un constructor de un tipo inductivo con identificador `IndId := Nat`: -/
inductive IndTy where
  | base  : Nat → IndTy               -- Tipo básico o inductivo con identificador `id`
  | prod  : IndTy → IndTy → IndTy     -- Producto `A × B`
  | arrow : IndTy → IndTy → IndTy     -- Tipo función `A → B`
  deriving Repr, DecidableEq

namespace IndTy

/-- Comprueba si el tipo inductivo `target` aparece en cualquier lugar de `ty` (`occurs target ty`): -/
@[simp]
def occurs (target : Nat) : IndTy → Bool
  | .base id   => id == target
  | .prod a b  => occurs target a || occurs target b
  | .arrow a b => occurs target a || occurs target b

/-- Comprobador de **Positividad Estricta** del Kernel (`isStrictlyPositive target ty`):
    Un argumento de constructor `ty` es estrictamente positivo respecto al tipo inductivo `target` si:
    - En `base id`: siempre es válido (sea `id == target` o cualquier otro tipo).
    - En `prod a b`: tanto `a` como `b` son estrictamente positivos.
    - En `arrow dom cod`: el tipo `target` **NO PUEDE APARECER EN ABSOLUTO en el dominio `dom`**
      (`!occurs target dom`), y el codominio `cod` debe ser estrictamente positivo! -/
@[simp]
def isStrictlyPositive (target : Nat) : IndTy → Bool
  | .base _        => true
  | .prod a b      => isStrictlyPositive target a && isStrictlyPositive target b
  | .arrow dom cod => !occurs target dom && isStrictlyPositive target cod

/-- TEOREMA 1 (Todo Tipo donde no Ocurre `target` es Estrictamente Positivo): -/
theorem strictlyPositive_of_not_occurs (target : Nat) (ty : IndTy)
    (hNo : occurs target ty = false) :
    isStrictlyPositive target ty = true := by
  induction ty with
  | base _ =>
    rfl
  | prod a b iha ihb =>
    dsimp [occurs] at hNo
    rw [Bool.or_eq_false_iff] at hNo
    dsimp [isStrictlyPositive]
    rw [iha hNo.1, ihb hNo.2]
    rfl
  | arrow dom cod _ ihCod =>
    dsimp [occurs] at hNo
    rw [Bool.or_eq_false_iff] at hNo
    dsimp [isStrictlyPositive]
    rw [hNo.1, ihCod hNo.2]
    rfl

/-- TEOREMA 2 (El Kernel Rechaza Garantizadamente la Paradoja de Curry `(I → False) → I`):
    Para cualquier identificador de tipo inductivo `I` y cualquier tipo `falseTy`, el argumento
    de constructor negativo `I → falseTy` (`.arrow (.base I) falseTy`) es rechazado (`false`)
    por `isStrictlyPositive I`! -/
theorem kernel_rejects_negative_occurrence (I : Nat) (falseTy : IndTy) :
    isStrictlyPositive I (.arrow (.base I) falseTy) = false := by
  dsimp [isStrictlyPositive, occurs]
  simp

end IndTy

/-! ## Parte II: Unificación de Orden Superior en el Fragmento de Patrones de Dale Miller (1991) -/

/-- Términos con variables libres del contexto (`fvar id`), la variable ligada `#0` (`bvar0`),
    constantes y operaciones binarias, para la ecuación de unificación `?m (fvar targetId) ≐ rhs`: -/
inductive PatTerm where
  | fvar  : Nat → PatTerm             -- Variable libre del contexto `x_id`
  | bvar0 : PatTerm                   -- Variable ligada `#0` de la solución `λ #0 => ...`
  | const : Nat → PatTerm             -- Constante
  | app   : PatTerm → PatTerm → PatTerm -- Aplicación `f a`
  deriving Repr, DecidableEq

namespace PatTerm

/-- Abstrae la única variable libre permitida `targetId` reemplazándola por `.bvar0`.
    Si encuentra cualquier otra variable libre `id ≠ targetId` (que escaparía del alcance de `?m`)
    o si `rhs` ya contenía un `.bvar0` suelto, falla devolviendo `none`: -/
@[simp]
def abstractFVar1 (targetId : Nat) : PatTerm → Option PatTerm
  | .fvar id =>
    if id == targetId then some .bvar0 else none
  | .bvar0 =>
    none
  | .const c =>
    some (.const c)
  | .app f a =>
    match abstractFVar1 targetId f, abstractFVar1 targetId a with
    | some fBody, some aBody => some (.app fBody aBody)
    | _,          _          => none

/-- Instancia la variable ligada `.bvar0` del cuerpo de la solución `λ #0 => body` con un argumento `arg` -/
@[simp]
def instantiateBVar0 (arg : PatTerm) : PatTerm → PatTerm
  | .fvar id => .fvar id
  | .bvar0   => arg
  | .const c => .const c
  | .app f a => .app (instantiateBVar0 arg f) (instantiateBVar0 arg a)

/-- TEOREMA CUMBRE (`M70` — Corrección Formal del Unificador de Patrones de Miller):
    Si `abstractFVar1 targetId rhs` tiene éxito y devuelve el cuerpo de la solución ` some body`
    (es decir, `?m := λ x => body`), entonces al aplicar dicha solución al argumento `.fvar targetId`
    (`instantiateBVar0 (.fvar targetId) body`) ¡obtenemos exactamente el lado derecho original `rhs`! -/
theorem miller_pattern_unification_sound (targetId : Nat) (rhs body : PatTerm)
    (hSolve : abstractFVar1 targetId rhs = some body) :
    instantiateBVar0 (.fvar targetId) body = rhs := by
  induction rhs generalizing body with
  | fvar id =>
    dsimp [abstractFVar1] at hSolve
    split at hSolve
    · next hEq =>
      simp only [Option.some.injEq] at hSolve
      subst hSolve
      simp only [beq_iff_eq] at hEq
      subst hEq
      rfl
    · contradiction
  | bvar0 =>
    dsimp [abstractFVar1] at hSolve
    contradiction
  | const c =>
    dsimp [abstractFVar1] at hSolve
    simp only [Option.some.injEq] at hSolve
    subst hSolve
    rfl
  | app f a ihf iha =>
    dsimp [abstractFVar1] at hSolve
    cases hf : abstractFVar1 targetId f with
    | none =>
      rw [hf] at hSolve
      contradiction
    | some fBody =>
      rw [hf] at hSolve
      cases ha : abstractFVar1 targetId a with
      | none =>
        rw [ha] at hSolve
        contradiction
      | some aBody =>
        rw [ha] at hSolve
        simp only [Option.some.injEq] at hSolve
        subst hSolve
        dsimp [instantiateBVar0]
        rw [ihf fBody hf, iha aBody ha]

end PatTerm
end LeanTT.M70
