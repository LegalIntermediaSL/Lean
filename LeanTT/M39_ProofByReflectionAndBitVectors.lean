/-!
# Módulo 39: Pruebas por Reflexión Computacional (*Proof by Reflection*)
## Ámbito: Automatización de Tácticas de Alto Rendimiento (Cómo Funcionan `ring` y `omega`)

Cuando una meta matemática tiene cientos de términos asociativos o constantes (por ejemplo,
`((x + 0) + (y + z)) + 0 = x + (y + z)`), encadenar `rw [Nat.add_assoc]` y `rw [Nat.add_zero]`
crea un término de prueba enorme.

La técnica de **Prueba por Reflexión (*Proof by Reflection*)** (Boutin, 1997) consiste en:
1. Representar la expresión mediante un AST sintáctico `MonoidExpr` (*Reificación*).
2. Escribir un normalizador computable `norm : MonoidExpr → List Nat` que aplana los paréntesis
   y elimina los elementos neutros `0`.
3. Demostrar **una sola vez** el teorema `denote_norm_eq : denote env e = denoteList env (norm e)`.
4. A partir de ese momento, demostrar que dos expresiones grandes son iguales se reduce a ejecutar
   **`rfl`** para que el kernel compruebe que sus listas normalizadas coinciden!
-/

namespace LeanTT.M39

/-- Sintaxis reificada de expresiones en un monoide aditivo con variables indexadas por `Nat` -/
inductive AddExpr where
  | zero : AddExpr
  | var  : Nat → AddExpr
  | add  : AddExpr → AddExpr → AddExpr
  deriving Repr, DecidableEq

/-- Semántica denotacional de `AddExpr` dado un entorno de variables `env : Nat → Nat` -/
@[simp]
def denote (env : Nat → Nat) : AddExpr → Nat
  | .zero      => 0
  | .var i     => env i
  | .add e1 e2 => denote env e1 + denote env e2

/-- Normalizador sintáctico: aplana todos los árboles `.add` en una lista plana de índices de
    variables y elimina todos los `.zero`. -/
@[simp]
def flatten : AddExpr → List Nat
  | .zero      => []
  | .var i     => [i]
  | .add e1 e2 => flatten e1 ++ flatten e2

/-- Semántica de una lista plana de variables -/
@[simp]
def denoteList (env : Nat → Nat) : List Nat → Nat
  | []      => 0
  | i :: is => env i + denoteList env is

/-- Lema de homomorfismo: `denoteList` convierte `++` en `+` -/
theorem denoteList_append (env : Nat → Nat) (xs ys : List Nat) :
    denoteList env (xs ++ ys) = denoteList env xs + denoteList env ys := by
  induction xs with
  | nil          => simp
  | cons i is ih =>
    dsimp [denoteList]
    rw [ih, Nat.add_assoc]

/-- Teorema de Corrección del Normalizador: evaluar `e` es igual a evaluar su lista aplanada -/
theorem denote_eq_denoteList_flatten (env : Nat → Nat) (e : AddExpr) :
    denote env e = denoteList env (flatten e) := by
  induction e with
  | zero          => rfl
  | var i         => simp
  | add e1 e2 ih1 ih2 =>
    dsimp [denote, flatten]
    rw [denoteList_append, ih1, ih2]

/-- TEOREMA DE REFLEXIÓN COMPUTACIONAL:
    Para demostrar que dos expresiones arbitrariamente anidadas `e1` y `e2` tienen el mismo
    valor en cualquier entorno `env`, ¡basta comprobar que `flatten e1 = flatten e2` por `rfl`! -/
theorem reflect_add_eq (env : Nat → Nat) (e1 e2 : AddExpr)
    (h_norm : flatten e1 = flatten e2) :
    denote env e1 = denote env e2 := by
  rw [denote_eq_denoteList_flatten env e1]
  rw [denote_eq_denoteList_flatten env e2]
  rw [h_norm]

/-- Ejemplo: Demostramos una identidad con múltiples paréntesis y ceros con un simple `rfl`! -/
example (a b c d : Nat) :
    let env := fun | 0 => a | 1 => b | 2 => c | _ => d
    denote env (.add (.add (.var 0) .zero) (.add (.var 1) (.add .zero (.var 2)))) =
    denote env (.add (.var 0) (.add (.add (.var 1) (.var 2)) .zero)) :=
  fun env => reflect_add_eq env _ _ rfl

end LeanTT.M39
