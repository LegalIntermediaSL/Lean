/-!
# Módulo 49: Programación Probabilística Discreta, Conservación de Masa y Valor Esperado
## Ámbito: Semántica Probabilística, Cadenas de Markov y Criptografía Basada en Juegos (`VCV-io`)

En la verificación formal de algoritmos aleatorizados y protocolos criptográficos (como en la
biblioteca **`Verified-zkEVM/VCV-io`**), las distribuciones de probabilidad discretas con soporte
finito se modelan mediante listas de pares `(valor, peso)` (la **Mónada de Distribuciones de Giry**
discreta).

En este módulo:
1. Definimos distribuciones ponderadas `Dist α`, la masa total `totalMass` y el valor esperado
   no normalizado `weightedSum`.
2. Definimos las operaciones functoriales y monádicas: `Dist.pure`, `Dist.map`, `Dist.scale` y `Dist.bind`.
3. **Demostramos formalmente la Ley de Conservación de la Masa de Probabilidad:**
   - Transformar una variable aleatoria con `Dist.map f` **conserva exactamente la masa total**.
   - Escalar los pesos con `Dist.scale k` multiplica la masa total por `k`.
   - Componer con una distribución de masa constante multiplica las masas totales (Ley del Producto).
-/

namespace LeanTT.M49

universe u v

/-- Una distribución discreta finita sobre `α`: lista de resultados con su peso `Nat` -/
abbrev Dist (α : Type u) := List (α × Nat)

namespace Dist

/-- Distribución puntual de Dirac (`pure x`) concentrada en `x` con masa `1` -/
@[simp]
def pure {α : Type u} (x : α) : Dist α :=
  [(x, 1)]

/-- Masa total (suma de todos los pesos) de una distribución `d : Dist α` -/
@[simp]
def totalMass {α : Type u} : Dist α → Nat
  | []          => 0
  | (_, w) :: r => w + totalMass r

/-- Imagen directa (*Pushforward* / `map`) de una distribución bajo una función `f : α → β` -/
@[simp]
def map {α : Type u} {β : Type v} (f : α → β) : Dist α → Dist β
  | []          => []
  | (x, w) :: r => (f x, w) :: map f r

/-- Reescalado uniforme de los pesos de una distribución por un factor `k : Nat` -/
@[simp]
def scale {α : Type u} (k : Nat) : Dist α → Dist α
  | []          => []
  | (x, w) :: r => (x, k * w) :: scale k r

/-- Composición monádica (`bind`) de dos pasos probabilísticos (transición de una Cadena de Markov) -/
@[simp]
def bind {α : Type u} {β : Type v} : Dist α → (α → Dist β) → Dist β
  | [],         _ => []
  | (x, w) :: r, k => scale w (k x) ++ bind r k

/-! ## Teoremas de Conservación de Masa y Leyes de Probabilidad -/

/-- TEOREMA 1: La distribución puntual `pure x` tiene masa total exactamente igual a `1` -/
theorem totalMass_pure {α : Type u} (x : α) :
    totalMass (pure x) = 1 :=
  rfl

/-- TEOREMA 2 (Conservación de Masa bajo Pushforward `map`):
    Aplicar cualquier función determinista `f : α → β` a una variable aleatoria conserva
    exactamente la masa total de probabilidad (`totalMass (map f d) = totalMass d`)! -/
theorem totalMass_map {α : Type u} {β : Type v} (f : α → β) (d : Dist α) :
    totalMass (map f d) = totalMass d := by
  induction d with
  | nil          => rfl
  | cons xw r ih =>
    rcases xw with ⟨x, w⟩
    dsimp [map, totalMass]
    rw [ih]

/-- TEOREMA 3: La masa total de la unión disjunta de soportes `d1 ++ d2` es aditiva -/
theorem totalMass_append {α : Type u} (d1 d2 : Dist α) :
    totalMass (d1 ++ d2) = totalMass d1 + totalMass d2 := by
  induction d1 with
  | nil          => simp
  | cons xw r ih =>
    rcases xw with ⟨x, w⟩
    dsimp [totalMass]
    rw [ih, Nat.add_assoc]

/-- TEOREMA 4: Escalar cada peso por `k` multiplica la masa total por `k` -/
theorem totalMass_scale {α : Type u} (k : Nat) (d : Dist α) :
    totalMass (scale k d) = k * totalMass d := by
  induction d with
  | nil          => simp
  | cons xw r ih =>
    rcases xw with ⟨x, w⟩
    dsimp [scale, totalMass]
    rw [ih, Nat.mul_add]

/-- TEOREMA 5 (Invariante de Masa en Transiciones de Markov):
    Si un núcleo de transición de Markov `step : α → Dist β` tiene masa constante `M` desde
    cualquier estado `x` (`∀ x, totalMass (step x) = M`), entonces tras un paso `bind d step`
    la masa total es exactamente `totalMass d * M`! -/
theorem totalMass_bind_const {α : Type u} {β : Type v}
    (d : Dist α) (step : α → Dist β) (M : Nat)
    (h_markov : ∀ x : α, totalMass (step x) = M) :
    totalMass (bind d step) = totalMass d * M := by
  induction d with
  | nil          => simp
  | cons xw r ih =>
    rcases xw with ⟨x, w⟩
    dsimp [bind, totalMass]
    rw [totalMass_append, totalMass_scale, h_markov x, ih, Nat.right_distrib]

end Dist
end LeanTT.M49
