/-!
# Módulo 14 (Especialmente Didáctico): Tu Primera Demostración Paso a Paso
## Cómo Pensar en Lean 4 viendo el Estado del Infoview en Cada Línea

Este módulo está diseñado como un **laboratorio guiado ultra-didáctico**.
En cada demostración hemos anotado en comentarios **exactamente qué aparece en el
panel Lean Infoview (`Contexto Γ ⊢ Meta`) antes y después de cada línea**.

### Regla Mental Fundamental:
Siempre tienes dos preguntas ante cualquier estado `Γ ⊢ Meta`:
1. **Mirar la `Meta` (abajo de `⊢`):** ¿Qué forma tiene lo que quiero demostrar?
   - Si es `A → B` o `∀ x, P x`  👉 usa **`intro`**
   - Si es `A ∧ B` o `A ↔ B`     👉 usa **`constructor`**
   - Si es `A ∨ B`               👉 usa **`left`** o **`right`**
   - Si es `∃ x, P x`            👉 usa **`exists testigo`** (o `⟨testigo, prueba⟩`)
   - Si ambos lados son iguales por cálculo 👉 usa **`rfl`**
2. **Mirar las Hipótesis `Γ` (arriba de `⊢`):** ¿Cómo uso lo que ya sé?
   - Si tengo `h : A ∧ B`        👉 usa **`rcases h with ⟨ha, hb⟩`** (o `h.left`, `h.right`)
   - Si tengo `h : A ∨ B`        👉 usa **`rcases h with ha | hb`** (divide la prueba en 2 casos)
   - Si tengo `h : a = b`        👉 usa **`rw [h]`** (reemplaza `a` por `b` en la meta)
   - Si tengo `h : A → B` y mi meta es `B` 👉 usa **`apply h`** (la meta pasa a ser `A`)
-/

namespace LeanTT.M14

variable (P Q R : Prop)

/-! ## Lección 1: `intro` y `exact` (Navegando Implicaciones `→`) -/

theorem leccion1_implicacion : P → (Q → P) := by
  -- ESTADO INICIAL DEL INFOVIEW:
  -- P Q : Prop
  -- ⊢ P → (Q → P)
  --
  -- Como la meta es una flecha `P → ...`, usamos `intro hp` para asumir `P`:
  intro hp
  -- ESTADO TRAS `intro hp`:
  -- P Q : Prop
  -- hp : P
  -- ⊢ Q → P
  --
  -- La meta sigue siendo una flecha `Q → P`, así que usamos `intro hq`:
  intro _hq
  -- ESTADO TRAS `intro _hq`:
  -- P Q : Prop
  -- hp : P
  -- _hq : Q
  -- ⊢ P
  --
  -- ¡Ahora la meta `P` coincide exactamente con nuestra hipótesis `hp`!
  exact hp
  -- ¡No goals! Demostración completada.

/-! ## Lección 2: `apply` (Razonamiento Hacia Atrás) vs `have` (Razonamiento Hacia Adelante) -/

/-- Enfoque A: Razonamiento hacia atrás con `apply` -/
theorem leccion2_hacia_atras (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
  -- Meta inicial: ⊢ R
  -- Sabemos que `hqr : Q → R` produce `R` si le damos `Q`. Aplicamos `hqr`:
  apply hqr
  -- Nueva meta: ⊢ Q
  -- Sabemos que `hpq : P → Q` produce `Q` si le damos `P`. Aplicamos `hpq`:
  apply hpq
  -- Nueva meta: ⊢ P
  -- Y `P` ya lo tenemos en la hipótesis `hp`:
  exact hp

/-- Enfoque B: Razonamiento hacia adelante con `have` (como se escribe en un libro de texto) -/
theorem leccion2_hacia_adelante (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
  -- Paso 1: Como tenemos `hp : P` y `hpq : P → Q`, deducimos `hq : Q`:
  have hq : Q := hpq hp
  -- Paso 2: Como ahora tenemos `hq : Q` y `hqr : Q → R`, deducimos `hr : R`:
  have hr : R := hqr hq
  -- Paso 3: Concluimos con `hr`:
  exact hr

/-! ## Lección 3: `constructor` y `rcases` (Armando y Desarmando `∧` y `∨`) -/

theorem leccion3_conjuncion_y_disyuncion : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  -- 1. Asumimos el antecedente `h : P ∧ (Q ∨ R)`:
  intro h
  -- 2. Desarmamos la conjunción `h` en `hp : P` y `hqr : Q ∨ R`:
  rcases h with ⟨hp, hqr⟩
  -- 3. Como `hqr : Q ∨ R` es una disyunción, abrimos dos casos:
  rcases hqr with hq | hr
  · -- CASO 1: Sabemos `hq : Q`. Queremos probar `(P ∧ Q) ∨ (P ∧ R)`.
    -- Elegimos el lado izquierdo con `left`:
    left
    -- Meta: ⊢ P ∧ Q. Como es una conjunción, usamos `constructor` para abrir 2 submetas:
    constructor
    · exact hp -- Submeta 1: ⊢ P
    · exact hq -- Submeta 2: ⊢ Q
  · -- CASO 2: Sabemos `hr : R`. Queremos probar `(P ∧ Q) ∨ (P ∧ R)`.
    -- Elegimos el lado derecho con `right`:
    right
    -- Meta: ⊢ P ∧ R. Usamos `constructor`:
    constructor
    · exact hp -- Submeta 1: ⊢ P
    · exact hr -- Submeta 2: ⊢ R

/-! ## Lección 4: `rw` (Reescritura Ecuacional Paso a Paso) -/

theorem leccion4_reescritura (a b c d : Nat) (h1 : a = b + c) (h2 : b = d) (h3 : c = 0) :
    a = d := by
  -- Meta inicial: ⊢ a = d
  -- 1. `rw [h1]` reemplaza `a` por `b + c`:
  rw [h1]
  -- Meta ahora:   ⊢ b + c = d
  -- 2. `rw [h2]` reemplaza `b` por `d`:
  rw [h2]
  -- Meta ahora:   ⊢ d + c = d
  -- 3. `rw [h3]` reemplaza `c` por `0`:
  rw [h3]
  -- Meta ahora:   ⊢ d + 0 = d
  -- 4. `d + 0 = d` es verdadero por definición de la suma (`Nat.add_zero` o `rfl`):
  rfl

/-! ## Lección 5: `induction` Explicada Paso a Paso -/

/-- Definimos nuestra propia función que duplica cada elemento de una lista -/
def duplicarElementos {α : Type} : List α → List α
  | []      => []
  | x :: xs => x :: x :: duplicarElementos xs

#eval duplicarElementos [1, 2, 3] -- [1, 1, 2, 2, 3, 3]

/-- Demostramos por inducción que `duplicarElementos xs` tiene el doble de longitud que `xs` -/
theorem length_duplicarElementos {α : Type} (xs : List α) :
    (duplicarElementos xs).length = 2 * xs.length := by
  induction xs with
  | nil =>
    -- CASO BASE (`xs = []`):
    -- Meta: ⊢ (duplicarElementos []).length = 2 * [].length
    -- Ambos lados valen `0` por definición:
    rfl
  | cons x tail ih =>
    -- PASO INDUCTIVO (`xs = x :: tail`):
    -- Hipótesis inductiva `ih`: (duplicarElementos tail).length = 2 * tail.length
    -- Meta: ⊢ (duplicarElementos (x :: tail)).length = 2 * (x :: tail).length
    simp [duplicarElementos, ih]
    omega

end LeanTT.M14
