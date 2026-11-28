# Módulo 03: Jerarquía de Universos (`Sort u`), la Paradoja de Girard, Impredicatividad y Subsingletons

> **Archivo Lean ejecutable asociado:** [`LeanTT/M03_UniversesAndProp.lean`](../LeanTT/M03_UniversesAndProp.lean)

---

## Índice del Módulo
1. [Historia del Problema: De Russell a `Type : Type` y la Paradoja de Girard](#1-historia-del-problema-de-russell-a-type--type-y-la-paradoja-de-girard)
2. [Anatomía Completa de los Niveles de Universo (`Level`) en Lean 4](#2-anatomía-completa-de-los-niveles-de-universo-level-en-lean-4)
3. [ElÁlgebra de `max` e `imax` en los Tipos Producto Dependiente](#3-el-álgebra-de-max-e-imax-en-los-tipos-producto-dependiente)
4. [Polimorfismo de Universos en la Práctica (`universe u v` y `.{u, v}`)](#4-polimorfismo-de-universos-en-la-práctica-universe-u-v-y-u-v)
5. [La Distinción Fundamental entre `Prop` (`Sort 0`) y `Type u` (`Sort (u+1)`)](#5-la-distinción-fundamental-entre-prop-sort-0-y-type-u-sort-u1)
6. [Eliminación de Subsingletons: ¿Cuándo Podemos Extraer Datos de `Prop`?](#6-eliminación-de-subsingletons-cuándo-podemos-extraer-datos-de-prop)
7. [Elevación Explícita de Universos: `ULift` y `PLift`](#7-elevación-explícita-de-universos-ulift-y-plift)

---

## 1. Historia del Problema: De Russell a `Type : Type` y la Paradoja de Girard

En su primera formulación de la Teoría de Tipos Intuicionista (1971), Per Martin-Löf incluyó el axioma:

$$\texttt{Type} : \texttt{Type}$$

Poco después, **Jean-Yves Girard** (1972) demostró que su sistema $U^-$ (que permite cuantificación polimórfica en dos niveles sin estratificación adecuada) es inconsistente: permite codificar la **Paradoja de Burali-Forti** (el ordinal de todos los ordinales bien ordenados es estrictamente mayor que sí mismo). En 1986, Meyer y Reinhold simplificaron el argumento (la **Paradoja de Hurkens**, 1995, es hoy la versión más corta) mostrando que en cualquier sistema con $\texttt{Type} : \texttt{Type}$ se puede construir un término cerrado de tipo $\bot$ (`False`) que no termina al reducirse.

### ¿Cómo evita Lean la Paradoja de Hurkens / Girard?
Si intentas cuantificar sobre un universo $\mathcal{U}$ para definir un nuevo tipo de datos, el tipo resultante debe vivir en un universo **estrictamente mayor** $\mathcal{U}+1$ (predicatividad), **salvo** en el universo inferior `Prop` (`Sort 0`), donde la impredicatividad es consistente **únicamente porque no puedes extraer testigos computacionales arbitrarios de `Prop` hacia `Type`**.

---

## 2. Anatomía Completa de los Niveles de Universo (`Level`) en Lean 4

En el kernel de Lean 4 (`Lean.Level`), los niveles de universo se construyen inductivamente mediante cuatro constructores:

```text
inductive Level where
  | zero   : Level                   -- 0
  | succ   : Level → Level           -- u + 1
  | max    : Level → Level → Level   -- max u v
  | imax   : Level → Level → Level   -- imax u v
  | param  : Name → Level            -- variable polimórfica de universo `u`, `v`
  | mvar   : LMVarId → Level         -- metavariable de nivel durante la elaboración
```

Y para cada nivel $u$, existe el universo `Sort u`:

$$
\begin{array}{ccccccc}
\texttt{Sort 0} & : & \texttt{Sort 1} & : & \texttt{Sort 2} & : & \texttt{Sort 3} & \dots \\
\parallel & & \parallel & & \parallel & & \parallel \\
\texttt{Prop} & : & \texttt{Type 0} & : & \texttt{Type 1} & : & \texttt{Type 2} & \dots
\end{array}
$$

---

## 3. El Álgebra de `max` e `imax` en los Tipos Producto Dependiente

Cuando formas el tipo función o producto dependiente $(x : A) \to B(x)$ donde:
* $A : \texttt{Sort } u$
* $x : A \vdash B(x) : \texttt{Sort } v$

el tipo del producto dependiente es:

$$(x : A) \to B(x) : \texttt{Sort }(\text{imax}(u, v))$$

donde:
$$\text{imax}(u, 0) = 0, \qquad \text{imax}(u, v + 1) = \max(u, v + 1)$$

### Tabla Completa de Ejemplos de Universos de $\Pi$-Types en Lean 4

| Dominio $A$ (`Sort u`) | Codominio $B(x)$ (`Sort v`) | Cálculo de $\text{imax}(u, v)$ | Universo de $(x : A) \to B(x)$ | Ejemplo en Lean 4 |
| :--- | :--- | :---: | :--- | :--- |
| `Prop` (`Sort 0`) | `Prop` (`Sort 0`) | $\text{imax}(0, 0) = 0$ | `Prop` (`Sort 0`) | `P → Q : Prop` |
| `Nat : Type 0` (`Sort 1`) | `Prop` (`Sort 0`) | $\text{imax}(1, 0) = 0$ | `Prop` (`Sort 0`) | `∀ n : Nat, n = n : Prop` |
| `Type 0` (`Sort 2`) | `Prop` (`Sort 0`) | $\text{imax}(2, 0) = 0$ | `Prop` (`Sort 0`) | `∀ α : Type, Nonempty α : Prop` |
| `Prop` (`Sort 0`) | `Nat : Type 0` (`Sort 1`) | $\text{imax}(0, 1) = 1$ | `Type 0` (`Sort 1`) | `(0 = 0) → Nat : Type 0` |
| `Nat : Type 0` (`Sort 1`) | `Type 0` (`Sort 2`) | $\text{imax}(1, 2) = 2$ | `Type 1` (`Sort 2`) | `Nat → Type 0 : Type 1` |
| `Type 0` (`Sort 2`) | `α : Type 0` (`Sort 1`) | $\text{imax}(2, 1) = 2$ | `Type 1` (`Sort 2`) | `(α : Type 0) → α : Type 1` |

```lean
-- Comprobación interactiva en Lean 4 de las 6 filas de la tabla:
#check (True → False : Prop)
#check (∀ n : Nat, n + 0 = n : Prop)
#check (∀ α : Type 0, ∀ x : α, x = x : Prop)
#check ((1 = 1) → Nat : Type 0)
#check (Nat → Type 0 : Type 1)
#check ((α : Type 0) → α → α : Type 1)
```

---

## 4. Polimorfismo de Universos en la Práctica (`universe u v` y `.{u, v}`)

Si definieras `Lista` fijándola únicamente para `α : Type 0`:
```text
inductive ListaFija (α : Type 0) : Type 0 where ...
```
no podrías construir una `ListaFija (Type 0)` porque `Type 0` vive en `Type 1`.

Para evitar duplicar definiciones en cada piso de la jerarquía, Lean 4 permite parametrizar cualquier definición, estructura o tipo inductivo por **variables de nivel de universo**:

```lean
universe u v

inductive MiLista (α : Type u) : Type u where
  | nil  : MiLista α
  | cons : α → MiLista α → MiLista α

-- Ahora podemos instanciar `MiLista` en cualquier nivel explícita o implícitamente:
#check MiLista.{0} Nat      -- MiLista Nat : Type 0
#check MiLista.{1} (Type 0) -- MiLista Type : Type 1
#check MiLista.{2} (Type 1) -- MiLista (Type 1) : Type 2
```

> **Tip en Lean 4:** Si tienes `set_option autoImplicit true` (el valor por defecto), incluso puedes escribir `Type u` directamente en la firma sin declarar `universe u` antes, y Lean añadirá el parámetro de universo automáticamente.

---

## 5. La Distinción Fundamental entre `Prop` (`Sort 0`) y `Type u` (`Sort (u+1)`)

| Propiedad | `Prop` (`Sort 0`) | `Type u` (`Sort (u+1)`) |
| :--- | :--- | :--- |
| **Propósito** | Proposiciones lógicas y especificaciones | Estructuras de datos y programas ejecutables |
| **Cuantificación universal** | **Impredicativa**: `(∀ α : Type u, P α) : Prop` | **Predicativa**: `((α : Type u) → F α) : Type (max (u+1) v)` |
| **Igualdad de habitantes** | **Proof Irrelevance**: si $p, q : P$, entonces $p \equiv q$ (`rfl`) | **Proof Relevance**: `true` y `false` en `Bool` son distintos |
| **Representación en compilación** | **Borrado total** (se reemplaza por una constante irrelavante en la IR) | Representados en memoria (enteros, punteros con RC, closures) |
| **Eliminación hacia `Type v`** | **Restringida** a *subsingletons* | **Sin restricción** (puedes hacer `match` libremente hacia cualquier universo) |

---

## 6. Eliminación de Subsingletons: ¿Cuándo Podemos Extraer Datos de `Prop`?

Veamos con ejemplos concretos en Lean 4 qué ocurre cuando intentamos hacer reconocimiento de patrones (`match`) sobre una proposición $h : P$ (con $P : \texttt{Prop}$) para devolver un dato en `Type` (por ejemplo, un `Nat` o un `Bool`):

### 6.1 Caso Prohibido 1: Disyunción `P ∨ Q` (Tiene 2 Constructores)
```lean
-- ❌ ERROR DE COMPILACIÓN:
-- tactic 'cases' failed, nested error:
-- recursor 'Or.casesOn' can only eliminate into Prop
/-
def queLadoGano {P Q : Prop} (h : P ∨ Q) : Bool :=
  match h with
  | Or.inl _ => true
  | Or.inr _ => false
-/
```
**¿Por qué falla?** Supongamos que $P = \texttt{True}$ y $Q = \texttt{True}$. Entonces `Or.inl trivial` y `Or.inr trivial` son dos habitantes de `True ∨ True : Prop`. Por irrelevancia de prueba, `Or.inl trivial = Or.inr trivial`. Si `queLadoGano` estuviera permitida, tendríamos `true = queLadoGano (Or.inl trivial) = queLadoGano (Or.inr trivial) = false`, contradicción.

**Solución constructiva:** Si necesitas decidir en tiempo de ejecución cuál de los dos casos se cumple, usa el coproducto en `Type` (`Sum P Q` o `PSum P Q`), o exige `[Decidable P]`:
```lean
def queLadoGanoDecidable {P Q : Prop} [Decidable P] (_ : P ∨ Q) : Bool :=
  if P then true else false
```

### 6.2 Caso Prohibido 2: Existencial `∃ x : Nat, P x` (El testigo `x` es un dato en `Type`)
```lean
-- ❌ ERROR DE COMPILACIÓN:
-- recursor 'Exists.casesOn' can only eliminate into Prop
/-
def extraerTestigo {P : Nat → Prop} (h : ∃ x : Nat, P x) : Nat :=
  match h with
  | ⟨x, _⟩ => x
-/
```
**Solución constructiva:** Empaqueta el testigo usando `Subtype` (`{ x : Nat // P x }`) o `Sigma` (`(x : Nat) × P x`), que viven en `Type`:
```lean
def extraerTestigoSubtype {P : Nat → Prop} (h : { x : Nat // P x }) : Nat :=
  h.val
```

### 6.3 Casos Permitidos (Subsingletons Sintácticos en `Prop`)
Un tipo inductivo en `Prop` **sí** puede eliminarse hacia `Type` si tiene 0 o 1 constructor y sus argumentos son proposiciones o índices fijos:
* **`False` (0 constructores):** `False.elim : False → α` para cualquier `α : Sort u`.
* **`True` (1 constructor sin campos):** `True.rec`.
* **`And P Q` (1 constructor cuyos dos campos están en `Prop`):** Puedes extraer `h.1` y `h.2` dentro de una función que devuelve en `Type`.
* **`Eq a b` (1 constructor `Eq.refl` donde `b` es un índice):** ¡Esto es lo que permite que el **transporte de tipos** `Eq.rec` funcione sobre tipos en `Type u`!
* **`Acc r x` (Accesibilidad para recursión bien fundada):** Aunque `Acc r x : Prop`, tiene un único constructor `Acc.intro (x : α) (h : ∀ y, r y x → Acc r y)` cuyo único argumento libre es una proposición en `Prop` (gracias a la impredicatividad de $\forall$). ¡Esto permite que `WellFounded.fix` compute valores en `Type u`!

---

## 7. Elevación Explícita de Universos: `ULift` y `PLift`

1. **`ULift.{r, s} (α : Type s) : Type (max s r)`:** Eleva un tipo de datos de `Type s` a un universo superior envolviéndolo en `structure ULift (α : Type s) : Type (max s r) where up :: (down : α)`.
2. **`PLift (α : Sort u) : Type u`:** Permite elevar incluso una proposición `P : Prop` (`Sort 0`) al universo de datos `Type 0` (`Sort 1`) cuando una estructura de datos polimórfica solo acepta `Type u` y no `Sort u`:

```lean
-- Una lista de pruebas de `1 = 1` elevada a `Type 0` mediante `PLift`:
def listaDePruebas : List (PLift (1 = 1)) :=
  [PLift.up rfl, PLift.up rfl]
```
