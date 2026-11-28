# Módulo 06: El Tipo Identidad de Martin-Löf, Eliminador $J$, Transporte sobre Fibraciones, `HEq` y HoTT

> **Archivo Lean ejecutable asociado:** [`LeanTT/M06_EqualityAndTransport.lean`](../LeanTT/M06_EqualityAndTransport.lean)

---

## Índice del Módulo
1. [Igualdad Intensional vs. Igualdad Extensional en Teoría de Tipos](#1-igualdad-intensional-vs-igualdad-extensional-en-teoría-de-tipos)
2. [El Eliminador $J$ (`Eq.rec`): Cómo Funciona la Inducción sobre Caminos](#2-el-eliminador-j-eqrec-cómo-funciona-la-inducción-sobre-caminos)
3. [Transporte Dependiente (`▸`) y Concatenación de Vectores Paso a Paso](#3-transporte-dependiente--y-concatenación-de-vectores-paso-a-paso)
4. [El Error Clásico `"motive is not type correct"` y Cómo Resolverlo](#4-el-error-clásico-motive-is-not-type-correct-y-cómo-resolverlo)
5. [Igualdad Heterogénea de John Major (`HEq` / `≍`) y `cast`](#5-igualdad-heterogénea-de-john-major-heq--y-cast)
6. [Estructura de $\infty$-Grupoide del Tipo Identidad, UIP y Comparación con HoTT](#6-estructura-de-infty-grupoide-del-tipo-identidad-uip-y-comparación-con-hott)
7. [Tipos Cociente (`Quot` y `Quotient`) en el Kernel de Lean 4](#7-tipos-cociente-quot-y-quotient-en-el-kernel-de-lean-4)

---

## 1. Igualdad Intensional vs. Igualdad Extensional en Teoría de Tipos

En el diseño de asistentes de demostraciones con tipos dependientes existe una bifurcación fundamental:

* **Teoría de Tipos Extensional (NuPRL):** Incluye la regla de reflexión de la igualdad: si existe una prueba proposicional $h : a = b$, entonces $a$ y $b$ se consideran definicionalmente iguales ($a \equiv b$).
  * *Precio a pagar:* **La verificación de tipos se vuelve indecidible** (comprobar si un término está bien tipado requiere demostrar teoremas arbitrarios).
* **Teoría de Tipos Intensional (Lean 4, Coq, Agda):** Separa estrictamente:
  1. **La igualdad definicional $a \equiv b$:** Decidible algorítmicamente mediante reducción a forma normal.
  2. **La igualdad proposicional `a = b` (`Eq a b`):** Un tipo cuyos habitantes son pruebas explícitas que deben aplicarse mediante transporte (`Eq.rec` / `rw`) cuando queremos cambiar el índice de un tipo dependiente.

### Ejemplo 1.1: Por qué `n + 0 = n` es Definicional pero `0 + n = n` es Proposicional
En la librería estándar de Lean 4, `Nat.add` se define por recursión estructural sobre su **segundo** argumento:
```lean
-- Definición interna de `Nat.add`:
-- Nat.add n 0       := n
-- Nat.add n (m + 1) := Nat.succ (Nat.add n m)

-- Por tanto, `n + 0` se reduce por ι-reducción a `n` inmediatamente:
example (n : Nat) : n + 0 = n := rfl

-- En cambio, en `0 + n`, el segundo argumento es una variable libre `n` (no un constructor),
-- por lo que la ι-reducción se detiene. Para demostrar `0 + n = n` necesitamos inducción:
theorem zero_add_prop (n : Nat) : 0 + n = n := by
  induction n with
  | zero      => rfl
  | succ k ih => exact congrArg Nat.succ ih
```

---

## 2. El Eliminador $J$ (`Eq.rec`): Cómo Funciona la Inducción sobre Caminos

Recordemos la definición del tipo identidad:
```lean
namespace PreludioEq
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
end PreludioEq
```
Y su eliminador (regla $J$ de Paulin-Mohring):
```text
Eq.rec :
  {α : Sort u} → {a : α} →
  {motive : (b : α) → a = b → Sort v} →
  motive a (Eq.refl a) →
  {b : α} → (h : a = b) → motive b h
```

### ¿Cómo se construye el motivo `motive` en la práctica?
Cuando quieres usar una igualdad `h : a = b` para transformar un objetivo $G(b)$ en $G(a)$:
1. Abstraes las apariciones de `b` en el objetivo mediante una función $\lambda x.\, G(x)$: ese es tu **motivo** (`motive`).
2. Demuestras el caso base para `x := a` (es decir, $G(a)$).
3. `Eq.rec` transporta tu prueba de $G(a)$ a una prueba de $G(b)$.

---

## 3. Transporte Dependiente (`▸`) y Concatenación de Vectores Paso a Paso

En Lean 4, la macro `h ▸ term` (se escribe `\t`) invoca a `Eq.rec` inferiendo el motivo automáticamente.

Veamos cómo funciona al concatenar dos vectores `xs : Vec α m` e `ys : Vec α n`:
* En el caso base `xs = Vec.nil`, tenemos $m = 0$ e `ys : Vec α n`, pero el tipo de retorno esperado es `Vec α (0 + n)`.
* Como `0 + n` es definicionalmente igual a `n` si `Nat.add` recurriera sobre el primer argumento, pero en Lean 4 recurre sobre el segundo argumento, `0 + n` **no** es definicionalmente igual a `n`.
* Necesitamos transportar `ys : Vec α n` a lo largo de la igualdad `Nat.zero_add n : 0 + n = n` (invertida):

```lean
namespace DemoTransporte

inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n + 1)

def Vec.append {α : Type u} {m n : Nat} : Vec α m → Vec α n → Vec α (m + n)
  | .nil,       ys => (Nat.zero_add n).symm ▸ ys
  | .cons x xs, ys => (Nat.succ_add _ n).symm ▸ .cons x (Vec.append xs ys)

end DemoTransporte
```

---

## 4. El Error Clásico `"motive is not type correct"` y Cómo Resolverlo

Uno de los errores más frecuentes al iniciarse en la teoría de tipos dependientes en Lean es intentar usar `rw [h]` sobre una variable `n` cuando **en el contexto o en la meta hay otro término cuyo tipo depende de `n`**.

### ¿Por qué ocurre `"motive is not type correct"`?
Supongamos que tienes `v : Vec α n` y una igualdad `h : n = m`, y tu meta es una propiedad `P n v` donde `P : (k : Nat) → Vec α k → Prop`.
Si intentas hacer `rw [h]` para reemplazar solo `n` por `m` en `P n v`, Lean intenta construir el motivo:

$$\text{motive}(x) := P\; x\; v$$

¡Pero para una variable genérica $x : \texttt{Nat}$, la expresión $P\; x\; v$ **está mal tipada** porque $P\; x$ espera un vector de tipo `Vec α x`, mientras que `v` sigue teniendo el tipo fijo `Vec α n`!

### Las 3 Soluciones Canónicas en Lean 4

1. **Generalizar o revertir el término dependiente junto con su prueba antes de hacer `cases h` o `subst h`:**
   Si `h : n = m` donde `m` o `n` es una variable libre, la táctica **`subst h`** (o **`cases h`**) elimina simultáneamente la variable `m` en `v` y en todo el contexto sin construir un motivo mal tipado:
   ```lean
   open DemoTransporte

   theorem resolver_con_subst {α : Type} {n m : Nat}
       (P : (k : Nat) → Vec α k → Prop)
       (v : Vec α n) (h : n = m) (hp : P n v) :
       P m (h ▸ v) := by
     subst h
     -- Tras `subst h`, `m` desaparece y `h` se convierte en `rfl`,
     -- por lo que `rfl ▸ v` se reduce definicionalmente a `v`!
     exact hp
   ```
2. **Incluir el término dependiente dentro del motivo cuantificando sobre él:**
   En lugar de reescribir con `v : Vec α n` fijo en el contexto, haz `revert v` para que la meta sea `∀ v : Vec α n, ...`; ahora el motivo `fun x => ∀ v : Vec α x, ...` **sí está bien tipado** para cualquier `x`!
3. **Usar Igualdad Heterogénea (`HEq` / `≍`):** Cuando queremos razonar ecuacionalmente sobre términos de tipos distintos `Vec α n` y `Vec α m`.

---

## 5. Igualdad Heterogénea de John Major (`HEq` / `≍`) y `cast`

Introducida por Conor McBride (1999), la igualdad heterogénea `HEq a b` (escrita `a ≍ b`) permite afirmar que $a : \alpha$ y $b : \beta$ son iguales aunque sus tipos $\alpha$ y $\beta$ no sean definicionalmente iguales:

```lean
namespace PreludioHEq
inductive HEq {α : Sort u} (a : α) : {β : Sort u} → β → Prop where
  | refl : HEq a a
end PreludioHEq
```

Propiedades clave en Lean 4:
* `heq_of_eq : a = b → a ≍ b`
* **`eq_of_heq : (h : a ≍ b) → a = b`** *(cuando `a` y `b` ya tienen el mismo tipo $\alpha$, gracias a UIP)*
* **`cast : (h : α = β) → α → β`**: Transporta un término de tipo $\alpha$ al tipo $\beta$, cumpliendo `cast_heq : ∀ (h : α = β) (a : α), cast h a ≍ a`.

```lean
-- Ejemplo: `cast h a` es heterogéneamente igual a `a` para cualquier `h : α = β`:
example {α β : Type} (h : α = β) (a : α) : cast h a ≍ a := by
  subst h
  rfl
```

---

## 6. Estructura de $\infty$-Grupoide del Tipo Identidad, UIP y Comparación con HoTT

En cualquier teoría de tipos dependientes (incluso sin UIP), los tipos identidad dotan a cada tipo $\alpha$ de la estructura de un **grupoide débil**:
* **Objetos:** Los puntos $x, y, z : \alpha$.
* **1-Morfismos (Caminos):** Las pruebas de igualdad $p : x = y$.
* **Identidad:** El camino constante `rfl : x = x`.
* **Composición de caminos:** La transitividad `Eq.trans p q : x = z`.
* **Inverso de un camino:** La simetría `Eq.symm p : y = x`.
* **2-Morfismos (Homotopías entre caminos):** Las pruebas de igualdad entre pruebas de igualdad $\gamma : p = q$ (donde $p, q : x = y$).

### La Divergencia entre Lean 4 (CIC) y HoTT (Voevodsky)
* **En Lean 4:** Como `Eq a b : Prop`, la irrelevancia de prueba colapsa todos los 2-morfismos ($\forall (p\; q : x = y),\, p = q$ por `rfl`). Cada tipo es un **0-tipo (conjunto discreto de caminos)**. Esto hace que el trabajo con subtipos, cocientes y estructuras algebraicas clásicas sea extraordinariamente directo.
* **En HoTT (Homotopy Type Theory):** El tipo identidad vive en `Type u` y **no** se asume UIP. El **Axioma de Univalencia** de Voevodsky postula que el tipo de caminos $(A =_{\texttt{Type}} B)$ es equivalente al tipo de equivalencias homotópicas $(A \simeq B)$. En particular, como existen dos automorfismos de `Bool` (`id` y `not`), en HoTT existen **dos pruebas distintas** de `Bool = Bool`, lo cual contradiría UIP.
