# Módulo 06: Igualdad Definicional vs. Proposicional, Transporte ($J$) y Tipos Cociente

> **Archivo Lean ejecutable asociado:** [`LeanTT/M06_EqualityAndTransport.lean`](../LeanTT/M06_EqualityAndTransport.lean)

---

## 1. Las Dos Nociones de Igualdad en Teoría de Tipos Intensional

En la Teoría de Tipos Intensional (como MLTT y Lean 4), es crucial distinguir entre:

### 1.1 Igualdad Definicional (o de Juicio / Computacional): $a \equiv b$
Es una relación **metateórica** decidida algorítmicamente por el kernel mediante reducción ($\beta, \eta, \delta, \iota, \zeta$) e irrelevancia de prueba.
* Si $a \equiv b$, entonces para cualquier familia $P : \alpha \to \texttt{Sort } u$, los tipos $P(a)$ y $P(b)$ son **idénticos** para el verificador de tipos.
* Ejemplo: `n + 0` es definicionalmente igual a `n` porque `Nat.add` se define por recursión sobre su **segundo** argumento.

### 1.2 Igualdad Proposicional (Tipo Identidad de Martin-Löf): `a = b` (`Eq a b`)
Es un **tipo interno** del lenguaje (`a = b : Prop`) que puede ser habitado por un término de prueba $h : a = b$.
* Ejemplo: `0 + n = n` **no** es definicionalmente cierto para una variable libre `n` (porque `0 + n` no puede $\iota$-reducirse hasta conocer qué constructor tiene `n`), pero es **proposicionalmente demostrable** por inducción sobre `n`.

---

## 2. El Tipo Identidad `Eq` y el Eliminador $J$ (`Eq.rec`)

La definición completa de la igualdad en la librería núcleo de Lean 4 ocupa apenas dos líneas:

```lean
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
```

Observa su estructura como familia inductiva:
* `a : α` es un **parámetro** fijo.
* El segundo argumento `: α → Prop` es un **índice** libre.
* El único constructor `Eq.refl` (o `rfl`) exige que el índice coincida con el parámetro `a`.

### El Principio de Inducción sobre la Igualdad (Regla $J$ de Martin-Löf)
El eliminador generado por el kernel es:

```lean
Eq.rec :
  {α : Sort u} → {a : α} →
  {motive : (x : α) → a = x → Sort v} →
  motive a (Eq.refl a) →
  {b : α} → (h : a = b) → motive b h
```

En palabras: **para demostrar una propiedad `motive b h` sobre dos elementos iguales `a = b` y su prueba `h`, basta con demostrarla para el caso reflexivo `b := a` y `h := rfl`**.

De este único principio emanan:
* La **simetría** ($x = y \to y = x$).
* La **transitividad** ($x = y \to y = z \to x = z$).
* La **congruencia** ($x = y \to f(x) = f(y)$).
* El **transporte dependiente** (`h ▸ px : P y` dado `px : P x` y `h : x = y`).

---

## 3. Transporte sobre Fibraciones y el "Infierno Dependiente" (`HEq`)

Si tienes un vector `v : Vec α n` y una igualdad `h : n = m`, entonces `v` **no tiene tipo** `Vec α m` directamente (a menos que $n \equiv m$). Para cambiar su tipo debes **transportarlo** a lo largo de la fibra `Vec α`:

$$\text{transport}(\texttt{Vec }\alpha, h, v) : \texttt{Vec }\alpha\; m \qquad (\text{escrito } \texttt{h ▸ v} \text{ en Lean 4})$$

Cuando necesitamos comparar términos $a : \alpha$ y $b : \beta$ cuyos tipos $\alpha$ y $\beta$ son proposicionalmente iguales ($\alpha = \beta$) pero no definicionalmente iguales, usamos la **Igualdad Heterogénea (de John Major)**:

```lean
inductive HEq {α : Sort u} (a : α) : {β : Sort u} → β → Prop where
  | refl : HEq a a
```
Notación infija: `a ≍ b`.

---

## 4. Extensionalidad y Tipos Cociente en Lean 4

El cálculo lambda puro es **intensional**: dos funciones `f g : Nat → Nat` tales que `∀ x, f x = g x` (por ejemplo, `fun x => x + 0` y `fun x => 0 + x`) no tienen el mismo cuerpo sintáctico y no son definicionalmente iguales.

Para que la matemática formal sea ergonómica, el kernel de Lean incluye como primitivos los **Tipos Cociente (`Quot`)** y el axioma de **Extensionalidad Proposicional (`propext`)**:

1. **`propext`:** $\forall (P\; Q : \texttt{Prop}),\, (P \leftrightarrow Q) \to P = Q$. Dos proposiciones lógicamente equivalentes son iguales.
2. **`Quot`:** Dado un tipo $\alpha$ y una relación $r : \alpha \to \alpha \to \texttt{Prop}$, forma el tipo cociente $\texttt{Quot } r$ donde `Quot.sound : r a b → Quot.mk r a = Quot.mk r b`.
3. **`funext` (Teorema en Lean):** A partir de `Quot`, Lean **demuestra** la **Extensionalidad Funcional**:
   $$(\forall x : \alpha,\, f(x) = g(x)) \longrightarrow f = g$$

---

## 5. Lean 4 (UIP / Axioma $K$) vs. Teoría de Tipos Homotópica (HoTT)

| Característica | Lean 4 (CIC con `Prop`) | HoTT / Cubical Type Theory (Agda `--cubical`) |
| :--- | :--- | :--- |
| Universo de `x = y` | `Prop` (`Sort 0`) | `Type u` (el mismo universo que `x` e `y`) |
| **UIP (Unicidad de Pruebas de Identidad)** | **Sí (`rfl`)**: todas las pruebas `p, q : x = y` son idénticas | **No**: un tipo se interpreta como un $\infty$-grupoide espacial; `x = y` es el espacio de caminos |
| **Axioma de Univalencia** $(\alpha \simeq \beta) \simeq (\alpha = \beta)$ | **Incompatible con UIP** (en `Type`) | **Válido** (los tipos isomorfos son iguales) |
| **Cocientes efectivos (`Quot`)** | Primitivos en el kernel con reducción computacional en `Quot.lift` | Construidos como *Higher Inductive Types* (HITs) |
