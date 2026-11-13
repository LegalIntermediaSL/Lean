# Módulo 04: El Isomorfismo de Curry-Howard — Lógica Intuicionista, Traducción de Gödel-Gentzen y el Teorema de Diaconescu

> **Archivo Lean ejecutable asociado:** [`LeanTT/M04_CurryHoward.lean`](../LeanTT/M04_CurryHoward.lean)

---

## Índice del Módulo
1. [La Trinidad de Curry-Howard-Lambek (Lógica, Tipos y Categorías)](#1-la-trinidad-de-curry-howard-lambek-lógica-tipos-y-categorías)
2. [Las Conectivas Proposicionales como Tipos Inductivos en Lean 4](#2-las-conectivas-proposicionales-como-tipos-inductivos-en-lean-4)
3. [Cuantificadores como $\Pi$-Types y $\Sigma$-Types en `Prop`](#3-cuantificadores-como-pi-types-y-sigma-types-en-prop)
4. [Semántica de Brouwer-Heyting-Kolmogorov (BHK) y Lógica Constructiva](#4-semántica-de-brouwer-heyting-kolmogorov-bhk-y-lógica-constructiva)
5. [La Traducción de Doble Negación de Gödel-Gentzen (con Ejemplos en Lean 4)](#5-la-traducción-de-doble-negación-de-gödel-gentzen-con-ejemplos-en-lean-4)
6. [El Teorema de Diaconescu: Cómo `Classical.choice` Implica `P ∨ ¬P`](#6-el-teorema-de-diaconescu-cómo-classicalchoice-implica-p--p)
7. [Catálogo de Demostraciones Comparadas (Términos $\lambda$ vs Tácticas)](#7-catálogo-de-demostraciones-comparadas-términos-lambda-vs-tácticas)

---

## 1. La Trinidad de Curry-Howard-Lambek (Lógica, Tipos y Categorías)

El isomorfismo de Curry-Howard se extiende con el trabajo de Joachim Lambek a una correspondencia triple (**el Triunvirato Computacional**):

| Lógica Intuicionista | Teoría de Tipos Dependientes (Lean 4) | Teoría de Categorías (LCCCs / Topos) |
| :--- | :--- | :--- |
| Proposición $P$ | Tipo $P : \texttt{Prop}$ | Objeto $P$ |
| Demostración $\Gamma \vdash p : P$ | Término $\Gamma \vdash p : P$ | Morfismo $\Gamma \xrightarrow{p} P$ |
| Verdad $\top$ (`True`) | Tipo Unitario (`Unit`) | Objeto Terminal $1$ |
| Falsedad $\bot$ (`False`) | Tipo Vacío (`Empty`) | Objeto Inicial $0$ |
| Conjunción $P \land Q$ | Tipo Producto $P \times Q$ | Producto Categórico $P \times Q$ |
| Disyunción $P \lor Q$ | Tipo Suma $P \oplus Q$ (`Sum P Q`) | Coproducto Categórico $P \sqcup Q$ |
| Implicación $P \to Q$ | Tipo Función $P \to Q$ | Objeto Exponencial $Q^P$ |
| Universal $\forall x : A,\, B(x)$ | Producto Dependiente $\Pi (x : A),\, B(x)$ | Adjunto Derecho $\Pi_f$ al cambio de base $f^*$ |
| Existencial $\exists x : A,\, B(x)$ | Suma Dependiente $\Sigma (x : A),\, B(x)$ | Adjunto Izquierdo $\Sigma_f$ al cambio de base $f^*$ |

---

## 2. Las Conectivas Proposicionales como Tipos Inductivos en Lean 4

Con la única excepción de la implicación $P \to Q$ y el cuantificador universal $\forall x : A,\, P(x)$ (que son primitivos del kernel mediante `Expr.forallE`), **todas las demás conectivas lógicas de Lean 4 son simples tipos inductivos definidos en la librería estándar**:

```lean
-- 1. Verdad (1 constructor sin argumentos):
inductive True : Prop where
  | intro : True

-- 2. Falsedad (0 constructores):
inductive False : Prop

-- 3. Negación (abreviatura de implicar False):
def Not (a : Prop) : Prop := a → False
prefix:max "¬" => Not

-- 4. Conjunción (estructura inductiva con 1 constructor y 2 campos):
structure And (a b : Prop) : Prop where
  intro ::
  left  : a
  right : b

-- 5. Disyunción (tipo inductivo con 2 constructores):
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

-- 6. Equivalencia lógica (estructura que empaqueta dos implicaciones):
structure Iff (a b : Prop) : Prop where
  intro ::
  mp  : a → b
  mpr : b → a
```

### Ejemplo 2.1: Reducción de Cortes = $\beta/\iota$-Reducción
En lógica de Gentzen, eliminar un lema intermedio ("corte") de una demostración corresponde exactamente a **evaluar ($\beta/\iota$-reducir) el término $\lambda$**:
* Construir `⟨hp, hq⟩ : P ∧ Q` y proyectar inmediatamente `.left` se reduce en el kernel a `hp`:
  ```lean
  example {P Q : Prop} (hp : P) (hq : Q) : (And.intro hp hq).left = hp := rfl
  ```

---

## 3. Cuantificadores como $\Pi$-Types y $\Sigma$-Types en `Prop`

### 3.1 El Cuantificador Universal (`∀ x : α, P x`)
En Lean 4, `∀ x : α, P x` y `(x : α) → P x` son **el mismo tipo**.
* **Introducir $\forall$:** Abstraer una variable con `fun x => ...` (o `intro x`).
* **Eliminar $\forall$:** Aplicar la hipótesis $h : \forall x : \alpha,\, P(x)$ a un término concreto $a : \alpha$ obteniendo `h a : P a`.

```lean
-- Ejemplo: Si para todo x se cumple P x → Q x, y para todo x se cumple P x,
-- entonces para todo x se cumple Q x.
-- Observa que es exactamente el combinador S dependiente: `fun h1 h2 x => h1 x (h2 x)`
theorem forall_modus_ponens {α : Type} {P Q : α → Prop}
    (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x :=
  fun x => h1 x (h2 x)
```

### 3.2 El Cuantificador Existencial (`∃ x : α, P x`)
Se define en la librería estándar como la versión en `Prop` de un $\Sigma$-type:
```lean
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
```

```lean
-- Ejemplo: Demostrar que existe un número natural k tal que 10 = 2 * k,
-- proporcionando el testigo explícito `5` y la prueba `rfl`:
example : ∃ k : Nat, 10 = 2 * k :=
  ⟨5, rfl⟩

-- Ejemplo: Eliminar un existencial para demostrar otro existencial:
theorem exists_mono {α : Type} {P Q : α → Prop}
    (himp : ∀ x, P x → Q x) (hex : ∃ x, P x) : ∃ x, Q x :=
  match hex with
  | ⟨w, hpw⟩ => ⟨w, himp w hpw⟩
```

---

## 4. Semántica de Brouwer-Heyting-Kolmogorov (BHK) y Lógica Constructiva

En la interpretación BHK (que el cálculo lambda tipado materializa formalmente):
* **No existe verdad sin evidencia:** Afirmar $P \lor Q$ constructivamente exige indicar cuál de los dos disjuntos se cumple (`Or.inl` o `Or.inr`).
* Por tanto, si $P$ es una conjetura abierta (como la conjetura de Goldbach), no poseemos ni una prueba de $P$ ni una refutación $P \to \bot$, por lo que no podemos construir un término cerrado de $P \lor \neg P$ sin axiomas no computables.

### Tabla de Principios Clásicos Equivalentes entre Sí
En presencia de la lógica intuicionista base, las siguientes cinco afirmaciones son **mutuamente equivalentes** (ninguna es constructivamente demostrable, pero asumir cualquiera de las primeras cuatro permite demostrar las demás):

1. **Principio del Tercio Excluso (`LEM`):** $\forall P : \texttt{Prop},\, P \lor \neg P$.
2. **Eliminación de la Doble Negación (`DNE`):** $\forall P : \texttt{Prop},\, \neg\neg P \to P$.
3. **Ley de Peirce:** $\forall P\; Q : \texttt{Prop},\, ((P \to Q) \to P) \to P$.
4. **Contraposición Clásica:** $\forall P\; Q : \texttt{Prop},\, (\neg Q \to \neg P) \to (P \to Q)$.
5. **Implicación Material Clásica:** $\forall P\; Q : \texttt{Prop},\, (P \to Q) \to (\neg P \lor Q)$.

Demostremos formalmente en Lean 4, **de manera 100% constructiva (sin abrir `Classical`)**, que `LEM`, `DNE` y la `Ley de Peirce` son equivalentes:

```lean
def LEM    : Prop := ∀ P : Prop, P ∨ ¬P
def DNE    : Prop := ∀ P : Prop, ¬¬P → P
def Peirce : Prop := ∀ P Q : Prop, ((P → Q) → P) → P

-- 1. LEM → DNE (Constructivo):
theorem lem_imp_dne (lem : LEM) : DNE :=
  fun P hnnp =>
    match lem P with
    | Or.inl hp  => hp
    | Or.inr hnp => False.elim (hnnp hnp)

-- 2. DNE → Peirce (Constructivo):
theorem dne_imp_peirce (dne : DNE) : Peirce :=
  fun P Q hpqp =>
    dne P (fun hnp =>
      have hp : P := hpqp (fun hp => False.elim (hnp hp))
      hnp hp)

-- 3. Peirce → LEM (Constructivo):
theorem peirce_imp_lem (peirce : Peirce) : LEM :=
  fun P =>
    peirce (P ∨ ¬P) False (fun h_not_em =>
      Or.inr (fun hp => h_not_em (Or.inl hp)))
```

---

## 5. La Traducción de Doble Negación de Gödel-Gentzen (con Ejemplos en Lean 4)

Aunque $\neg\neg P \to P$ no es constructivamente válido para una proposición arbitraria $P$, **sí es constructivamente válido cuando $P$ es una negación ($\neg A$), una conjunción de proposiciones estables o una fórmula universal sobre un consecuente estable**.

Además, la **mónada de doble negación** $T(P) := \neg\neg P$ permite incrustar toda la lógica clásica dentro de la lógica intuicionista:

```lean
-- La doble negación actúa como una mónada en `Prop`:
-- 1. `pure` (Introducción de doble negación):
theorem dn_pure {P : Prop} (hp : P) : ¬¬P :=
  fun hnp => hnp hp

-- 2. `bind` (Si tenemos ¬¬P y de P se deduce ¬¬Q, entonces tenemos ¬¬Q):
theorem dn_bind {P Q : Prop} (h : ¬¬P) (f : P → ¬¬Q) : ¬¬Q :=
  fun hnq => h (fun hp => f hp hnq)

-- 3. Aplicando `dn_bind` al teorema de Glivenko `¬¬(P ∨ ¬P)`, podemos hacer
--    análisis de casos clásico `P ∨ ¬P` de forma 100% CONSTRUCTIVA siempre que
--    nuestra meta final sea una proposición negada `¬R` o doblemente negada `¬¬R`!
theorem analisis_casos_constructivo_en_meta_negada {P R : Prop}
    (h_pos : P → ¬R) (h_neg : ¬P → ¬R) : ¬R :=
  fun hr =>
    have h_em_dn : ¬¬(P ∨ ¬P) :=
      fun h => h (Or.inr (fun hp => h (Or.inl hp)))
    h_em_dn (fun hp_or_np =>
      match hp_or_np with
      | Or.inl hp  => h_pos hp hr
      | Or.inr hnp => h_neg hnp hr)
```

---

## 6. El Teorema de Diaconescu: Cómo `Classical.choice` Implica `P ∨ ¬P`

En Lean 4, el principio del tercio excluso `Classical.em` **no es un axioma primitivo**, sino un **teorema** demostrado a partir de:
1. `Classical.choice : Nonempty α → α` (Axioma de elección global en tipos).
2. `propext : (P ↔ Q) → P = Q` (Extensionalidad proposicional).
3. `Quot.sound` (Cocientes).

**Idea de la demostración de Radu Diaconescu (1975):**
Dada una proposición $P : \texttt{Prop}$, se definen dos predicados sobre `Bool`:
* $U(x) :\equiv (x = \texttt{true}) \lor P$
* $V(x) :\equiv (x = \texttt{false}) \lor P$

Ambos subtipos están habitados (`true` habita $U$ y `false` habita $V$). Aplicando la función de elección `Classical.choice` elegimos representantes $u \in U$ y $v \in V$.
* Si $u = v$, entonces ambos no pueden ser `true` y `false` a la vez, de donde se deduce $P$.
* Si $u \neq v$, como $P$ implicaría por `propext` y `funext` que los predicados $U$ y $V$ son idénticos (y por tanto que la función de elección habría devuelto el mismo elemento $u = v$), concluimos $\neg P$.
* Como la igualdad en `Bool` es decidible ($u = v \lor u \neq v$), obtenemos $P \lor \neg P$.
