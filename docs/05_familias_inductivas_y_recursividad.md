# Módulo 05: Familias Inductivas Indexadas, Compilación de Patrones Dependientes y Recursividad

> **Archivo Lean ejecutable asociado:** [`LeanTT/M05_InductiveFamilies.lean`](../LeanTT/M05_InductiveFamilies.lean)

---

## Índice del Módulo
1. [El Esquema General de una Familia Inductiva en el CIC](#1-el-esquema-general-de-una-familia-inductiva-en-el-cic)
2. [Parámetros vs. Índices: Cuándo Usar Cada Uno (con Ejemplos)](#2-parámetros-vs-índices-cuándo-usar-cada-uno-con-ejemplos)
3. [Cómo Compila Lean 4 el `match` Dependiente (`casesOn`, `noConfusion`)](#3-cómo-compila-lean-4-el-match-dependiente-caseson-noconfusion)
4. [Familias Inductivas Clásicas en Programación Dependiente](#4-familias-inductivas-clásicas-en-programación-dependiente)
5. [Tipos Inductivos Mutuos y Anidados (Árboles Rosa y ASTs)](#5-tipos-inductivos-mutuos-y-anidados-árboles-rosa-y-asts)
6. [La Condición de Positividad Estricta y Contraejemplos detallados](#6-la-condición-de-positividad-estricta-y-contraejemplos-detallados)
7. [Recursión Bien Fundada (`Acc`, `WellFounded`, `termination_by`)](#7-recursión-bien-fundada-acc-wellfounded-termination_by)

---

## 1. El Esquema General de una Familia Inductiva en el CIC

En el Cálculo de Construcciones Inductivas (formulado por Thierry Coquand y Christine Paulin-Mohring, y refinado por Peter Dybjer como *Inductive Families*), una declaración inductiva general tiene la forma:

```lean
inductive I (p₁ : P₁) ... (pₘ : Pₘ) : (i₁ : X₁) → ... → (iₖ : Xₖ) → Sort u where
  | c₁ : (a₁ : A₁) → ... → I p₁ ... pₘ t₁ ... tₖ
  | c₂ : ...
```

Donde:
* **`p₁, ..., pₘ` son los Parámetros:** Están fijos en todo el tipo inductivo y aparecen sin cambios (`I p₁ ... pₘ`) en la conclusión de todos los constructores.
* **`i₁, ..., iₖ` son los Índices:** Cada constructor puede instanciar los índices con términos específicos $t_1, \dots, t_k$, restringiendo en qué fibras de la familia existe ese constructor.

---

## 2. Parámetros vs. Índices: Cuándo Usar Cada Uno (con Ejemplos)

Veamos por qué la elección entre parámetro e índice cambia radicalmente el tipo del eliminador generado por el kernel:

### Ejemplo 2.1: `List α` (1 Parámetro, 0 Índices) vs. `Vec α n` (1 Parámetro, 1 Índice)
```lean
-- En `List`, `α` es un parámetro: tanto `nil` como `cons` construyen una `List α`.
-- En `Vec`, `α` es un parámetro, pero la longitud `n : Nat` cambia en cada constructor:
inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n + 1)
```

### Ejemplo 2.2: `Eq` en Lean 4 (1 Parámetro `a : α`, 1 Índice `: α`)
Observa cómo se define la igualdad en Lean 4:
```lean
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
```
* El extremo izquierdo `a : α` es un **parámetro**.
* El extremo derecho `: α` es un **índice** (que el constructor `refl` instancia a `a`).
* Gracias a que `a` es un parámetro y solo el segundo argumento es un índice, el motivo (`motive`) del eliminador `Eq.rec` solo necesita abstraer sobre un extremo libre `(b : α) → a = b → Sort v` (la regla de eliminación de **Paulin-Mohring**), lo que simplifica enormemente el reconocimiento de patrones dependiente frente a tener ambos extremos como índices.

---

## 3. Cómo Compila Lean 4 el `match` Dependiente (`casesOn`, `noConfusion`)

El kernel de Lean 4 **no tiene expresiones `match` primitivas**. El elaborador de ecuaciones de Lean traduce todo reconocimiento de patrones dependiente a aplicaciones de tres construcciones derivadas del recursor `I.rec`:

1. **`I.casesOn`:** Análisis de casos sin hipótesis inductiva.
2. **`I.noConfusion`:** Demuestra automáticamente que constructores distintos son disjuntos (`0 ≠ n + 1`, `nil ≠ cons x xs`) y que cada constructor es **inyectivo** (`Nat.succ m = Nat.succ n → m = n`).
3. **Unificación de índices:** Cuando haces `match` sobre un término `v : Vec α (n + 1)`, el elaborador unifica el índice esperado `n + 1` con el índice `0` del constructor `nil`. Como `0 = n + 1` produce `Nat.noConfusion`, esa rama se llena automáticamente con código muerto verificado y no necesitas escribirla.

```lean
-- Demostración de inyectividad y disjunción de constructores usando `noConfusion`:
example (m n : Nat) (h : Nat.succ m = Nat.succ n) : m = n :=
  Nat.noConfusion h id

example (n : Nat) (h : 0 = Nat.succ n) : False :=
  Nat.noConfusion h
```

---

## 4. Familias Inductivas Clásicas en Programación Dependiente

### 4.1 El Subconjunto Finito Canónico `Fin n` y Matrices Tipadas `Matrix α m n`
```lean
-- Una matriz de `m` filas y `n` columnas como un vector de vectores:
abbrev Matrix (α : Type u) (m n : Nat) :=
   LeanTT.M05.Vec (LeanTT.M05.Vec α n) m
```
Con esta definición, una función `transpose : Matrix α m n → Matrix α n m` o la multiplicación matricial `mul : Matrix Nat m k → Matrix Nat k n → Matrix Nat m n` hacen que un error de dimensiones entre matrices sea un **error de compilación estático**.

### 4.2 Árboles Binarios Perfectamente Balanceados por Altura (`BalTree α h`)
Podemos indexar un árbol binario por su altura $h \in \mathbb{N}$ de modo que el sistema de tipos exija que ambos subárboles de cada nodo tengan **exactamente la misma altura $h$**:

```lean
inductive BalTree (α : Type u) : Nat → Type u where
  | leaf : α → BalTree α 0
  | node : {h : Nat} → BalTree α h → BalTree α h → BalTree α (h + 1)

/-- El número de hojas de un `BalTree α h` es siempre `2 ^ h` -/
def numLeaves {α : Type u} : {h : Nat} → BalTree α h → Nat
  | 0,     .leaf _   => 1
  | _ + 1, .node l r => numLeaves l + numLeaves r

theorem numLeaves_eq_pow2 {α : Type u} {h : Nat} (t : BalTree α h) :
    numLeaves t = 2 ^ h := by
  induction t with
  | leaf _ => rfl
  | @node k l r ihl ihr =>
    simp [numLeaves, ihl, ihr, Nat.pow_succ]
    omega
```

---

## 5. Tipos Inductivos Mutuos y Anidados (Árboles Rosa y ASTs)

Lean 4 soporta definiciones inductivas **mutuas** (`mutual ... end`) y **anidadas** (donde el tipo inductivo aparece dentro de otro contenedor estrictamente positivo como `List` o `Array`):

```lean
-- 1. Tipos inductivos mutuos (`Par` e `Impar`):
mutual
  inductive Par : Nat → Prop where
    | zero : Par 0
    | succ : {n : Nat} → Impar n → Par (n + 1)

  inductive Impar : Nat → Prop where
    | succ : {n : Nat} → Par n → Impar (n + 1)
end

-- 2. Tipo inductivo anidado (Rose Tree / Árbol de aridad arbitraria):
inductive RoseTree (α : Type u) : Type u where
  | node : α → List (RoseTree α) → RoseTree α
```

---

## 6. La Condición de Positividad Estricta y Contraejemplos Detallados

Sea $I$ el tipo inductivo que estamos declarando. El tipo de cada argumento de un constructor de $I$ tiene la forma $(x_1 : B_1) \to \dots \to (x_r : B_r) \to C$. La **Positividad Estricta** exige que $I$ **no ocurra nunca** en ningún $B_j$ (es decir, nunca a la izquierda de una flecha `→`).

| Ocurrencia de `I` en el argumento del constructor | Clasificación | ¿Permitido por el Kernel de Lean? |
| :--- | :--- | :---: |
| `I → I` (el argumento del constructor es de tipo `I`) | Estrictamente positiva | **Sí** |
| `(Nat → I) → I` (`I` solo a la derecha de la flecha interna) | Estrictamente positiva (Rama infinitamente ramificada / Brouwer ordinal) | **Sí** |
| `(I → Nat) → I` (`I` a la izquierda de una flecha) | **Negativa** | **No** (Inconsistente: permite codificar $\lambda$-cálculo no tipado y $\Omega$) |
| `((I → Prop) → Prop) → I` (`I` a la izquierda de dos flechas) | Positiva pero **no estrictamente** positiva | **No** (Inconsistente con `Prop` impredicativo: Paradoja de Reynolds-Coquand) |

```lean
-- Ejemplo VÁLIDO de árbol infinitamente ramificado (Notación de ordinales de Brouwer):
-- Aquí `OrdBrouwer` aparece a la DERECHA de `Nat → OrdBrouwer`, lo cual es estrictamente positivo:
inductive OrdBrouwer : Type where
  | zero : OrdBrouwer
  | succ : OrdBrouwer → OrdBrouwer
  | lim  : (Nat → OrdBrouwer) → OrdBrouwer
```

---

## 7. Recursión Bien Fundada (`Acc`, `WellFounded`, `termination_by`)

¿Cómo permite Lean escribir algoritmos como `quicksort`, `mergeSort` o el algoritmo de Euclides `gcd`, donde la llamada recursiva se hace sobre `a % b` o `xs.filter p` en lugar de un subtérmino sintáctico directo?

Mediante el predicado inductivo de **Accesibilidad (`Acc`)** definido en el núcleo:

```lean
inductive Acc {α : Sort u} (r : α → α → Prop) (x : α) : Prop where
  | intro (h : (y : α) → r y x → Acc r y) : Acc r x
```
Un elemento $x$ es accesible respecto a la relación $<$ si no existe ninguna cadena infinita descendente $\dots < x_2 < x_1 < x$. Una relación es **bien fundada (`WellFounded r`)** si todo elemento $x : \alpha$ es accesible.

En Lean 4, las cláusulas `termination_by` y `decreasing_by` automatizan completamente la construcción de pruebas sobre `WellFounded`:

```lean
def euclidesGcd (a b : Nat) : Nat :=
  if h : b = 0 then
    a
  else
    euclidesGcd b (a % b)
termination_by b
decreasing_by
  exact Nat.mod_lt a (Nat.pos_of_ne_zero h)

#eval euclidesGcd 1071 462 -- 21
```
