# Módulo 05: Familias Inductivas Indexadas, Eliminadores y Positividad Estricta

> **Archivo Lean ejecutable asociado:** [`LeanTT/M05_InductiveFamilies.lean`](../LeanTT/M05_InductiveFamilies.lean)

---

## 1. Tipos Inductivos en el Cálculo de Construcciones Inductivas (CIC)

Cuando declaras un tipo `inductive` en Lean 4, el kernel añade a tu entorno cuatro elementos primitivos:
1. El **constructor de tipo** $I$.
2. Los **constructores de datos** $c_1, \dots, c_k$ (reglas de introducción).
3. El **recursor o eliminador** `I.rec` (regla de eliminación e inducción dependiente).
4. Las **reglas de $\iota$-reducción** que dictan cómo se reduce `I.rec` al aplicarse a cada constructor $c_i$.

Todo lo demás (`match`, `casesOn`, `recOn`, `noConfusion`) se compila internamente hacia aplicaciones del eliminador primitivo `I.rec`.

---

## 2. Parámetros vs. Índices en Familias Inductivas

Observa la diferencia en la firma de una declaración inductiva:

```lean
inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n + 1)
```

* **Parámetros (antes de los dos puntos `:`, como `(α : Type u)`):** Deben permanecer **uniformes e invariantes** en el tipo de retorno de todos los constructores.
* **Índices (después de los dos puntos `:`, como `Nat` en `: Nat → Type u`):** Pueden **variar libremente** entre un constructor y otro (`0` en `nil`, `n + 1` en `cons`).

### El Poder del Reconocimiento de Patrones Dependiente
Cuando haces `match` sobre un habitante de una familia indexada `v : Vec α (n + 1)`, el elaborador de Lean unifica el índice `n + 1` con los índices de cada constructor:
* Como `0 = n + 1` es imposible (`Nat.noConfusion`), el caso `nil` se descarta automáticamente.
* Solo necesitas escribir el caso `cons x xs`, haciendo que funciones como `Vec.head` sean **totales**.

---

## 3. Anatomía del Eliminador (`I.rec`)

Para los números naturales:
```lean
inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat
```
El kernel genera automáticamente el recursor dependiente:
```lean
Nat.rec :
  {motive : Nat → Sort u} →
  motive Nat.zero →
  ((n : Nat) → motive n → motive (Nat.succ n)) →
  (t : Nat) → motive t
```
* Si `motive : Nat → Type u`, `Nat.rec` define una **función recursiva primitiva** (posiblemente dependiente).
* Si `motive : Nat → Prop`, `Nat.rec` es exactamente el **Principio de Inducción Matemática**.

¡En teoría de tipos dependientes, **recursión e inducción son exactamente el mismo concepto**!

---

## 4. La Condición de Positividad Estricta

¿Por qué Lean rechaza la siguiente definición inductiva?

```lean
-- ERROR: (kernel) arg #1 of 'Bad.mk' has a non positive occurrence of the datatypes being declared
inductive Bad : Type where
  | mk : (Bad → False) → Bad
```

Si `Bad` fuera aceptado, podríamos definir una función `diag (b : Bad) : False` por análisis de casos (`match b with | Bad.mk f => f b`) y luego aplicar `diag (Bad.mk diag) : False`, demostrando `False` sin hipótesis (Paradoja de Curry).

Para garantizar la consistencia y la normalización fuerte, el kernel exige **Positividad Estricta**: en el tipo de cualquier argumento de un constructor de $I$, el tipo $I$ **nunca puede aparecer a la izquierda de una flecha `→`**.

---

## 5. Recursión Estructural vs. Recursión Bien Fundada (`WellFounded`)

Todas las funciones en Lean deben ser **totales** (terminar para toda entrada). Lean dispone de dos mecanismos para verificar la terminación:

1. **Recursión Estructural:** La llamada recursiva se realiza sobre un subtérmino sintácticamente más pequeño extraído por reconocimiento de patrones (`n` dentro de `n + 1`, `xs` dentro de `x :: xs`). Se traduce directamente al eliminador `I.rec` y se calcula por $\iota$-reducción en el kernel.
2. **Recursión Bien Fundada (`termination_by` / `decreasing_by`):** Cuando el argumento disminuye según una medida general (como en `div`, el algoritmo de Euclides `gcd` o `mergeSort`), Lean utiliza `WellFounded.fix` sobre la relación de accesibilidad `Acc r a`.
