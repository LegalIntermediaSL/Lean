# Módulo 02: Teoría de Tipos Dependientes — Tipos $\Pi$, Tipos $\Sigma$ y Subtipos

> **Archivo Lean ejecutable asociado:** [`LeanTT/M02_DependentTypes.lean`](../LeanTT/M02_DependentTypes.lean)

---

## 1. ¿Qué es un Tipo Dependiente?

En los lenguajes de programación convencionales (Java, Rust, Haskell estándar, OCaml), existe una barrera infranqueable entre la **fase de tipos** y la **fase de valores**: un tipo puede depender de otro tipo (`List<T>`), pero **nunca de un valor de ejecución** (`Vector<T, n>` donde `n : Nat` es el resultado de una función arbitraria).

En la **Teoría de Tipos Dependientes de Martin-Löf (MLTT)**, los tipos son ciudadanos de primera clase: una función puede recibir un valor ordinario $x : A$ y devolver un **tipo** $B(x) : \texttt{Type}$.

Formalmente, una **familia de tipos** indexada por un tipo $A : \texttt{Type } u$ es simplemente una función:

$$B : A \to \texttt{Type } v$$

---

## 2. El Tipo Producto Dependiente ($\Pi$-Type)

Dada una familia de tipos $B : A \to \texttt{Sort } v$, el **tipo producto dependiente**

$$\Pi (x : A),\, B(x) \qquad \text{escrito en Lean 4 como } \texttt{(x : A) → B x} \text{ o } \texttt{∀ (x : A), B x}$$

es el tipo de las funciones $f$ que, para cada entrada $a : A$, producen un resultado $f(a)$ cuyo tipo es específicamente $B(a)$.

### Reglas Formales de Inferencia para $\Pi$-Types

* **Formación:**
  $$\frac{\Gamma \vdash A : \texttt{Sort } u \qquad \Gamma, x : A \vdash B(x) : \texttt{Sort } v}{\Gamma \vdash (\Pi x : A,\, B(x)) : \texttt{Sort }(\text{imax}(u, v))}$$
* **Introducción ($\lambda$-abstracción):**
  $$\frac{\Gamma, x : A \vdash t : B(x)}{\Gamma \vdash (\lambda x : A.\, t) : \Pi x : A,\, B(x)}$$
* **Eliminación (Aplicación dependiente):**
  $$\frac{\Gamma \vdash f : \Pi x : A,\, B(x) \qquad \Gamma \vdash a : A}{\Gamma \vdash f\; a : B[x := a]}$$
* **Computación ($\beta$):**
  $$(\lambda x : A.\, t)\; a \;\equiv_\beta\; t[x := a] : B[x := a]$$

### Caso Particular: Funciones No Dependientes
Cuando la familia $B(x)$ es constante (es decir, $x$ no aparece libre en $B$), el producto dependiente colapsa en el tipo función habitual:

$$(\Pi x : A,\, B) \;\equiv\; A \to B$$

---

## 3. El Tipo Suma Dependiente ($\Sigma$-Type)

Dada una familia de tipos $B : A \to \texttt{Type } v$, el **tipo suma dependiente** (o tipo de **pares dependientes**)

$$\Sigma (x : A),\, B(x) \qquad \text{escrito en Lean 4 como } \texttt{Σ (x : A), B x} \text{ o } \texttt{(x : A) × B x}$$

consta de pares ordenados $\langle a, b \rangle$ (`Sigma.mk a b`) donde:
1. El primer componente es un elemento $a : A$.
2. El segundo componente es un elemento $b : B(a)$, cuyo tipo **depende del valor $a$ del primer componente**.

### Caso Particular: Producto Cartesiano
Cuando $B(x) = B$ no depende de $x$, el tipo suma dependiente se reduce al producto cartesiano ordinario:

$$(\Sigma x : A,\, B) \;\equiv\; A \times B$$

---

## 4. Comparación entre $\Sigma$-Types (`Sigma`), Subtipos (`Subtype`) y Existenciales (`Exists`)

En Lean 4 existen tres formas de "pares dependientes" según en qué universo (`Type` vs `Prop`) viven el primer y el segundo componente:

| Construcción | Sintaxis en Lean 4 | 1.er Componente ($a$) | 2.º Componente ($b$) | Universo Resultante | ¿Se borra $b$ al compilar? |
| :--- | :--- | :---: | :---: | :---: | :---: |
| **`Sigma`** | `(x : α) × β x` o `Σ x, β x` | `α : Type u` | `β x : Type v` | `Type (max u v)` | No (ambos son datos computacionales) |
| **`Subtype`** | `{ x : α // P x }` | `α : Type u` | `P x : Prop` | `Type u` | **Sí** (la prueba `P x` se borra en tiempo de ejecución) |
| **`Exists`** | `∃ x : α, P x` | `α : Sort u` | `P x : Prop` | `Prop` | **Sí** (todo el existencial es una proposición) |

> **Importancia práctica de `Subtype` (`{ x : α // P x }`):** Permite programar con invariantes verificados (por ejemplo, `{ l : List Nat // l ≠ [] }` o `{ n : Nat // n > 0 }`) con **cero sobrecoste en tiempo de ejecución**, ya que el compilador de Lean 4 borra todos los términos de tipo `Prop` al generar código nativo C/LLVM.

---

## 5. Parámetros Explícitos, Implícitos y de Clase en $\Pi$-Types

Lean 4 distingue cuatro tipos de ligaduras en los $\Pi$-tipos para hacer ergonómica la programación dependiente:

1. **`(x : α)` — Explícito:** El usuario debe pasar el argumento manualmente.
2. **`{x : α}` — Implícito por unificación:** Lean infiere `x` a partir de los tipos de los argumentos posteriores. Se puede forzar el paso explícito escribiendo `@f` o `f (x := valor)`.
3. **`⦃x : α⦄` — Débilmente implícito (*strict implicit*):** Solo se inserta una metavariable si la función es seguida de al menos un argumento explícito.
4. **`[inst : C α]` — Implícito por síntesis de clases de tipos (*Typeclass resolution*):** Lean busca una instancia registrada de `C α` usando su motor de resolución tabular.
