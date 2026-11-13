# Módulo 02: Teoría de Tipos Dependientes en Profundidad — Tipos $\Pi$, Tipos $\Sigma$, Fibraciones y Refinamientos

> **Archivo Lean ejecutable asociado:** [`LeanTT/M02_DependentTypes.lean`](../LeanTT/M02_DependentTypes.lean)

---

## Índice del Módulo
1. [Intuición Geométrica y Categórica: Familias de Tipos como Fibraciones](#1-intuición-geométrica-y-categórica-familias-de-tipos-como-fibraciones)
2. [Los Cuatro Juicios Fundamentales de la Teoría de Tipos de Martin-Löf](#2-los-cuatro-juicios-fundamentales-de-la-teoría-de-tipos-de-martin-löf)
3. [El Tipo Producto Dependiente ($\Pi$-Type): Secciones de una Fibración](#3-el-tipo-producto-dependiente-pi-type-secciones-de-una-fibración)
4. [El Tipo Suma Dependiente ($\Sigma$-Type): Espacio Total de una Fibración](#4-el-tipo-suma-dependiente-sigma-type-espacio-total-de-una-fibración)
5. [Álgebra de Tipos Dependientes: Isomorfismos Canónicos y el Axioma de Elección](#5-álgebra-de-tipos-dependientes-isomorfismos-canónicos-y-el-axioma-de-elección)
6. [Subtipos `{ x : α // P x }`, Borrado Computacional y Programación por Contrato](#6-subtipos--x---α--p-x--borrado-computacional-y-programación-por-contrato)
7. [Ejemplos Avanzados de Programación con Tipos Dependientes en Lean 4](#7-ejemplos-avanzados-de-programación-con-tipos-dependientes-en-lean-4)

---

## 1. Intuición Geométrica y Categórica: Familias de Tipos como Fibraciones

Para dominar la teoría de tipos dependientes, la intuición más poderosa proviene de la geometría y la teoría de categorías:

Supongamos que tenemos un tipo base $A : \texttt{Type}$ y una **familia de tipos** indexada por $A$:

$$B : A \to \texttt{Type}$$

Imagina a $A$ como un **espacio base** de puntos $x \in A$, y encima de cada punto $x : A$ cuelga un tipo distinto $B(x)$ llamado la **fibra sobre $x$**:

```text
   Fibra B(x₁)     Fibra B(x₂)     Fibra B(x₃)
     ┌─────┐         ┌─────┐         ┌─────┐
     │ b₁' │         │     │         │ b₃''│
     │  •  │         │  •  │         │  •  │   <-- Espacio Total: Σ (x : A), B(x)
     │ b₁  │         │ b₂  │         │ b₃  │
     └──┬──┘         └──┬──┘         └──┬──┘
        │               │               │      Proyección π₁ : (Σ x, B x) → A
   ─────●───────────────●───────────────●─────
        x₁              x₂              x₃     <-- Espacio Base: A
```

Con esta imagen mental:
1. **Un habitante del tipo Suma Dependiente $\Sigma (x : A),\, B(x)$** es un punto en el **espacio total**: consiste en elegir primero una coordenada base $x : A$ y luego un punto $y : B(x)$ dentro de la fibra que cuelga sobre ese $x$, formando el par dependiente $\langle x, y \rangle$.
2. **Un habitante del tipo Producto Dependiente $\Pi (x : A),\, B(x)$** es una **sección global** del fibrado: una función $s$ que elige simultáneamente, para **cada** punto $x : A$ de la base, un elemento $s(x) : B(x)$ en su fibra correspondiente.

### ¿Por qué se llaman "Producto" ($\Pi$) y "Suma" ($\Sigma$)?
Si el tipo base $A$ es finito con elementos $\{x_1, x_2, \dots, x_n\}$:
* Elegir un elemento en cada fibra equivale al producto cartesiano de todas las fibras:
  $$\left| \Pi (x : A),\, B(x) \right| = \prod_{i=1}^n |B(x_i)| = |B(x_1)| \times |B(x_2)| \times \dots \times |B(x_n)|$$
* Elegir un punto base $x_i$ y un elemento de su fibra equivale a la unión disjunta (coproducto) de todas las fibras:
  $$\left| \Sigma (x : A),\, B(x) \right| = \sum_{i=1}^n |B(x_i)| = |B(x_1)| + |B(x_2)| + \dots + |B(x_n)|$$

---

## 2. Los Cuatro Juicios Fundamentales de la Teoría de Tipos de Martin-Löf

A diferencia de la teoría de conjuntos ZF (donde existe un único universo de conjuntos sin tipos y la pertenencia $x \in y$ es una proposición lógica que puede ser verdadera o falsa), en la **Teoría de Tipos de Per Martin-Löf (MLTT)** los contextos dependen del orden: cada variable introducida puede aparecer en los tipos de las variables posteriores:

$$\Gamma \equiv (x_1 : A_1,\; x_2 : A_2(x_1),\; \dots,\; x_n : A_n(x_1, \dots, x_{n-1}))$$

Sobre un contexto válido $\Gamma$, el kernel de Lean maneja cuatro **juicios formales**:
1. $\Gamma \vdash A : \texttt{Sort } u$ — "$A$ es un tipo bien formado en el contexto $\Gamma$".
2. $\Gamma \vdash t : A$ — "El término $t$ habita el tipo $A$ en el contexto $\Gamma$".
3. $\Gamma \vdash A \equiv B : \texttt{Sort } u$ — "Los tipos $A$ y $B$ son definicionalmente iguales".
4. $\Gamma \vdash t \equiv s : A$ — "Los términos $t$ y $s$ son definicionalmente iguales al tipo $A$".

**Regla de Conversión de Tipos (Crucial):**
$$\frac{\Gamma \vdash t : A \qquad \Gamma \vdash A \equiv B : \texttt{Sort } u}{\Gamma \vdash t : B}$$
Si $t$ tiene tipo $A$, y $A$ se reduce computacionalmente al mismo tipo que $B$, entonces $t$ también tiene tipo $B$ sin necesidad de ningún transporte ni conversión explícita.

---

## 3. El Tipo Producto Dependiente ($\Pi$-Type): Secciones de una Fibración

En Lean 4, el producto dependiente se escribe indistintamente como:
* `(x : α) → β x`
* `∀ (x : α), β x`
* `Π (x : α), β x` *(en Mathlib)*

### Ejemplo 3.1: Funciones Polimórficas y Dependientes Unificadas
En el Cálculo de Construcciones, **el polimorfismo paramétrico no es un mecanismo separado**, sino un caso particular de $\Pi$-type donde el primer argumento habita en un universo `Type u`:

```lean
-- Polimorfismo es simplemente un Π-type cuyo dominio es `Type`:
-- `identidad` tiene tipo `(α : Type) → (x : α) → α`
def identidad : (α : Type) → α → α :=
  fun _ x => x

-- Familia dependiente de un valor booleano:
def TipoSegunFlag (esEntero : Bool) : Type :=
  if esEntero then Int else String

-- Sección global de la familia `TipoSegunFlag`:
def negarOInvertir : (b : Bool) → (x : TipoSegunFlag b) → TipoSegunFlag b
  | true,  (n : Int)    => -n
  | false, (s : String) => String.mk s.data.reverse

#eval negarOInvertir true 42        -- -42 : Int
#eval negarOInvertir false "LAMBDA" -- "ADBMAL" : String
```

### Ejemplo 3.2: Tuplas Heterogéneas N-arias (`HList` / `NProduct`)
Podemos construir un tipo que tome una **lista de tipos** `[α₁, α₂, ..., αₙ] : List Type` y calcule el producto cartesiano anidado `α₁ × (α₂ × ... × Unit)`:

```lean
/-- `HList [Nat, String, Bool]` se reduce definicionalmente a `Nat × (String × (Bool × Unit))` -/
def HList : List Type → Type
  | []      => Unit
  | α :: αs => α × HList αs

/-- Ejemplo de habitante de `HList [Nat, String, Bool]` -/
def filaTabla : HList [Nat, String, Bool] :=
  (101, ("Alonzo Church", (true, ())))

/-- Función dependiente que extrae el k-ésimo tipo de una lista de tipos -/
def TipoEnIndice : (αs : List Type) → Fin αs.length → Type
  | α :: _,  ⟨0, _⟩     => α
  | _ :: αs, ⟨k + 1, h⟩ => TipoEnIndice αs ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- Proyección heterogénea tipada: extrae el elemento en la posición `i` con su tipo exacto! -/
def HList.get : {αs : List Type} → HList αs → (i : Fin αs.length) → TipoEnIndice αs i
  | _ :: _,  (x, _),  ⟨0, _⟩     => x
  | _ :: αs, (_, xs), ⟨k + 1, h⟩ => xs.get ⟨k, Nat.lt_of_succ_lt_succ h⟩

#eval filaTabla.get ⟨0, by decide⟩ -- 101 : Nat
#eval filaTabla.get ⟨1, by decide⟩ -- "Alonzo Church" : String
#eval filaTabla.get ⟨2, by decide⟩ -- true : Bool
```

---

## 4. El Tipo Suma Dependiente ($\Sigma$-Type): Espacio Total de una Fibración

En Lean 4, la suma dependiente en `Type` está definida en la librería estándar como:

```lean
structure Sigma {α : Type u} (β : α → Type v) where
  fst : α
  snd : β fst
```

* Notación: `Σ (x : α), β x` o `(x : α) × β x`.
* Constructor: `Sigma.mk a b` o la notación anónima `⟨a, b⟩`.
* Primera proyección: `p.fst : α` (o `p.1`).
* Segunda proyección: `p.snd : β (p.fst)` (o `p.2`). **¡Observa que el tipo de `p.snd` menciona a `p.fst`!**

> **Nota para tipos `Sort u` generales:** Si $\alpha : \texttt{Sort } u$ o $\beta : \alpha \to \texttt{Sort } v$ pueden ser tanto `Prop` como `Type`, Lean proporciona `PSigma` (con notación `Σ' x, β x`).

### Ejemplo 4.1: Matrices de Dimensión Dinámica Empaquetadas con $\Sigma$-Types
Cuando leemos una matriz o un vector desde un archivo externo o desde la entrada del usuario, no conocemos su longitud $n$ en tiempo de compilación, pero una vez leída queremos utilizar operaciones estáticamente verificadas sobre `Vec α n`. El tipo suma dependiente `Σ (n : Nat), Vec α n` resuelve este problema:

```lean
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n + 1)

def filtrarVec {α : Type} (p : α → Bool) : {n : Nat} → Vec α n → (m : Nat) × Vec α m
  | 0,     .nil       => ⟨0, .nil⟩
  | _ + 1, .cons x xs =>
    let ⟨m, ys⟩ := filtrarVec p xs
    if p x then
      ⟨m + 1, .cons x ys⟩
    else
      ⟨m, ys⟩
```
Observa por qué `filtrarVec` **necesita** devolver un $\Sigma$-type `(m : Nat) × Vec α m`: la longitud `m` del vector resultante depende de cuántos elementos satisfagan el predicado `p` en tiempo de ejecución.

---

## 5. Álgebra de Tipos Dependientes: Isomorfismos Canónicos y el Axioma de Elección

En la teoría de tipos dependientes existe un conjunto de isomorfismos fundamentales entre $\Pi$-types y $\Sigma$-types que generalizan las leyes de los exponentes y las distributividades aritméticas:

### 5.1 Currificación Dependiente (Adjunción entre $\Sigma$ y $\Pi$)
Dar una función dependiente sobre un par dependiente $p : \Sigma (x : A),\, B(x)$ es equivalente a dar una función de dos argumentos dependientes:

$$\Big( (p : \Sigma (x : A),\, B(x)) \to C(p) \Big) \;\simeq\; \Big( (x : A) \to (y : B(x)) \to C(\langle x, y \rangle) \Big)$$

```lean
def curryDep {A : Type u} {B : A → Type v} {C : ((x : A) × B x) → Type w}
    (f : (p : (x : A) × B x) → C p) :
    (x : A) → (y : B x) → C ⟨x, y⟩ :=
  fun x y => f ⟨x, y⟩

def uncurryDep {A : Type u} {B : A → Type v} {C : ((x : A) × B x) → Type w}
    (g : (x : A) → (y : B x) → C ⟨x, y⟩) :
    (p : (x : A) × B x) → C p :=
  fun ⟨x, y⟩ => g x y

-- El isomorfismo es definicional en ambas direcciones (`rfl`) gracias a la η-regla de Sigma:
example {A : Type u} {B : A → Type v} {C : ((x : A) × B x) → Type w}
    (f : (p : (x : A) × B x) → C p) : uncurryDep (curryDep f) = f :=
  rfl
```

### 5.2 El "Axioma" de Elección Tipo-Teórico (Teorema Constructivo)
En teoría de conjuntos ZF, el Axioma de Elección es independiente. En cambio, en MLTT, la distributividad de $\Pi$ sobre $\Sigma$:

$$\Big( \Pi (x : A),\, \Sigma (y : B(x)),\, R(x, y) \Big) \;\simeq\; \Big( \Sigma (f : \Pi (x : A),\, B(x)),\, \Pi (x : A),\, R(x, f(x)) \Big)$$

es un **teorema trivialmente demostrable** porque una prueba constructiva de que para cada $x$ existe un $y$ es, por definición, una función $h$ de la cual podemos proyectar el primer componente $f(x) := (h\;x).1$ y la prueba $(h\;x).2$:

> **¿Por qué entonces el Axioma de Elección clásico no es constructivo en Lean?** Porque en lógica clásica el existencial vive en `Prop` ($\forall x : A,\, \exists y : B(x),\, R(x, y)$) donde el testigo $y$ ha sido borrado por irrelevancia de prueba y `Large Elimination` está prohibida.

---

## 6. Subtipos `{ x : α // P x }`, Borrado Computacional y Programación por Contrato

El tipo `Subtype` se define en el preludio de Lean 4 como:

```lean
structure Subtype {α : Sort u} (p : α → Prop) where
  val : α
  property : p val
```
con la notación `{ x : α // p x }`.

### Ejemplo 6.1: Búsqueda Binaria o Indexación de Arrays sin Comprobaciones Dinámicas
En Lean 4, la operación `xs[i]` sobre un `Array α` o `List α` utiliza tipos dependientes: recibe implícitamente una prueba `h : i < xs.size` que garantiza en tiempo de compilación que el índice está en rango:

```lean
-- Acceso seguro sin Option ni pánico en tiempo de ejecución:
def primerElemento (xs : Array String) (h : 0 < xs.size) : String :=
  xs[0]'h

-- Usando un subtipo para representar porcentajes válidos (0 ≤ p ≤ 100):
abbrev Porcentaje := { p : Nat // p ≤ 100 }

def complementoPorcentaje (p : Porcentaje) : Porcentaje :=
  ⟨100 - p.val, by omega⟩

#eval (complementoPorcentaje ⟨35, by decide⟩).val -- 65
```

---

## 7. Ejemplos Avanzados de Programación con Tipos Dependientes en Lean 4

### Ejemplo 7.1: Evaluador de un Lenguaje de Esquemas de Bases de Datos Tipado
```lean
inductive ColType where
  | int  : ColType
  | text : ColType
  | flag : ColType
  deriving DecidableEq, Repr

@[simp]
def ColType.toLeanType : ColType → Type
  | .int  => Int
  | .text => String
  | .flag => Bool

abbrev Schema := List (String × ColType)

/-- Una fila `Row s` es un tipo dependiente del esquema `s : Schema` -/
def Row : Schema → Type
  | []            => Unit
  | (_, ct) :: s' => ct.toLeanType × Row s'

def esquemaEmpleados : Schema :=
  [("id", .int), ("nombre", .text), ("activo", .flag)]

def empleado1 : Row esquemaEmpleados :=
  (1, ("Kurt Gödel", (true, ())))
```
