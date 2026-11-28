# Módulo 01: Del Cálculo Lambda ($\lambda$) a los Sistemas de Tipos Puros y el Cubo de Barendregt

> **Archivo Lean ejecutable asociado:** [`LeanTT/M01_LambdaCalculus.lean`](../LeanTT/M01_LambdaCalculus.lean)

---

## Índice del Módulo
1. [El Cálculo Lambda No Tipado ($\lambda$) en Profundidad](#1-el-cálculo-lambda-no-tipado-lambda-en-profundidad)
2. [Sustitución Libre de Captura e Índices de De Bruijn](#2-sustitución-libre-de-captura-e-índices-de-de-bruijn)
3. [Las Seis Reglas de Reducción del Kernel de Lean 4 (con Ejemplos)](#3-las-seis-reglas-de-reducción-del-kernel-de-lean-4-con-ejemplos)
4. [Estrategias de Evaluación, Confluencia (Church-Rosser) y Normalización](#4-estrategias-de-evaluación-confluencia-church-rosser-y-normalización)
5. [Cálculo Combinatorio SKI y Completitud Funcional](#5-cálculo-combinatorio-ski-y-completitud-funcional)
6. [Codificaciones de Church / Böhm-Berarducci en Lean 4](#6-codificaciones-de-church--böhm-berarducci-en-lean-4)
7. [Sistemas de Tipos Puros (PTS) y el Cubo de Barendregt Completo](#7-sistemas-de-tipos-puros-pts-y-el-cubo-de-barendregt-completo)
8. [Ejercicios Resueltos en Lean 4](#8-ejercicios-resueltos-en-lean-4)

---

## 1. El Cálculo Lambda No Tipado ($\lambda$) en Profundidad

El **Cálculo Lambda**, introducido por Alonzo Church en 1932–1936, destila la noción matemática de **función como regla de cómputo intensional** (en contraste con la visión conjuntista de función como conjunto de pares ordenados).

### 1.1 Gramática Formal y Convenciones Sintácticas
El conjunto $\Lambda$ de los $\lambda$-términos se genera mediante tres reglas inductivas:

$$
\begin{aligned}
t, u, v \in \Lambda \quad &::= \quad x && \text{(Variable)} \\
&\;\mid\; \quad \lambda x.\, t && \text{(Abstracción: liga } x \text{ en } t\text{)} \\
&\;\mid\; \quad (t\; u) && \text{(Aplicación: evalúa } t \text{ en } u\text{)}
\end{aligned}
$$

**Convenciones universales de paréntesis (idénticas en papel y en Lean 4):**
1. **La aplicación asocia por la izquierda:**
   $$f\; x\; y\; z \quad \equiv \quad (((f\; x)\; y)\; z)$$
2. **El cuerpo de una abstracción $\lambda$ se extiende todo lo posible hacia la derecha:**
   $$\lambda x.\, \lambda y.\, x + y \quad \equiv \quad \lambda x.\, (\lambda y.\, (x + y))$$
3. **Múltiples ligaduras se agrupan en una sola palabra clave `fun`:**
   $$\lambda x\; y\; z.\, t \quad \equiv \quad \lambda x.\, \lambda y.\, \lambda z.\, t$$

### Ejemplo 1.1: Funciones Anónimas y Currificación en Lean 4
```lean
-- En Lean 4 todas estas expresiones definen exactamente el mismo término en el kernel:
def f1 : Nat → Nat → Nat := fun x => fun y => 2 * x + y
def f2 : Nat → Nat → Nat := fun x y => 2 * x + y
def f3 : Nat → Nat → Nat := λ x y => 2 * x + y
def f4 (x y : Nat) : Nat := 2 * x + y

-- Aplicación parcial: al pasar solo el primer argumento `3`, obtenemos una nueva función `Nat → Nat`:
def fParcial : Nat → Nat := f1 3

#eval fParcial 10 -- 2 * 3 + 10 = 16

-- El kernel verifica que `f1`, `f2`, `f3` y `f4` son definicionalmente idénticas:
example : f1 = f2 ∧ f2 = f3 ∧ f3 = f4 := ⟨rfl, rfl, rfl⟩
```

---

## 2. Sustitución Libre de Captura e Índices de De Bruijn

La operación fundamental del cálculo lambda es la **sustitución** $t[x := s]$ (reemplazar las apariciones **libres** de $x$ en $t$ por el término $s$).

### 2.1 El Peligro de la Captura de Variables
Si sustituimos ingenuamente $x := y$ dentro del término $\lambda y.\, x$, obtendríamos $\lambda y.\, y$ (la función identidad), ¡cuando el término original $\lambda y.\, x$ era la función constante que devolvía la variable externa $x$! La variable libre $y$ ha sido **capturada** por el ligador interno $\lambda y$.

Formalmente, la sustitución libre de captura se define como:
* $x[x := s] = s$
* $y[x := s] = y \quad (\text{si } y \neq x)$
* $(t_1\; t_2)[x := s] = (t_1[x := s])\; (t_2[x := s])$
* $(\lambda x.\, t)[x := s] = \lambda x.\, t \quad (x \text{ está ligada, no se sustituye})$
* $(\lambda y.\, t)[x := s] = \lambda y.\, (t[x := s]) \quad \text{si } y \neq x \text{ e } y \notin \text{FV}(s)$
* $(\lambda y.\, t)[x := s] = \lambda z.\, (t[y := z][x := s]) \quad \text{si } y \in \text{FV}(s)$, renombrando primero $y$ a una variable fresca $z$ ($\alpha$-conversión).

### 2.2 Cómo Resuelve Lean 4 la Captura: Representación Localmente Sin Nombres (De Bruijn)
En 1972, **Nicolaas Govert de Bruijn** propuso eliminar los nombres de las variables ligadas y reemplazar cada variable ligada por un número natural $k \in \mathbb{N}$ que cuenta **cuántos ligadores $\lambda$ o $\Pi$ hay que saltar hacia afuera** hasta llegar al ligador que la introdujo:

| Expresión con Nombres | Expresión con Índices de De Bruijn (0-indexado) | Representación en `Lean.Expr` |
| :--- | :--- | :--- |
| $\lambda x.\, x$ | $\lambda.\, \underline{0}$ | `.lam `x ty (.bvar 0) .default` |
| $\lambda x.\, \lambda y.\, x$ | $\lambda.\, \lambda.\, \underline{1}$ | `.lam `x ty (.lam `y ty (.bvar 1) .default) .default` |
| $\lambda x.\, \lambda y.\, y$ | $\lambda.\, \lambda.\, \underline{0}$ | `.lam `x ty (.lam `y ty (.bvar 0) .default) .default` |
| $\lambda f.\, \lambda x.\, f\;(f\; x)$ | $\lambda.\, \lambda.\, \underline{1}\;(\underline{1}\; \underline{0})$ | `.lam `f ... (.lam `x ... (.app (.bvar 1) (.app (.bvar 1) (.bvar 0))))` |

### Ejemplo 2.1: Demostración de $\alpha$-Equivalencia Automática en Lean 4
```lean
-- Aunque los nombres de las variables ligadas sean completamente distintos,
-- para el kernel de Lean ambos lados son el MISMO árbol `Expr` con índices de De Bruijn:
example : (fun (manzana : Nat) (pera : Nat) => manzana + pera) =
          (fun (x : Nat) (y : Nat) => x + y) :=
  rfl

-- Del mismo modo, en tipos dependientes (Π-types), renombrar la variable ligada es `rfl`:
example (P : Nat → Prop) : (∀ n : Nat, P n) = (∀ k : Nat, P k) :=
  rfl
```

---

## 3. Las Seis Reglas de Reducción del Kernel de Lean 4 (con Ejemplos)

En la teoría de tipos dependientes, los **tipos pueden contener términos arbitrarios** (por ejemplo, `Vec α ((fun k => k + 2) 3)`). Por ello, para comprobar si un término $t$ tiene tipo $T$, el kernel necesita decidir si dos tipos $T_1$ y $T_2$ son **definicionalmente iguales** ($T_1 \equiv T_2$).

Lean 4 decide $T_1 \equiv T_2$ aplicando seis reducciones computacionales. La táctica/constructor `rfl` tiene éxito **si y solo si** ambos lados de una igualdad se reducen a la misma forma normal bajo estas reglas:

```lean
-- 1. β-REDUCCIÓN (Aplicación de una abstracción lambda a un argumento):
--    (λ x. t) s  ──>β  t[x := s]
example : (fun (f : Nat → Nat) (x : Nat) => f (f x)) (fun n => n * 3) 2 = 18 :=
  rfl

-- 2. η-CONVERSIÓN (Extensionalidad definicional para funciones y estructuras unitarias):
--    (λ x. f x)  ≡η  f
example (α β : Type) (f : α → β) : (fun x => f x) = f :=
  rfl

--    En Lean 4, la η-conversión también vale para estructuras de un único constructor (`Prod`, etc.):
example (α β : Type) (p : α × β) : (p.fst, p.snd) = p :=
  rfl

-- 3. δ-REDUCCIÓN (Despliegue de definiciones transparentes):
def cuadrado (n : Nat) : Nat := n * n
example : cuadrado 7 = 49 :=
  rfl -- despliega `cuadrado` (δ) y evalúa `7 * 7`

-- 4. ι-REDUCCIÓN (Reconocimiento de patrones / recursor sobre constructores inductivos):
def miLongitud {α : Type} : List α → Nat
  | []      => 0
  | _ :: xs => 1 + miLongitud xs

-- `miLongitud [a, b]` se reduce por pasos ι a `1 + (1 + 0)`:
example (a b : α) : miLongitud [a, b] = 2 :=
  rfl

-- 5. ζ-REDUCCIÓN (Expansión de ligaduras locales `let`):
example (n : Nat) : (let k := n + 1; k * 2) = (n + 1) * 2 :=
  rfl

-- 6. REDUCCIÓN DE PROYECCIÓN (Seleccionar un campo de un constructor de estructura):
example (a b : Nat) : ({ fst := a, snd := b : Nat × Nat }).fst = a :=
  rfl
```

---

## 4. Estrategias de Evaluación, Confluencia (Church-Rosser) y Normalización

En un término complejo pueden existir múltiples **redexes** (subexpresiones de la forma $(\lambda x.\, t)\; s$ susceptibles de reducirse):

1. **Orden Normal (*Normal Order* / *Call-by-Name*):** Reduce siempre el redex más externo y a la izquierda, sin evaluar primero los argumentos.
   * *Propiedad:* Si un término tiene forma normal, el orden normal **siempre la encuentra** (incluso si algún argumento no se usa y divergiría).
2. **Orden Aplicativo (*Applicative Order* / *Call-by-Value*):** Evalúa primero los argumentos hasta obtener un valor antes de aplicar la función (es la estrategia de ejecución en código compilado de Lean 4 y `#eval`).
3. **Reducción a Forma Normal de Cabeza Débil (*WHNF — Weak Head Normal Form*):** El verificador de tipos de Lean (`Meta.whnf`) reduce una expresión solo lo suficiente para exponer su constructor externo ($\lambda$, $\Pi$, constante inductiva o variable aplicada), evitando desplegar subtérminos enormes si las cabezas ya difieren o ya son iguales.

---

## 5. Cálculo Combinatorio SKI y Completitud Funcional

En 1924, Moses Schönfinkel y posteriormente Haskell Curry demostraron que el cálculo lambda completo puede traducirse a un sistema **sin variables ligadas** usando únicamente tres combinadores:

$$
\begin{aligned}
I\; x &= x \\
K\; x\; y &= x \\
S\; f\; g\; x &= f\; x\; (g\; x)
\end{aligned}
$$

### Algoritmo de Abstracción de Corchetes (*Bracket Abstraction*)
Dado cualquier término $t$ que puede contener una variable $x$, construimos un término $[x]^*\, t$ (que NO contiene a $x$) tal que $([x]^*\, t)\; x \longrightarrow^* t$:
1. $[x]^*\, x = I$
2. $[x]^*\, c = K\; c \quad (\text{si } x \notin \text{FV}(c))$
3. $[x]^*\, (t_1\; t_2) = S\; ([x]^*\, t_1)\; ([x]^*\, t_2)$

### Ejemplo 5.1: Traducción de $\lambda x.\, \lambda y.\, y\; x$ (el combinador `reverseApply` / $T$) a SKI en Lean 4
Aplicando el algoritmo:
* $[y]^*\, (y\; x) = S\; ([y]^*\, y)\; ([y]^*\, x) = S\; I\; (K\; x)$
* $[x]^*\, (S\; I\; (K\; x)) = S\; (K\; (S\; I))\; K$

Comprobémoslo formalmente en Lean 4:
```lean
universe u v

def I {α : Type u} (x : α) : α := x
def K {α : Type u} {β : Type v} (x : α) (_ : β) : α := x
def S {α β γ : Type u} (f : α → β → γ) (g : α → β) (x : α) : γ := f x (g x)

-- Demostración por β-reducción pura (`rfl`) de que `S (K (S I)) K x f = f x`:
theorem reverse_apply_ski {α : Type u} (x : α) (f : α → α) :
    S (K (S (@I (α → α)))) (@K α (α → α)) x f = f x :=
  rfl
```

---

## 6. Codificaciones de Church / Böhm-Berarducci en Lean 4

La codificación de Böhm-Berarducci representa cualquier tipo de datos inductivo como el **tipo polimórfico de su propio eliminador (fold)**:

### 6.1 Pares Ordenados de Church ($\alpha \times \beta$)
Un par $(a, b)$ se codifica como la función de orden superior que recibe un consumidor $k : \alpha \to \beta \to \gamma$ y le entrega $a$ y $b$:

```lean
def ChurchPair (α β : Type) : Type 1 :=
  ∀ (γ : Type), (α → β → γ) → γ

def mkPair {α β : Type} (a : α) (b : β) : ChurchPair α β :=
  fun _ k => k a b

def fstPair {α β : Type} (p : ChurchPair α β) : α :=
  p α (fun a _ => a)

def sndPair {α β : Type} (p : ChurchPair α β) : β :=
  p β (fun _ b => b)

-- Las leyes de proyección se cumplen definicionalmente (`rfl`):
example (a : Nat) (b : String) : fstPair (mkPair a b) = a := rfl
example (a : Nat) (b : String) : sndPair (mkPair a b) = b := rfl
```

### 6.2 Listas de Church (`List α` como su `foldr`)
```lean
def ChurchList (α : Type) : Type 1 :=
  ∀ (γ : Type), (α → γ → γ) → γ → γ

def cNil {α : Type} : ChurchList α :=
  fun _ _ z => z

def cCons {α : Type} (x : α) (xs : ChurchList α) : ChurchList α :=
  fun γ f z => f x (xs γ f z)

def cAppend {α : Type} (xs ys : ChurchList α) : ChurchList α :=
  fun γ f z => xs γ f (ys γ f z)

def cLength {α : Type} (xs : ChurchList α) : Nat :=
  xs Nat (fun _ acc => acc + 1) 0

example : cLength (cCons 10 (cCons 20 cNil)) = 2 := rfl
```

---

## 7. Sistemas de Tipos Puros (PTS) y el Cubo de Barendregt Completo

Un **Sistema de Tipos Puros (PTS)** se especifica mediante una terna $(\mathcal{S}, \mathcal{A}, \mathcal{R})$:
* **$\mathcal{S}$ (Sorts):** Conjunto de universos, en el cubo clásico $\mathcal{S} = \{*, \square\}$ donde $* = \texttt{Type}$ y $\square = \texttt{Kind}$.
* **$\mathcal{A}$ (Axiomas):** $* : \square$.
* **$\mathcal{R}$ (Reglas de formación de productos $\Pi$):** Subconjunto de ternas $(s_1, s_2, s_3)$ que gobiernan la regla:
  $$\frac{\Gamma \vdash A : s_1 \qquad \Gamma, x : A \vdash B : s_2}{\Gamma \vdash (\Pi x : A,\, B) : s_3}$$

Cada una de las 4 reglas $(s_1, s_2, s_2)$ con $s_i \in \{*, \square\}$ abre una dimensión del cubo:

```lean
-- 1. Regla (*, *, *) — λ→ (STLC): Términos que dependen de Términos
--    A : Type, B : Type  ⊢  (A → B) : Type
def stlcEjemplo : Nat → Bool := fun n => n == 0

-- 2. Regla (□, *, *) — λ2 (Sistema F): Términos que dependen de Tipos
--    α : Type (que vive en □ = Type 1), (α → α) : Type  ⊢  (∀ α : Type, α → α) : Type 1
def sistemaFEjemplo : ∀ (α : Type), α → α := fun _ x => x

-- 3. Regla (□, □, □) — λω_ : Tipos que dependen de Tipos (Operadores de Tipos)
--    α : Type  ⊢  List (α × α) : Type
def operadorDeTipos : Type → Type := fun α => List (α × α)

-- 4. Regla (*, □, □) — λP (LF): Tipos que dependen de Términos (¡Tipos Dependientes!)
--    n : Nat  ⊢  Aridad n : Type
def Aridad : Nat → Type
  | 0     => Nat
  | n + 1 => Nat → Aridad n

-- `Aridad 3` se reduce definicionalmente a `Nat → Nat → Nat → Nat`!
def sumarTres : Aridad 3 :=
  fun a b c => a + b + c

#eval sumarTres 10 20 30 -- 60
```

---

## 8. Ejercicios Resueltos en Lean 4

### Ejercicio 1: Combinador $W$ (Duplicador $\lambda f.\, \lambda x.\, f\; x\; x$) a partir de $S, K, I$
```lean
def I {α : Type} (x : α) : α := x
def K {α β : Type} (x : α) (_ : β) : α := x
def S {α β γ : Type} (f : α → β → γ) (g : α → β) (x : α) : γ := f x (g x)
def W {α β : Type} (f : α → α → β) (x : α) : β := f x x

-- Solución: `W = S S (K I)`
theorem w_from_ski {α β : Type} (f : α → α → β) (x : α) :
    S S (K (@I α)) f x = W f x :=
  rfl
```

### Ejercicio 2: Predecesor de Kleene en Numerales de Church
```lean
-- El truco de Kleene usa pares `(a, b)` avanzando `(0, 0) ↦ (0, 1) ↦ (1, 2) ↦ ... ↦ (n-1, n)`:
def cPred (n : ∀ α : Type, (α → α) → α → α) : ∀ α : Type, (α → α) → α → α :=
  fun α f x =>
    (n (α × α) (fun p => (p.2, f p.2)) (x, x)).1
```
