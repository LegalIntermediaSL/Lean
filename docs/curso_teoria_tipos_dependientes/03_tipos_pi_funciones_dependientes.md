# Lección 03: Definición Formal II — El Tipo Producto Dependiente ($\Pi$-Type) y las Funciones Dependientes

> **Navegación del Mini-Curso:** [⬅️ Lección 02: Juicios, Contextos y Universos](02_juicios_contextos_y_universos.md) | [🏠 Índice](00_indice_minicurso_ttd.md) | [➡️ Lección 04: El Tipo Σ (Pares Dependientes)](04_tipos_sigma_pares_dependientes.md)
>
> **Apartado de Wikipedia ampliado:** Subsección sobre **el tipo $\Pi$ (funciones dependientes / producto dependiente)** dentro de *«Definición formal»* en [Teoría de Tipos Dependientes](https://es.wikipedia.org/wiki/Teor%C3%ADa_de_Tipos_Dependientes).
>
> **Módulos ejecutables relacionados:** [`LeanTT/M02_DependentTypes.lean`](../../LeanTT/M02_DependentTypes.lean), [`LeanTT/M15_DidacticDependentTypesFromZero.lean`](../../LeanTT/M15_DidacticDependentTypesFromZero.lean) y [`LeanTT/M40_MiniDependentTypeChecker.lean`](../../LeanTT/M40_MiniDependentTypeChecker.lean).

---

## 1. Definición y Notaciones del Producto Dependiente ($\Pi$-Type)

Tal como expone el artículo de Wikipedia:
> *"Dados un tipo $A : \mathcal{U}_i$ y una familia de tipos $B : A \to \mathcal{U}_j$, se puede construir el **tipo de funciones dependientes** (o **producto dependiente**) $\prod_{x:A} B(x)$ (también escrito $\Pi (x:A), B(x)$), cuyos términos son funciones que toman un elemento $a : A$ y devuelven un elemento en $B(a)$."*

### 1.1 Equivalencia de Notaciones en la Literatura y en Lean 4
A lo largo de la literatura matemática y en los asistentes de pruebas encontrarás cinco formas de escribir exactamente el mismo tipo:

| Notación | Dónde se usa | Ejemplo con Vectores |
| :--- | :--- | :--- |
| $\displaystyle\prod_{x : A} B(x)$ o $\Pi (x : A),\, B(x)$ | Artículos de Martin-Löf, HoTT Book y Wikipedia | $\displaystyle\prod_{n : \mathbb{N}} \text{Vec}(\alpha, n)$ |
| `(x : A) → B x` | **Lean 4** (cuando el codominio es un tipo de datos `Type u`) | `(n : Nat) → Vec α n` |
| `∀ (x : A), B x` | **Lean 4** (cuando el codominio es una proposición `Prop`; internamente es idéntico a `(x : A) → B x`) | `∀ (n : Nat), n + 0 = n` |
| `forall (x : A), B x` | Coq / Rocq | `forall (n : nat), vec A n` |
| `(x : A) -> B x` | Agda e Idris 2 | `(n : Nat) -> Vect n a` |

> **¿Por qué se llama «Producto» ($\Pi$) a un tipo de funciones?**
> En teoría de conjuntos y álgebra, si tenemos una familia de conjuntos $\{B_x\}_{x \in A}$ indexada por $A$, su **producto cartesiano generalizado** $\prod_{x \in A} B_x$ se define precisamente como el conjunto de todas las **funciones de elección** $f$ con dominio $A$ tales que $f(x) \in B_x$ para cada $x \in A$.
> Por ejemplo, si $A = \{1, 2\}$, una función $f : \prod_{i \in \{1, 2\}} B_i$ elige un elemento $f(1) \in B_1$ y un elemento $f(2) \in B_2$, lo que equivale a una tupla en $B_1 \times B_2$ (cuyo cardinal es $|B_1| \cdot |B_2|$).

---

## 2. Las 5 Reglas Canónicas de Inferencia del Tipo $\Pi$

Veamos las cinco reglas formales que gobiernan el producto dependiente en el kernel de Lean 4:

### 2.1 Regla 1: Formación ($\Pi$-Form)
Si $A$ es un tipo válido en el contexto $\Gamma$, y al extender el contexto con una hipótesis $x : A$ la expresión $B(x)$ es un tipo válido, entonces el producto dependiente $(x : A) \to B(x)$ es un tipo válido:

$$
\frac{\Gamma \vdash A : \mathcal{U}_i \qquad \Gamma,\; x : A \vdash B(x) : \mathcal{U}_j}{\Gamma \vdash \prod_{x : A} B(x) : \mathcal{U}_{\text{imax}(i, j)}} \;(\Pi\text{-Form})
$$

*(Nota sobre el nivel de universo en Lean 4: si los universos son predicativos de datos $\mathcal{U}_i = \texttt{Type } u$ y $\mathcal{U}_j = \texttt{Type } v$, el resultado vive en $\texttt{Type }(\max(u, v))$. Si el codominio $B(x)$ es una proposición en $\texttt{Prop} = \texttt{Sort } 0$, entonces $\text{imax}(i, 0) = 0$, por lo que $\forall (x : A), B(x)$ sigue siendo una proposición en $\texttt{Prop}$).*

### 2.2 Regla 2: Introducción ($\Pi$-Intro / Abstracción $\lambda$)
Para fabricar un habitante de $\prod_{x:A} B(x)$, introducimos una variable fresca $x : A$ en el contexto y construimos un cuerpo $b(x)$ cuyo tipo sea $B(x)$:

$$
\frac{\Gamma,\; x : A \vdash b(x) : B(x)}{\Gamma \vdash (\lambda (x : A).\, b(x)) : \prod_{x : A} B(x)} \;(\Pi\text{-Intro})
$$

En Lean 4 se escribe `fun (x : A) => b x` (o `λ x => b x`).

### 2.3 Regla 3: Eliminación ($\Pi$-Elim / Aplicación Dependiente)
Si tenemos una función dependiente $f : \prod_{x:A} B(x)$ y un argumento concreto $a : A$, podemos aplicar $f$ a $a$. **El tipo del resultado se obtiene sustituyendo la variable $x$ por el término $a$ dentro del tipo $B(x)$:**

$$
\frac{\Gamma \vdash f : \prod_{x : A} B(x) \qquad \Gamma \vdash a : A}{\Gamma \vdash f(a) : B[a/x]} \;(\Pi\text{-Elim})
$$

¡Esta sustitución $B[a/x]$ en el tipo de salida es la firma distintiva de la Teoría de Tipos Dependientes!

### 2.4 Regla 4: Computación ($\Pi$-$\beta$)
Aplicar una abstracción $\lambda$ recién construida a un argumento $a : A$ se reduce computacionalmente sustituyendo $x$ por $a$ en el cuerpo $b(x)$:

$$
\frac{\Gamma,\; x : A \vdash b(x) : B(x) \qquad \Gamma \vdash a : A}{\Gamma \vdash (\lambda (x : A).\, b(x))(a) \;\equiv\; b[a/x] : B[a/x]} \;(\Pi\text{-}\beta)
$$

### 2.5 Regla 5: Unicidad ($\Pi$-$\eta$)
Toda función dependiente $f : \prod_{x:A} B(x)$ es definicionalmente igual a la abstracción $\lambda$ que toma $x$ y le aplica $f$:

$$
\frac{\Gamma \vdash f : \prod_{x : A} B(x)}{\Gamma \vdash f \;\equiv\; (\lambda (x : A).\, f(x)) : \prod_{x : A} B(x)} \;(\Pi\text{-}\eta)
$$

---

## 3. Casos Particulares e Intuición Geométrica

### 3.1 Caso Degenerado: Funciones Ordinarias ($A \to B$)
Como señala el artículo de Wikipedia:
> *"Cuando la familia $B$ es constante (es decir, $B(x) \equiv B$ no depende de la variable $x$), el producto dependiente $\prod_{x:A} B$ se reduce al **tipo de funciones ordinarias** $A \to B$ del cálculo lambda simplemente tipado."*

En efecto, en Lean 4 la flecha simple `A → B` no es un constructor primitivo distinto en el kernel: es simplemente azúcar sintáctico para `(_ : A) → B` (un tipo $\Pi$ donde la variable ligada no aparece libre en el codominio).

### 3.2 Polimorfismo Paramétrico (Sistema F) como caso particular de $\Pi$
Cuando el dominio $A$ es un **universo de tipos** ($A \equiv \texttt{Type } u$), un producto dependiente
$$(\alpha : \texttt{Type } u) \to \alpha \to \alpha$$
toma primero un **tipo** $\alpha$ y devuelve una función $\alpha \to \alpha$ para ese tipo. Así, el polimorfismo de lenguajes como Haskell, Rust o Java (*generics*) es simplemente un caso particular de tipo $\Pi$ donde el argumento resulta ser un tipo.

### 3.3 Intuición Geométrica: Secciones de una Fibración
Si visualizamos la familia $B : A \to \mathcal{U}$ como un conjunto de fibras verticales situadas sobre cada punto $a : A$ del espacio base (véase la Lección 02), ¿qué es una función dependiente $f : \prod_{x:A} B(x)$?

Es una **sección transversal** del haz fibrado: una curva que, para cada coordenada horizontal $a : A$, elige exactamente un punto $f(a)$ **dentro de la fibra vertical $B(a)$ correspondiente a ese punto**, de manera que al proyectar $f(a)$ hacia abajo volvemos a caer sobre $a$.

---

## 4. Argumentos Implícitos `{x : A}` en Lean 4

Como en los tipos dependientes el tipo de un segundo argumento suele mencionar al primero, sería tedioso escribir siempre todos los argumentos a mano. Por ejemplo, en la función identidad polimórfica:
```lean
def idExplicita (α : Type) (x : α) : α := x
#eval idExplicita Nat 42
```
Al pasar `42 : Nat` como segundo argumento, Lean 4 ya sabe que `α` **tiene que ser `Nat`**. Por eso Lean permite marcar argumentos de un tipo $\Pi$ entre llaves `{α : Type}` (argumentos **implícitos**), pidiéndole al elaborador bidireccional (estudiado en el [`Módulo 50`](../../LeanTT/M50_BidirectionalElaboratorAndUnification.lean)) que los deduzca por unificación:

```lean
def idImplicita {α : Type} (x : α) : α := x
#eval idImplicita 42       -- Lean infiere automáticamente `α := Nat`
#eval @idImplicita Nat 42  -- El prefijo `@` convierte los argumentos implícitos en explícitos
```

---

## 5. Laboratorio en Lean 4: Cuatro Ejemplos Clásicos de Tipos $\Pi$

### Ejemplo 5.1: El Combinador $S$ Dependiente
En lógica combinatoria clásica, el combinador $S$ tiene tipo $(A \to B \to C) \to (A \to B) \to A \to C$. En Teoría de Tipos Dependientes, $B$ puede depender de $x : A$, y $C$ puede depender **tanto de $x : A$ como del resultado $y : B(x)$**:

```lean
def combinadorSDependiente
    {A : Type u}
    {B : A → Type v}
    {C : (x : A) → B x → Type w}
    (f : (x : A) → (y : B x) → C x y)
    (g : (x : A) → B x) :
    (x : A) → C x (g x) :=
  fun x => f x (g x)
```
Observa la precisión quirúrgica del tipo de retorno `(x : A) → C x (g x)`: la función `g` aparece **dentro del tipo** de salida porque `C` está indexado por el valor `g x : B x`.

### Ejemplo 5.2: `replicate` y `append` sobre Vectores de Longitud Exacta
```lean
inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n + 1)
  deriving Repr

/-- Tipo Π genuino: el valor numérico de `n` determina el tipo de salida `Vec α n` -/
def replicate {α : Type u} (n : Nat) (x : α) : Vec α n :=
  match n with
  | 0     => .nil
  | k + 1 => .cons x (replicate k x)

/-- La concatenación suma las longitudes a nivel de tipos: `Vec α (m + n)` -/
def append {α : Type u} {m n : Nat} : Vec α m → Vec α n → Vec α (m + n)
  | .nil,       ys => by
    -- En esta rama `m = 0`, y como `0 + n = n`, transportamos o usamos recursión en `m`
    simpa [Nat.zero_add] using ys
  | .cons x xs, ys =>
    by
      have cola := append xs ys
      rw [Nat.succ_add]
      exact .cons x cola
```

### Ejemplo 5.3: Aridad Variable Calculada por un Tipo $\Pi$ (`NaryFun n`)
¿Puede una función en un lenguaje estáticamente tipado recibir un **número de argumentos que dependa de un parámetro natural $n$**? ¡Sí, calculando un tipo $\Pi$ por recursión sobre $n$!

```lean
/-- `SumaN n` calcula el tipo `Nat → Nat → ... → Nat` con `n` argumentos `Nat`: -/
def SumaN : Nat → Type
  | 0     => Nat
  | n + 1 => Nat → SumaN n

/-- Acumulador con tipo Π `(n : Nat) → Nat → SumaN n`: -/
def sumarArgumentos : (n : Nat) → Nat → SumaN n
  | 0,     acc => acc
  | k + 1, acc => fun x => sumarArgumentos k (acc + x)

-- `sumarArgumentos 3 0` tiene tipo `Nat → Nat → Nat → Nat` (espera exactamente 3 números):
#eval sumarArgumentos 3 0 10 20 30 -- 60
-- `sumarArgumentos 1 0` tiene tipo `Nat → Nat` (espera exactamente 1 número):
#eval sumarArgumentos 1 0 42       -- 42
```

---

## 6. Ejercicios Prácticos de la Lección 03 (en Lean 4)

### Ejercicio 3.1: Composición Dependiente (`compDep`)
Dados:
* $A : \texttt{Type } u$
* $B : A \to \texttt{Type } v$
* $C : \{x : A\} \to B\; x \to \texttt{Type } w$
* una función dependiente $g : (x : A) \to B\; x$
* y una función dependiente $f : \{x : A\} \to (y : B\; x) \to C\; y$,
escribe la composición dependiente `compDep f g` y verifica su tipo $\Pi$.

<details>
<summary>💡 <b>Ver Solución Comentada en Lean 4</b></summary>

```lean
def compDep
    {A : Type u} {B : A → Type v} {C : {x : A} → B x → Type w}
    (f : {x : A} → (y : B x) → C y)
    (g : (x : A) → B x) :
    (x : A) → C (g x) :=
  fun x => f (g x)
```
</details>

### Ejercicio 3.2: Demostrar la Regla $\eta$ del Tipo $\Pi$ en Lean 4
Demuestra en Lean 4 que para cualquier función dependiente `f : (x : A) → B x`, la igualdad `(fun x => f x) = f` se cumple por simple reflexividad `rfl` (porque el kernel incorpora la conversión $\Pi$-$\eta$).

<details>
<summary>💡 <b>Ver Solución Comentada en Lean 4</b></summary>

```lean
theorem pi_eta {A : Type u} {B : A → Type v} (f : (x : A) → B x) :
    (fun x => f x) = f :=
  rfl
```
</details>

---

👉 **Siguiente lección:** [**Lección 04 — Definición Formal III: El Tipo Suma Dependiente ($\Sigma$-Type), Pares Dependientes y el Axioma de Elección**](04_tipos_sigma_pares_dependientes.md)
