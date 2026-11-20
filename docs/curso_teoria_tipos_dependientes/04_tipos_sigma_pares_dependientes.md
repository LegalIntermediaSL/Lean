# Lección 04: Definición Formal III — El Tipo Suma Dependiente ($\Sigma$-Type), Pares Dependientes y el Axioma de Elección

> **Navegación del Mini-Curso:** [⬅️ Lección 03: El Tipo Π (Funciones Dependientes)](03_tipos_pi_funciones_dependientes.md) | [🏠 Índice](00_indice_minicurso_ttd.md) | [➡️ Lección 05: Curry-Howard en Lógica de Predicados](05_curry_howard_y_logica_predicados.md)
>
> **Apartado de Wikipedia ampliado:** Subsección sobre **el tipo $\Sigma$ (pares dependientes / suma dependiente)** dentro de *«Definición formal»* en [Teoría de Tipos Dependientes](https://es.wikipedia.org/wiki/Teor%C3%ADa_de_Tipos_Dependientes).
>
> **Módulos ejecutables relacionados:** [`LeanTT/M02_DependentTypes.lean`](../../LeanTT/M02_DependentTypes.lean), [`LeanTT/M03_UniversesAndProp.lean`](../../LeanTT/M03_UniversesAndProp.lean) y [`LeanTT/M15_DidacticDependentTypesFromZero.lean`](../../LeanTT/M15_DidacticDependentTypesFromZero.lean).

---

## 1. Definición y Notaciones de la Suma Dependiente ($\Sigma$-Type)

Continuando con la sección *«Definición formal»* del artículo de Wikipedia:
> *"Dual al producto dependiente es el **tipo de pares dependientes** (o **suma dependiente** o **tipo $\Sigma$**), denotado $\sum_{x:A} B(x)$ (o $\Sigma (x:A), B(x)$). Sus habitantes son pares ordenados $(a, b)$ tales que $a : A$ y el tipo del segundo componente depende del valor del primero: $b : B(a)$."*

### 1.1 Equivalencia de Notaciones en la Literatura y en Lean 4

| Notación | Dónde se usa | Significado |
| :--- | :--- | :--- |
| $\displaystyle\sum_{x : A} B(x)$ o $\Sigma (x : A),\, B(x)$ | Martin-Löf, HoTT Book y Wikipedia | Suma dependiente general de la familia $B$ sobre $A$. |
| `(x : A) × B x` o `Σ x : A, B x` | **Lean 4** (`Sigma B`) | Par dependiente de datos $\langle a, b \rangle$ donde $A : \texttt{Type } u$ y $B : A \to \texttt{Type } v$. |
| `{ x : A // P x }` | **Lean 4** (`Subtype P`) | **Subtipo (refinamiento):** par dependiente $\langle a, h \rangle$ donde $A : \texttt{Type } u$ es un dato y $P : A \to \texttt{Prop}$ es una propiedad lógica. |
| `∃ x : A, P x` | **Lean 4** (`Exists P`) | **Cuantificador existencial proposicional** en `Prop` (el testigo queda encapsulado por irrelevancia de prueba). |
| `Σ' x : A, B x` | **Lean 4** (`PSigma B`) | Suma dependiente polimórfica en cualquier `Sort u` y `Sort v`. |

> **¿Por qué se llama «Suma» ($\Sigma$) a un tipo de pares?**
> En teoría de conjuntos, si tenemos una familia de conjuntos $\{B_x\}_{x \in A}$ indexada por $x \in A$, su **unión disjunta (coproducto indexado)** $\bigsqcup_{x \in A} B_x$ se construye como el conjunto de todos los pares etiquetados $(a, b)$ donde la primera coordenada $a \in A$ indica de qué fibra proviene el elemento y la segunda coordenada $b \in B_a$ es el elemento dentro de esa fibra.
> Si $A$ es finito, el número total de pares es la **suma** de los cardinales de cada fibra: $\left|\sum_{x \in A} B(x)\right| = \sum_{x \in A} |B(x)|$.

---

## 2. Las 5 Reglas Canónicas de Inferencia del Tipo $\Sigma$

### 2.1 Regla 1: Formación ($\Sigma$-Form)
Dado un tipo base $A : \mathcal{U}_i$ y una familia de tipos $B : A \to \mathcal{U}_j$:

$$
\frac{\Gamma \vdash A : \mathcal{U}_i \qquad \Gamma,\; x : A \vdash B(x) : \mathcal{U}_j}{\Gamma \vdash \sum_{x : A} B(x) : \mathcal{U}_{\max(i, j)}} \;(\Sigma\text{-Form})
$$

### 2.2 Regla 2: Introducción ($\Sigma$-Intro / Constructor de Par Dependiente)
Para construir un par dependiente $\langle a, b \rangle : \sum_{x:A} B(x)$, debemos proporcionar primero un término $a : A$, y a continuación un segundo término $b$ cuyo tipo sea **$B$ evaluado en ese mismo $a$** ($B[a/x]$):

$$
\frac{\Gamma \vdash a : A \qquad \Gamma \vdash b : B[a/x]}{\Gamma \vdash \langle a, b \rangle : \sum_{x : A} B(x)} \;(\Sigma\text{-Intro})
$$

En Lean 4 se escribe `⟨a, b⟩` o `Sigma.mk a b`.

### 2.3 Regla 3: Eliminación ($\Sigma$-Elim — Proyecciones Dependientes e Inducción `Sigma.rec`)
Existen dos formas equivalentes de presentar la eliminación de un par dependiente $p : \sum_{x:A} B(x)$:

1. **Mediante las dos proyecciones ($\pi_1$ y $\pi_2$, en Lean `p.1` / `p.fst` y `p.2` / `p.snd`):**
   $$
   \frac{\Gamma \vdash p : \sum_{x : A} B(x)}{\Gamma \vdash \pi_1(p) : A} \;(\Sigma\text{-Elim}_1)
   \qquad\qquad
   \frac{\Gamma \vdash p : \sum_{x : A} B(x)}{\Gamma \vdash \pi_2(p) : B[\pi_1(p)/x]} \;(\Sigma\text{-Elim}_2)
   $$
   *¡Observa la regla $\Sigma\text{-Elim}_2$!* El tipo de la segunda proyección $\pi_2(p)$ **menciona a la primera proyección $\pi_1(p)$ del propio par $p$**.

2. **Mediante el principio de inducción dependiente (`Sigma.rec`):**
   Para demostrar o construir una sección de un motivo $C : \left(\sum_{x:A} B(x)\right) \to \mathcal{U}_k$ sobre un par arbitrario $p$, basta con definirla para los pares canónicos $\langle x, y \rangle$:
   $$
   \frac{C : \left(\sum_{x:A} B(x)\right) \to \mathcal{U}_k \qquad g : \prod_{x : A} \prod_{y : B(x)} C(\langle x, y \rangle) \qquad p : \sum_{x : A} B(x)}{\text{ind}_\Sigma(C, g, p) : C(p)}
   $$

### 2.4 Regla 4: Computación ($\Sigma$-$\beta$)
Extraer la primera o segunda proyección de un par recién construido $\langle a, b \rangle$ recupera exactamente $a$ y $b$:

$$
\pi_1(\langle a, b \rangle) \;\equiv\; a : A
\qquad\text{y}\qquad
\pi_2(\langle a, b \rangle) \;\equiv\; b : B[a/x]
$$

### 2.5 Regla 5: Unicidad ($\Sigma$-$\eta$)
Reensamblar las dos proyecciones de un par $p$ reconstruye el par original:

$$
\langle \pi_1(p),\; \pi_2(p) \rangle \;\equiv\; p : \sum_{x : A} B(x)
$$

---

## 3. Casos Particulares e Intuición Geométrica

### 3.1 Caso Degenerado: El Producto Cartesiano ($A \times B$)
Como subraya el artículo de Wikipedia:
> *"En el caso particular en que la familia $B$ no depende de $x$ (es decir, $B(x) \equiv B$ es constante), la suma dependiente $\sum_{x:A} B$ se reduce al **producto cartesiano ordinario** $A \times B$ de dos tipos."*

### 3.2 Intuición Geométrica: El Espacio Total de una Fibración
Si en la Lección 03 vimos que un tipo $\Pi$ es el espacio de las *secciones* de un haz fibrado $B : A \to \mathcal{U}$, el tipo $\Sigma (x : A), B(x)$ es el **Espacio Total ($E$)** del haz fibrado: la unión de todas las fibras $B(a)$ empaquetadas juntas, donde la primera proyección $\pi_1 : \left(\sum_{x:A} B(x)\right) \to A$ es exactamente la **proyección del haz sobre la base**.

### 3.3 Los Tres Sabores de $\Sigma$ en Lean 4: `Sigma` vs `Subtype` vs `Exists`

En Lean 4 es fundamental elegir el tipo $\Sigma$ adecuado según dónde viva la familia $B$:

| Tipo en Lean 4 | Sintaxis | Firma de $A$ y $B$ | ¿Se puede extraer el testigo $\pi_1(p)$ en código ejecutable (`Type`)? | Caso de Uso Ideal |
| :--- | :--- | :--- | :---: | :--- |
| **`Sigma`** | `(x : A) × B x` | $A : \texttt{Type } u$, $B : A \to \texttt{Type } v$ | **✅ Sí** (`p.1` y `p.2`) | Empaquetar un dato `n : Nat` con una estructura de datos `Vec α n` (p. ej. listas dinámicas como vectores). |
| **`Subtype`** | `{ x : A // P x }` | $A : \texttt{Type } u$, $P : A \to \texttt{Prop}$ | **✅ Sí** (`p.val` es el dato en tiempo de ejecución; `p.property` se borra al compilar) | **Programación certificada (Refinement Types):** números pares `{n : Nat // n % 2 = 0}`, índices `Fin n`, árboles ordenados. |
| **`Exists`** | `∃ x : A, P x` | $A : \texttt{Sort } u$, $P : A \to \texttt{Prop}$ | **❌ No** (solo puede eliminarse hacia otra proposición `Prop`) | **Teoremas puramente lógicos** donde la existencia es una afirmación en `Prop` con irrelevancia de prueba. |

---

## 4. El «Axioma de Elección» es un Teorema Demostrable en Teoría de Tipos Dependientes

Uno de los resultados más célebres de la Teoría de Tipos Dependientes de Martin-Löf (y que sorprende a quienes vienen de la teoría de conjuntos ZFC) es que el **Axioma de Elección Tipado** no es un axioma independiente, sino una **equivalencia (isomorfismo) demostrable constructivamente**:

$$\left( \prod_{x : A} \sum_{y : B(x)} R(x, y) \right) \;\simeq\; \left( \sum_{f : \prod_{x : A} B(x)} \prod_{x : A} R(x, f(x)) \right)$$

* **Lectura de izquierda a derecha:** Si para todo $x : A$ tenemos un par dependiente $\langle y, r \rangle$ formado por un elemento $y : B(x)$ y una evidencia $r : R(x, y)$, entonces ¡ya tenemos una función de elección $f : \prod_{x:A} B(x)$ (basta tomar la primera proyección $f(x) :\equiv \pi_1(g(x))$) junto con la demostración $\pi_2(g(x)) : R(x, f(x))$!

Veamos la demostración constructiva completa (con ida, vuelta y pruebas de biyección) en **Lean 4**:

```lean
universe u v w

/-- El "Axioma de Elección" de Martin-Löf es una equivalencia constructiva entre tipos Π y Σ: -/
def eleccionIda
    {A : Type u} {B : A → Type v} {R : (x : A) → B x → Type w}
    (h : (x : A) → (y : B x) × R x y) :
    (f : (x : A) → B x) × ((x : A) → R x (f x)) :=
  ⟨fun x => (h x).1, fun x => (h x).2⟩

def eleccionVuelta
    {A : Type u} {B : A → Type v} {R : (x : A) → B x → Type w}
    (p : (f : (x : A) → B x) × ((x : A) → R x (f x))) :
    (x : A) → (y : B x) × R x y :=
  fun x => ⟨p.1 x, p.2 x⟩

/-- ¡La composición en ambos sentidos es la identidad por simple cálculo (`rfl`)! -/
theorem eleccion_ida_vuelta
    {A : Type u} {B : A → Type v} {R : (x : A) → B x → Type w}
    (h : (x : A) → (y : B x) × R x y) :
    eleccionVuelta (eleccionIda h) = h :=
  rfl

theorem eleccion_vuelta_ida
    {A : Type u} {B : A → Type v} {R : (x : A) → B x → Type w}
    (p : (f : (x : A) → B x) × ((x : A) → R x (f x))) :
    eleccionIda (eleccionVuelta p) = p :=
  rfl
```
*(Nota importante: este teorema vale porque el lado izquierdo entrega constructivamente un par $\Sigma$ para cada $x$. Si reemplazamos `Sigma` por un cociente o por el existencial truncado `∃` en presencia de cocientes donde los testigos están identificados, recuperar una función sobre el cociente sí requiere el axioma clásico `Classical.choice`).*

---

## 5. Ejercicios Prácticos de la Lección 04 (en Lean 4)

### Ejercicio 4.1: Isomorfismo entre `List α` y la Suma Dependiente `(n : Nat) × Vec α n`
Una lista ordinaria `List α` de longitud desconocida en tiempo de compilación no es más que el tipo suma dependiente $\sum_{n : \mathbb{N}} \text{Vec}(\alpha, n)$ que empaqueta la longitud `n` junto con el vector de longitud `n`. Define la función `listToSigmaVec : List α → (n : Nat) × Vec α n`.

<details>
<summary>💡 <b>Ver Solución Comentada en Lean 4</b></summary>

```lean
inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n + 1)

def listToSigmaVec {α : Type u} : List α → (n : Nat) × Vec α n
  | []      => ⟨0, .nil⟩
  | x :: xs =>
    let ⟨n, v⟩ := listToSigmaVec xs
    ⟨n + 1, .cons x v⟩
```
</details>

### Ejercicio 4.2: Currying Dependiente (Adjunción entre $\Sigma$ y $\Pi$)
Demuestra constructivamente en Lean 4 que dar una función dependiente desde un par $\Sigma$ (`(p : (x : A) × B x) → C p`) es equivalente a dar una función currificada de dos argumentos dependientes (`(x : A) → (y : B x) → C ⟨x, y⟩`).

<details>
<summary>💡 <b>Ver Solución Comentada en Lean 4</b></summary>

```lean
def depCurry
    {A : Type u} {B : A → Type v} {C : ((x : A) × B x) → Type w}
    (f : (p : (x : A) × B x) → C p) :
    (x : A) → (y : B x) → C ⟨x, y⟩ :=
  fun x y => f ⟨x, y⟩

def depUncurry
    {A : Type u} {B : A → Type v} {C : ((x : A) × B x) → Type w}
    (g : (x : A) → (y : B x) → C ⟨x, y⟩) :
    (p : (x : A) × B x) → C p :=
  fun ⟨x, y⟩ => g x y
```
</details>

---

👉 **Siguiente lección:** [**Lección 05 — La Correspondencia de Curry-Howard-Lambek en Lógica de Predicados ($\forall$ y $\exists$)**](05_curry_howard_y_logica_predicados.md)
