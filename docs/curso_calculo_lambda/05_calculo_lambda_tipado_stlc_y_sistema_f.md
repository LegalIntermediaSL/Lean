# Lección 05: Del Cálculo $\lambda$ Simplemente Tipado (STLC) al Sistema F, Normalización Fuerte y Parametricidad

> **Navegación del Mini-Curso:** [⬅️ Lección 04: Lógica Combinatoria SKI](04_logica_combinatoria_ski_y_abstraccion.md) | [🏠 Índice](00_indice_minicurso_lambda.md) | [➡️ Lección 06: Máquinas Abstractas (Krivine, CEK, NbE)](06_maquinas_abstractas_krivine_cek_y_nbe.md)
>
> **Módulos ejecutables relacionados:** [`LeanTT/M10_MetatheorySTLC.lean`](../../LeanTT/M10_MetatheorySTLC.lean), [`LeanTT/M16_DidacticLambdaCubeAndPTS.lean`](../../LeanTT/M16_DidacticLambdaCubeAndPTS.lean) y [`LeanTT/M26_SystemFAndParametricity.lean`](../../LeanTT/M26_SystemFAndParametricity.lean).

---

## 1. ¿Por Qué Añadimos Tipos al Cálculo Lambda? (Church, 1940)

En el cálculo $\lambda$ no tipado de las Lecciones 01–04 podemos escribir cualquier algoritmo recursivo gracias al término de autoaplicación $\omega \equiv \lambda x.\, x\; x$ y al combinador $Y$.
Pero esa expresividad ilimitada tiene una consecuencia devastadora si queremos usar el cálculo $\lambda$ como **fundamento lógico**:
* Si todo tipo o proposición $P$ pudiera habitarse usando el combinador de punto fijo $Y\; (\lambda p : P.\, p) : P$, **toda proposición sería demostrable** (incluida la falsedad $\bot$: la **Paradoja de Curry**).
* La reducción $\beta$ puede no terminar jamás: $\Omega = (\lambda x.\, x\; x)(\lambda x.\, x\; x) \longrightarrow_\beta \Omega$.

En **1940**, Alonzo Church formuló el **Cálculo Lambda Simplemente Tipado ($\lambda^\to$, STLC)**:
* Los tipos se construyen inductivamente a partir de tipos base ($\iota, \text{Nat}, \text{Bool}$) mediante el constructor de flecha $\sigma \to \tau$.
* Toda variable ligada lleva una anotación de su tipo: $\lambda (x : \sigma).\, t$.
* **Regla de aplicación:** Para aplicar $f$ a $a$, $f$ debe tener tipo $\sigma \to \tau$ y $a$ debe tener tipo $\sigma$.

> **¿Por qué $\lambda x.\, x\; x$ queda prohibido en STLC?**
> Si $x$ tuviera tipo $\sigma$, para poder aplicarse a sí mismo ($x\; x$) el primer $x$ tendría que tener a la vez tipo $\sigma \to \tau$, lo que exigiría la igualdad de árboles finitos $\sigma = (\sigma \to \tau)$, que es imposible.

---

## 2. El Teorema de Normalización Fuerte (Tait, 1967)

La propiedad más profunda del Cálculo $\lambda$ Simplemente Tipado (y que se extiende al Sistema $F$ por Girard y al Cálculo de Construcciones Inductivas de Lean 4) es la **Normalización Fuerte (*Strong Normalization*)**:

> **Teorema de Normalización Fuerte:** En el cálculo $\lambda$ tipado ($\lambda^\to$, Sistema $F$, CIC), **no existen cadenas infinitas de $\beta$-reducción**. Independientemente de qué redex elijamos reducir en cada paso, toda secuencia de reducciones desde un término bien tipado $\Gamma \vdash t : \tau$ termina en un número finito de pasos en su única forma normal.

### ¿Por qué no basta una inducción estructural ingenua para demostrar la Normalización Fuerte?
Porque al contraer $(\lambda x : \sigma.\, t)\; u \longrightarrow_\beta t[u/x]$, si $x$ aparece $10$ veces dentro de $t$, el término sustituido $t[u/x]$ puede ser **mucho más grande** que el término original.

En **1967**, **William W. Tait** inventó el método de las **Relaciones Lógicas (o Candidatos de Reducibilidad de Girard)**:
definimos un predicado semántico $\text{Red}_\tau(t)$ (*«$t$ es hereditariamente reducible de tipo $\tau$»*) por recursión sobre el **tipo** $\tau$:
* **En un tipo base $\iota$:** $\text{Red}_\iota(t) \iff t$ es fuertemente normalizable ($\text{SN}(t)$).
* **En un tipo función $\sigma \to \tau$:**
  $$\text{Red}_{\sigma \to \tau}(f) \;\iff\; \forall u,\; \text{Red}_\sigma(u) \implies \text{Red}_\tau(f\; u)$$
  *(«Una función es reducible si transforma cualquier argumento reducible en un resultado reducible»).*

En el módulo [`LeanTT/M10_MetatheorySTLC.lean`](../../LeanTT/M10_MetatheorySTLC.lean) de este repositorio hemos formalizado un **evaluador total denotacional del STLC en Lean 4** (`eval : Env Γ → Term Γ τ → τ.denote`) que traduce cada término intrínsecamente tipado del STLC a una función de Lean 4 sin ningún bucle ni combustible `fuel`, certificando constructivamente su terminación.

---

## 3. El Sistema $F$ ($\lambda 2$) de Girard-Reynolds y el Teorema de Parametricidad (*Theorems for Free*)

En el STLC ($\lambda^\to$), no podemos escribir una única función identidad: tenemos que escribir $\text{id}_{\text{Nat}} = \lambda x : \text{Nat}.\, x$, $\text{id}_{\text{Bool}} = \lambda x : \text{Bool}.\, x$, etc.

En **1972–1974**, el lógico **Jean-Yves Girard** (para estudiar la teoría de la demostración de la aritmética de segundo orden) y el informático **John C. Reynolds** (para estudiar el polimorfismo en lenguajes de programación) descubrieron independientemente el **Sistema $F$ (o $\lambda 2$)**:
* Añade **abstracción sobre tipos** ($\Lambda \alpha.\, t$) y **aplicación de tipos** ($t\; [\tau]$), habitando el **tipo polimórfico universal**:
  $$\forall \alpha.\, T(\alpha) \qquad \big(\text{escrito en Lean 4 como } \texttt{(α : Type) → T α}\big)$$

### El Teorema de Parametricidad de Reynolds (1983) y *Theorems for Free!* (Philip Wadler, 1989)
Como una función polimórfica pura $f : \forall \alpha.\, T(\alpha)$ en el Sistema $F$ no puede inspeccionar qué tipo concreto $\alpha$ le han pasado (no tiene reflexión en tiempo de ejecución ni `instanceof`), **debe tratar a todos los valores de tipo $\alpha$ como cajas negras opacas**.

Esto significa que **solo con mirar el tipo polimórfico de una función podemos deducir teoremas matemáticos sobre su comportamiento**:

| Firma Polimórfica en Sistema F / Lean 4 | ¿Cuántas funciones puras habitan este tipo? | Teorema Gratis (*Free Theorem*) por Parametricidad |
| :--- | :--- | :--- |
| `(α : Type) → α → α` | **Exactamente 1:** la identidad `fun α x => x` | $f\; \beta\; (g\; x) = g\; (f\; \alpha\; x)$ $\implies f\; \alpha\; x = x$ |
| `(α : Type) → α → α → α` | **Exactamente 2:** `cTrue` y `cFalse` (los 2 booleanos de Church) | $f\; \beta\; (g\; x)\; (g\; y) = g\; (f\; \alpha\; x\; y)$ |
| `(α : Type) → (α → α) → α → α` | **Infinitas numerables:** los numerales de Church $c_0, c_1, c_2, \dots$ | Conmuta con cualquier homomorfismo de álgebras unarias |
| `(α : Type) → List α → List α` | Reordenaciones / duplicaciones / borrados de índices (`reverse`, `tail`, `take n`) | **Naturalidad con `List.map`:** `List.map g (r α xs) = r β (List.map g xs)` |

---

## 4. Demostración en Lean 4 de un «Teorema Gratis» por Parametricidad

En [`LeanTT/M26_SystemFAndParametricity.lean`](../../LeanTT/M26_SystemFAndParametricity.lean) (y en el siguiente fragmento autocontenido) demostramos que toda función polimórfica $f : (\alpha : \texttt{Type}) \to \alpha \to \alpha$ que cumple la condición de parametricidad de Reynolds para relaciones funcionales **es necesariamente igual a la función identidad**:

```lean
namespace CursoLambda.Leccion05

/-- Condición de Parametricidad Relacional de Reynolds para `f : (α : Type) → α → α`:
    Para cualesquiera tipos `α, β` y cualquier función `g : α → β`,
    aplicar `g` después de `f α` es igual a aplicar `f β` después de `g`. -/
def EsParametricaId (f : (α : Type) → α → α) : Prop :=
  ∀ (α β : Type) (g : α → β) (x : α), f β (g x) = g (f α x)

/-- TEOREMA ("Theorem for Free!"):
    Cualquier función `f : (α : Type) → α → α` que cumpla la naturalidad paramétrica de Reynolds
    satisface `f α x = x` para todo tipo `α` y todo elemento `x : α`! -/
theorem unica_habitante_id_polimorfica
    (f : (α : Type) → α → α) (hParam : EsParametricaId f)
    (α : Type) (x : α) :
    f α x = x := by
  -- Instanciamos la condición de parametricidad con `Unit`, la función constante `fun _ => x` y `()`:
  have h := hParam Unit α (fun _ => x) ()
  -- El lado izquierdo de `h` es `f α x`, y el lado derecho es `(fun _ => x) (f Unit ()) = x`!
  exact h

end CursoLambda.Leccion05
```

---

## 5. Ejercicio Práctico de la Lección 05

### Ejercicio 5.1: Teorema Gratis para Booleanos de Church `(α : Type) → α → α → α`
Formula la condición de parametricidad relacional para una función $b : (\alpha : \texttt{Type}) \to \alpha \to \alpha \to \alpha$:
$$\forall (\alpha\, \beta : \texttt{Type})\, (g : \alpha \to \beta)\, (x\, y : \alpha),\;\; b\; \beta\; (g\; x)\; (g\; y) = g\; (b\; \alpha\; x\; y)$$
y demuestra en Lean 4 que cualquier función $b$ que la cumpla está completamente determinada por su valor sobre `Bool` (`b Bool true false`): si `b Bool true false = true`, entonces $b\; \alpha\; x\; y = x$; y si `b Bool true false = false`, entonces $b\; \alpha\; x\; y = y$.

<details>
<summary>💡 <b>Ver Solución Comentada en Lean 4</b></summary>

```lean
def EsParametricaBool (b : (α : Type) → α → α → α) : Prop :=
  ∀ (α β : Type) (g : α → β) (x y : α), b β (g x) (g y) = g (b α x y)

theorem solo_dos_booleanos_de_church
    (b : (α : Type) → α → α → α) (hParam : EsParametricaBool b)
    (α : Type) (x y : α) :
    b α x y = (if b Bool true false then x else y) := by
  have h := hParam Bool α (fun cond => if cond then x else y) true false
  exact h
```
</details>

---

👉 **Siguiente lección:** [**Lección 06 — Máquinas Abstractas para el Cálculo $\lambda$ (Krivine KAM, Máquina CEK) y Normalización por Evaluación (NbE) en Lean 4**](06_maquinas_abstractas_krivine_cek_y_nbe.md)
