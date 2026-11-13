# Módulo 08: Términos de Prueba Puros vs. Modo Táctico (`by`), `calc` y `conv`

> **Archivo Lean ejecutable asociado:** [`LeanTT/M08_TacticsAndCalculationalProofs.lean`](../LeanTT/M08_TacticsAndCalculationalProofs.lean)

---

## 1. ¿Qué hace realmente el bloque `by`?

Un principio fundamental de la arquitectura de Lean (la **arquitectura de De Bruijn**):

> **El kernel de Lean 4 no sabe qué es una táctica.** El kernel únicamente verifica términos del Cálculo de Construcciones Inductivas.

Cuando escribes una demostración usando `by ...`, el modo táctico es un **metaprograma** que construye gradualmente un término $\lambda$ con huecos (**metavariables** `?m : P`). Al finalizar el bloque `by`, el término $\lambda$ completo se entrega al kernel para que lo verifique exactamente igual que si lo hubieras escrito a mano. Puedes inspeccionar el término $\lambda$ generado por cualquier prueba táctica con `#print nombre_del_teorema`.

---

## 2. Diccionario de Traducción: Tácticas $\longleftrightarrow$ Términos $\lambda$

| Táctica en un bloque `by` | Estado de la Meta ($\Gamma \vdash G$) | Término $\lambda$ que Construye Internamente |
| :--- | :--- | :--- |
| **`intro x`** | Transforma $\vdash (x : A) \to B(x)$ en $x : A \vdash B(x)$ | `fun (x : A) => ?m` |
| **`exact t`** | Cierra la meta si $t$ tiene el tipo de la meta | `t` |
| **`apply f`** | Si $f : A \to B$ y la meta es $B$, cambia la meta a $A$ | `f ?m` |
| **`refine t`** | Como `exact`, pero permite dejar huecos `?_` en $t$ | `t` (con nuevas metavariables para cada `?_`) |
| **`have h : P := p`** | Añade la hipótesis intermedia $h : P$ al contexto | `(fun (h : P) => ?m) p` (o `let h : P := p; ?m`) |
| **`constructor`** | Para $A \land B$ o estructuras de 1 constructor, abre sus campos | `And.intro ?m1 ?m2` |
| **`cases h`** | Destruye un tipo inductivo $h$ en un subobjetivo por constructor | `Or.casesOn h (fun h1 => ?m1) (fun h2 => ?m2)` |
| **`rcases h with ⟨a, b⟩`** | Desestructuración recursiva de conjunciones/existenciales | Aplicaciones anidadas de `casesOn` |
| **`induction n`** | Aplica inducción sobre un tipo inductivo | `Nat.rec ?m_base (fun n ih => ?m_step) n` |
| **`rw [h]`** | Reescribe el objetivo usando una igualdad $h : a = b$ | Aplicación del eliminador `Eq.ndrec` / `Eq.rec` |
| **`assumption`** | Busca en el contexto $\Gamma$ una hipótesis del mismo tipo que la meta | La variable local `h` encontrada |
| **`contradiction`** | Cierra la meta si en $\Gamma$ hay $h_1 : P$ y $h_2 : \neg P$, o $h : \texttt{False}$ | `False.elim (h2 h1)` o `nomatch h` |

---

## 3. Demostraciones Calculacionales (`calc`)

En matemáticas en papel es muy común encadenar igualdades o desigualdades transitivas:
$$a = b = c \le d < e$$

El bloque `calc` de Lean 4 permite escribir este razonamiento de forma legible y verificada en cada eslabón:

```lean
example (a b : Nat) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b)
      = (a + b) * a + (a + b) * b       := by rw [Nat.mul_add]
    _ = a * a + b * a + (a * b + b * b) := by rw [Nat.add_mul, Nat.add_mul]
    _ = a * a + a * b + a * b + b * b   := by rw [Nat.mul_comm b a, ← Nat.add_assoc]
    _ = a * a + 2 * (a * b) + b * b     := by omega
```
Bajo el capó, Lean utiliza la clase `Trans` para encadenar automáticamente `=`, `≤`, `<` e `↔`.

---

## 4. El Modo de Conversión Dirigida (`conv`)

A veces `rw [Nat.add_comm]` reescribe la **primera** aparición de `x + y` en el objetivo, cuando en realidad querías reescribir solo el lado izquierdo de la ecuación o dentro de una función `fun x => ...`.

El modo `conv` te permite **hacer zoom dentro de un subtérmino** antes de aplicar una reescritura:
* `conv => lhs; ...` entra únicamente en el miembro izquierdo de la igualdad.
* `conv => rhs; ...` entra únicamente en el miembro derecho.
* `conv => enter [1, 2]; ...` o `conv in (patron) => ...` selecciona exactamente el subtérmino deseado.

---

## 5. Automatización en el Núcleo: `simp`, `decide` y `omega`

1. **`simp` (El Simplificador Contextual):** Reescribe repetidamente de adentro hacia afuera utilizando una base de datos extensible de lemas marcados con `@[simp]`, además de desplegar proyecciones y simplificar condicionales.
2. **`decide` (Prueba por Reflexión Computacional):** Si $P$ tiene una instancia de `Decidable P`, `decide` evalúa el algoritmo de decisión y reduce la prueba a `of_decide_eq_true rfl`.
3. **`omega` (Aritmética Lineal Entera de Presburger):** Resuelve automáticamente cualquier sistema de ecuaciones, inecuaciones, divisibilidad por constantes y lógica proposicional sobre `Nat` e `Int`.
