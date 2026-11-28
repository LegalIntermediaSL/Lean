# Módulo 08: Modo Término vs. Modo Táctico (`by`), Estado de Metavariables, `calc` y `conv`

> **Archivo Lean ejecutable asociado:** [`LeanTT/M08_TacticsAndCalculationalProofs.lean`](../LeanTT/M08_TacticsAndCalculationalProofs.lean)

---

## Índice del Módulo
1. [El Criterio de De Bruijn y el Papel de las Metavariables (`?m`)](#1-el-criterio-de-de-bruijn-y-el-papel-de-las-metavariables-m)
2. [Tabla Completa de Traducción: Tácticas $\longleftrightarrow$ Términos $\lambda$ Dependientes](#2-tabla-completa-de-traducción-tácticas-longleftrightarrow-términos-lambda-dependientes)
3. [Mezclando Modo Término y Modo Táctico Libremente](#3-mezclando-modo-término-y-modo-táctico-libremente)
4. [Estructuración Profesional de Demostraciones (`have`, `suffices`, `obtain`, `rcases`)](#4-estructuración-profesional-de-demostraciones-have-suffices-obtain-rcases)
5. [Pruebas Calculacionales (`calc`) y Relaciones Transitivas Generalizadas (`Trans`)](#5-pruebas-calculacionales-calc-y-relaciones-transitivas-generalizadas-trans)
6. [Modo de Conversión Dirigida (`conv`): Navegación Quirúrgica bajo Ligadores $\lambda$](#6-modo-de-conversión-dirigida-conv-navegación-quirúrgica-bajo-ligadores-lambda)

---

## 1. El Criterio de De Bruijn y el Papel de las Metavariables (`?m`)

Un asistente de demostraciones satisface el **Criterio de De Bruijn** si todas las pruebas generadas por su motor de automatización o de tácticas se traducen a un **lenguaje nuclear diminuto** verificable por un **kernel independiente de pocas miles de líneas de código**.

En Lean 4, ese lenguaje nuclear es el **Cálculo de Construcciones Inductivas (`Lean.Expr`)**.

### ¿Cómo construye una táctica un término $\lambda$ paso a paso?
1. Al iniciar `theorem T : P := by ...`, Lean crea una **metavariable** raíz `?m0 : P` en el contexto vacío $\Gamma = []$.
2. Cuando ejecutas `intro h` (suponiendo que $P \equiv A \to B$), la táctica asigna:
   $$?m_0 := \texttt{fun } (h : A) \Rightarrow ?m_1$$
   donde `?m1` es una **nueva metavariable** de tipo $B$ en el contexto extendido $\Gamma = [h : A]$.
3. Cuando todas las metavariables han sido asignadas sin ciclos y sin huecos pendientes, la expresión resultante se envía al kernel.

---

## 2. Tabla Completa de Traducción: Tácticas $\longleftrightarrow$ Términos $\lambda$ Dependientes

| Táctica en `by` | Acción en el Estado de Prueba ($\Gamma \vdash G$) | Equivalente Exacto en Términos $\lambda$ |
| :--- | :--- | :--- |
| `intro x` | Mueve el antecedente/ligador $\Pi$ al contexto $\Gamma$ | `fun x => ...` |
| `exact e` | Cierra la meta actual con el término `e` | `e` |
| `apply f` | Empareja la conclusión de `f` con la meta y abre submetas para las premisas de `f` | `f ?_ ?_ ...` |
| `refine e` | Como `exact`, pero cada `?_` en `e` se convierte en una nueva submeta | `e` |
| `have h : A := p` | Introduce un lema local `h : A` demostrado por `p` | `let h : A := p; ...` (con tipo opaco) |
| `let x : A := v` | Introduce una definición local transparente (`ζ`-reducible) | `let x : A := v; ...` |
| `suffices h : A by tac` | Invierte el orden: primero prueba la meta asumiendo `h : A`, luego prueba `A` | `(fun (h : A) => ...) (by tac)` |
| `constructor` | Aplica el único constructor de una estructura o conjunción | `⟨?_, ?_⟩` |
| `left` / `right` | Selecciona el primer o segundo constructor de `P ∨ Q` | `Or.inl ?_` / `Or.inr ?_` |
| `cases h` | Destruye `h` por casos usando `casesOn` | `match h with \| ... => ...` |
| `rcases h with ⟨a, b \| c⟩` | Desestructura recursivamente productos, existenciales y sumas | `match` anidados |
| `obtain ⟨x, hx⟩ := h` | Combina `have` y `rcases` en un paso | `match h with \| ⟨x, hx⟩ => ...` |
| `induction n with ...` | Aplica el principio de inducción `rec` | `Nat.rec ...` |
| `rw [h]` / `rw [← h]` | Reescribe con `h : a = b` (de izq. a der. o viceversa) | `Eq.ndrec ... h` |
| `subst x` | Si hay `h : x = e`, sustituye `x` por `e` en todo $\Gamma$ y la meta | Eliminación de Paulin-Mohring |
| `contradiction` | Busca `h : False` o `h1 : P` y `h2 : ¬P` en $\Gamma$ | `absurd h1 h2` / `False.elim h` |

---

## 3. Mezclando Modo Término y Modo Táctico Libremente

En Lean 4, `by ...` es simplemente una expresión que puede aparecer en **cualquier lugar donde se espere un término**, y dentro de `by ...` puedes pasar términos $\lambda$ complejos a `exact` o `refine`:

```lean
-- Ejemplo de prueba híbrida: usamos construcción de términos `⟨..., ...⟩` y `fun`
-- en la estructura exterior, y delegamos la aritmética interna a `by omega`:
theorem division_con_resto_acotado (a : Nat) :
    ∃ q r : Nat, a = 5 * q + r ∧ r < 5 :=
  ⟨a / 5, a % 5, ⟨by omega, by omega⟩⟩
```

---

## 4. Estructuración Profesional de Demostraciones (`have`, `suffices`, `obtain`, `rcases`)

```lean
theorem estructuracion_ejemplo {P Q R S : Prop}
    (h1 : P ∧ (Q ∨ R)) (h2 : P → Q → S) (h3 : P → R → S) : S := by
  -- `rcases` desestructura en profundidad conjunciones y disyunciones en una sola línea:
  rcases h1 with ⟨hp, hq | hr⟩
  · -- Subcaso 1: tenemos `hp : P` y `hq : Q`
    have hs : S := h2 hp hq
    exact hs
  · -- Subcaso 2: tenemos `hp : P` y `hr : R`
    suffices h_basta : R → S by
      exact h_basta hr
    exact h3 hp
```

---

## 5. Pruebas Calculacionales (`calc`) y Relaciones Transitivas Generalizadas (`Trans`)

Un bloque `calc` en Lean 4 puede mezclar **distintas relaciones** (`=`, `≤`, `<`) siempre que exista una instancia de la clase de tipos dependiente `Trans`:

```text
class Trans (r : α → β → Sort u) (s : β → γ → Sort v) (t : outParam (α → γ → Sort w)) where
  trans : r a b → s b c → t a c
```

```lean
-- Ejemplo de cadena `calc` que combina `=`, `<` y `≤`:
theorem desigualdad_encadenada (a b c : Nat) (h1 : a = b + 2) (h2 : b ≤ c) :
    a + 1 < c + 5 :=
  calc
    a + 1 = b + 3 := by omega
    _     < b + 5 := by omega
    _     ≤ c + 5 := by omega
```

---

## 6. Modo de Conversión Dirigida (`conv`): Navegación Quirúrgica bajo Ligadores $\lambda$

Cuando necesitas simplificar o reescribir **dentro del cuerpo de una función anónima `fun x => ...`** sin usar `funext` en toda la meta, `conv` te permite entrar bajo el ligador con `ext x`:

```lean
theorem reescribir_bajo_lambda :
    (List.map (fun n : Nat => n + 0) [1, 2, 3]) = [1, 2, 3] := by
  conv =>
    lhs
    arg 1       -- selecciona el primer argumento de `List.map`, que es `fun n => n + 0`
    ext n       -- entra bajo el ligador `fun n => ...`
    rw [Nat.add_zero]
  -- Ahora la meta es `List.map (fun n => n) [1, 2, 3] = [1, 2, 3]`, que es `rfl`!
  rfl
```
