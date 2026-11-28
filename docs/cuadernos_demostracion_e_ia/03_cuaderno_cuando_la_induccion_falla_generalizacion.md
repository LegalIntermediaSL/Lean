# Cuaderno 03: Cuando una Demostración se Atasca — Generalización de Invariantes (`generalizing`)

> **Jupyter Notebook (`.ipynb`) correspondiente:** [`notebooks/03_generalizacion_invariantes_y_acumuladores.ipynb`](../../notebooks/03_generalizacion_invariantes_y_acumuladores.ipynb)
> **Navegación:** [⬅ Cuaderno 02: Teorema de Nicómaco](02_cuaderno_induccion_nicomaco_y_calc.md) | [Siguiente: Cuaderno 04 (Bucle IA ↔ Compilador) ➡](04_cuaderno_bucle_ia_compilador_autoreparacion.md)

---

## 🎯 Objetivo del Cuaderno

El momento más formativo al aprender Lean 4 (y el obstáculo más frecuente para un LLM) ocurre cuando intentas demostrar un teorema verdadero por inducción directa y **la hipótesis inductiva resulta demasiado particular para aplicarse**.

En este cuaderno veremos el problema en acción con dos algoritmos reales con acumulador (`fastRev` en listas y `sumTail` en números) y la receta universal para desbloquearlos.

---

## Celda 1 — El Algoritmo Rápido `fastRev` ($O(n)$) frente al Ingenuo `reverse`

Invertir una lista concatenando al final en cada paso cuesta $O(n^2)$. La versión funcional eficiente en tiempo lineal $O(n)$ usa una función auxiliar recursiva de cola `revAcc xs acc` que va apilando elementos en un acumulador `acc`:

```lean
namespace Cuaderno03

def revAcc {α : Type} : List α → List α → List α
  | [],      acc => acc
  | x :: xs, acc => revAcc xs (x :: acc)

def fastRev {α : Type} (xs : List α) : List α :=
  revAcc xs []

#eval fastRev ["Lean 4", "Tipos", "Dependientes", "IA"]

end Cuaderno03
```

---

## Celda 2 — Anatomía del Bloqueo: ¿Por Qué Falla la Inducción Directa?

Si intentamos demostrar directamente `theorem intento_ingenuo (xs : List α) : revAcc xs [] = xs.reverse` haciendo `induction xs`, Lean muestra en el paso inductivo `cons x rest ih` este **Infoview bloqueado**:

```text
α : Type
x : α
rest : List α
ih : revAcc rest [] = rest.reverse          ◀── ¡`ih` SOLO habla del acumulador vacío `[]`!
⊢ revAcc rest [x] = rest.reverse ++ [x]     ◀── ¡Pero la meta tiene `revAcc rest [x]` (no vacío)!
```

Observa el diagnóstico: **`ih` tiene el segundo argumento congelado en `[]`**, mientras que la definición de `revAcc (x :: rest) []` llama a `revAcc rest [x]` cambiando el acumulador a `[x]`. Ninguna táctica puede reescribir `revAcc rest [x]` usando `ih` porque `[] ≠ [x]`!

---

## Celda 3 — La Solución Universal: Descubrir el Invariante General y Usar `generalizing`

Pregúntate siempre: **¿qué calcula `revAcc xs acc` para un acumulador `acc` arbitrario?**
¡Calcula `xs.reverse ++ acc`! Y al añadir `generalizing acc` a `induction xs`, nuestra hipótesis inductiva se convierte en una **fórmula universalmente cuantificada** `∀ (acc : List α), revAcc rest acc = rest.reverse ++ acc`, que podemos instanciar con `ih (x :: acc)`!

```lean
namespace Cuaderno03

theorem revAcc_invariant {α : Type} (xs acc : List α) :
    revAcc xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil =>
    -- Caso base: `revAcc [] acc = [] ++ acc`, ambos son `acc`
    simp [revAcc]
  | cons x rest ih =>
    -- Ahora `ih : ∀ (acc : List α), revAcc rest acc = rest.reverse ++ acc`!
    calc
      revAcc (x :: rest) acc
        = revAcc rest (x :: acc)       := rfl
      _ = rest.reverse ++ (x :: acc)   := ih (x :: acc)
      _ = (rest.reverse ++ [x]) ++ acc := by simp [List.append_assoc]
      _ = (x :: rest).reverse ++ acc   := by simp [List.reverse_cons]

/-- Y ahora el teorema original sale en dos líneas como corolario para `acc = []`! -/
theorem fastRev_correct {α : Type} (xs : List α) :
    fastRev xs = xs.reverse := by
  dsimp [fastRev]
  rw [revAcc_invariant, List.append_nil]

end Cuaderno03
```

---

## Celda 4 — Segundo Ejemplo Práctico: Suma en Recursión de Cola (`sumTail`)

Apliquemos exactamente la misma receta a un acumulador numérico `sumAcc n acc`:

```lean
namespace Cuaderno03

def sumPure : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sumPure n

def sumAcc : Nat → Nat → Nat
  | 0,     acc => acc
  | n + 1, acc => sumAcc n (acc + (n + 1))

-- Invariante para todo acumulador `acc`: `sumAcc n acc = acc + sumPure n`
theorem sumAcc_invariant (n acc : Nat) :
    sumAcc n acc = acc + sumPure n := by
  induction n generalizing acc with
  | zero =>
    rfl
  | succ k ih =>
    dsimp [sumAcc, sumPure]
    rw [ih (acc + (k + 1))]
    omega

theorem sumAcc_zero_eq_sumPure (n : Nat) :
    sumAcc n 0 = sumPure n := by
  rw [sumAcc_invariant, Nat.zero_add]

#eval (sumAcc 100 0, sumPure 100) -- (5050, 5050)

end Cuaderno03
```

---

👉 **Siguiente cuaderno:** [**Cuaderno 04 — Trazas Reales del Bucle IA ↔ Compilador: Cómo se Auto-Repara una IA en Lean 4**](04_cuaderno_bucle_ia_compilador_autoreparacion.md)
