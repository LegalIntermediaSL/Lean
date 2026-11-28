# Cuaderno 02: Inducción, Blueprints y Cadenas Ecuacionales `calc` — El Teorema de Nicómaco

> **Jupyter Notebook (`.ipynb`) correspondiente:** [`notebooks/02_induccion_teorema_nicomaco_y_calc.ipynb`](../../notebooks/02_induccion_teorema_nicomaco_y_calc.ipynb)
> **Navegación:** [⬅ Cuaderno 01: Del Papel al Infoview](01_cuaderno_del_papel_al_infoview_paso_a_paso.md) | [Siguiente: Cuaderno 03 (Cuando la Inducción Falla) ➡](03_cuaderno_cuando_la_induccion_falla_generalizacion.md)

---

## 🎯 Objetivo del Cuaderno

Aprender la técnica de **descomposición en *Blueprint* (plano maestro de lemas)** para demostrar identidades inductivas no lineales sin atascarse:
$$0^3 + 1^3 + 2^3 + \dots + n^3 = (0 + 1 + 2 + \dots + n)^2.$$

---

## Celda 1 — Especificación sin Divisiones Truncadas y Test Empírico

> **Lección clave:** En `Nat`, la división `/` redondea hacia abajo (`3 / 2 = 1`). Si defines la fórmula de Gauss como `n * (n + 1) / 2`, toda tu demostración quedará contaminada de lemas de divisibilidad par. Si en cambio trabajas con `2 * sumN n = n * (n + 1)` y `4 * sumCubes n = (n * (n + 1))^2`, trabajas en un **semianillo polinómico limpio** y cancelas el `4` una única vez en la última línea!

```lean
namespace Cuaderno02

def sumN : Nat → Nat
  | 0     => 0
  | n + 1 => sumN n + (n + 1)

def sumCubes : Nat → Nat
  | 0     => 0
  | n + 1 => sumCubes n + (n + 1) * (n + 1) * (n + 1)

-- Comprobamos los primeros 7 valores (0..6):
#eval List.map (fun n => (n, sumCubes n, sumN n * sumN n)) [0, 1, 2, 3, 4, 5, 6]

end Cuaderno02
```

---

## Celda 2 — Escalón 1 del Blueprint: La Identidad de Gauss (`2 * sumN n = n * (n + 1)`)

```lean
namespace Cuaderno02

theorem gauss_sin_division (n : Nat) : 2 * sumN n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    calc
      2 * sumN (k + 1)
        = 2 * sumN k + 2 * (k + 1) := Nat.mul_add 2 (sumN k) (k + 1)
      _ = k * (k + 1) + 2 * (k + 1):= by rw [ih]
      _ = (k + 2) * (k + 1)        := (Nat.add_mul k 2 (k + 1)).symm
      _ = (k + 1) * (k + 2)        := Nat.mul_comm (k + 2) (k + 1)

end Cuaderno02
```

---

## Celda 3 — Escalón 2 del Blueprint: Aislar el Paso Algebraico de Grado 4

Separamos por completo la identidad algebraica pura de la inducción. Al factorizar $s = (k + 1)^2$, todo se reduce a $k^2 + 4(k + 1) = (k + 2)^2$:

```lean
namespace Cuaderno02

theorem paso_algebraico_nicomaco (k : Nat) :
    (k * (k + 1)) * (k * (k + 1)) + 4 * ((k + 1) * (k + 1) * (k + 1)) =
      ((k + 1) * (k + 2)) * ((k + 1) * (k + 2)) := by
  have hQuad : k * k + 4 * (k + 1) = (k + 2) * (k + 2) := by
    calc
      k * k + 4 * (k + 1)
        = k * k + 2 * k + (2 * k + 4) := by omega
      _ = k * (k + 2) + 2 * (k + 2)   := by rw [Nat.mul_add k k 2, Nat.mul_add 2 k 2]; omega
      _ = (k + 2) * (k + 2)           := (Nat.add_mul k 2 (k + 2)).symm
  have sqMul (a b : Nat) : (a * b) * (a * b) = (a * a) * (b * b) := by
    rw [Nat.mul_assoc a b (a * b), ← Nat.mul_assoc b a b, Nat.mul_comm b a,
        Nat.mul_assoc a b b, ← Nat.mul_assoc a a (b * b)]
  let s := (k + 1) * (k + 1)
  have hCube : 4 * (s * (k + 1)) = (4 * (k + 1)) * s := by
    rw [Nat.mul_comm s (k + 1), ← Nat.mul_assoc 4 (k + 1) s]
  calc
    (k * (k + 1)) * (k * (k + 1)) + 4 * ((k + 1) * (k + 1) * (k + 1))
      = (k * k) * s + (4 * (k + 1)) * s           := by rw [sqMul k (k + 1), hCube]
    _ = (k * k + 4 * (k + 1)) * s                 := (Nat.add_mul (k * k) (4 * (k + 1)) s).symm
    _ = ((k + 2) * (k + 2)) * s                   := by rw [hQuad]
    _ = s * ((k + 2) * (k + 2))                   := Nat.mul_comm _ s
    _ = ((k + 1) * (k + 2)) * ((k + 1) * (k + 2)) := (sqMul (k + 1) (k + 2)).symm

end Cuaderno02
```

---

## Celda 4 — Escalón 3 y Teorema Final (`suffices ... by omega`)

```lean
open Cuaderno02

theorem cuatro_sumCubes (n : Nat) :
    4 * sumCubes n = (n * (n + 1)) * (n * (n + 1)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    calc
      4 * sumCubes (k + 1)
        = 4 * sumCubes k + 4 * ((k + 1) * (k + 1) * (k + 1)) := Nat.mul_add 4 _ _
      _ = (k * (k + 1)) * (k * (k + 1)) + 4 * ((k + 1) * (k + 1) * (k + 1)) := by rw [ih]
      _ = ((k + 1) * (k + 2)) * ((k + 1) * (k + 2)) := paso_algebraico_nicomaco k

/-- TEOREMA DE NICÓMACO COMPLETO: ∑ k³ = (∑ k)² -/
theorem teorema_nicomaco (n : Nat) : sumCubes n = sumN n * sumN n := by
  suffices h4 : 4 * sumCubes n = 4 * (sumN n * sumN n) by
    omega
  have hFour : 4 * (sumN n * sumN n) = (2 * sumN n) * (2 * sumN n) := by
    change (2 * 2) * (sumN n * sumN n) = (2 * sumN n) * (2 * sumN n)
    rw [Nat.mul_assoc 2 2 (sumN n * sumN n), ← Nat.mul_assoc 2 (sumN n) (sumN n),
        Nat.mul_comm (2 * sumN n) (sumN n), ← Nat.mul_assoc 2 (sumN n) (2 * sumN n)]
  rw [cuatro_sumCubes n, hFour, gauss_sin_division n]

#print axioms teorema_nicomaco
```

---

👉 **Siguiente cuaderno:** [**Cuaderno 03 — Cuando una Demostración se Atasca: Cómo Diagnosticar y Generalizar Invariantes (`generalizing`)**](03_cuaderno_cuando_la_induccion_falla_generalizacion.md)
