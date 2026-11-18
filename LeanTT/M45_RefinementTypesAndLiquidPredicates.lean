/-!
# Módulo 45: Tipos de Refinamiento (*Refinement Types*), Intervalos Acotados y Aritmética Segura
## Ámbito: Verificación Intrínseca Estilo Liquid Haskell / F* y Programación sin Errores de Ejecución

Un **Tipo de Refinamiento** (Freeman & Pfenning, 1991; Vazou et al., *Liquid Haskell*, 2014) es un
subtipo dependiente `{ x : α // P x }` que refina un tipo base `α` con un predicado lógico `P x : Prop`.
A diferencia de las pruebas extrínsecas (donde primero escribes la función y luego escribes un
teorema aparte), en la **verificación intrínseca con tipos de refinamiento** la función devuelve
en un único paquete tanto el resultado como el certificado formal de que cumple su postcondición.
-/

namespace LeanTT.M45

/-- Tipo de refinamiento de los números naturales estrictamente positivos (`x > 0`) -/
abbrev PosNat := { x : Nat // 0 < x }

/-- Tipo de refinamiento de los enteros en un intervalo cerrado `[lo, hi]` -/
abbrev Interval (lo hi : Nat) := { x : Nat // lo ≤ x ∧ x ≤ hi }

/-- Constructor inteligente (*smart constructor*) para `PosNat` a partir de cualquier `n : Nat` -/
def succPos (n : Nat) : PosNat :=
  ⟨n + 1, by omega⟩

/-- Los números `PosNat` son cerrados bajo la suma: la prueba viaja acoplada al dato -/
def addPos (a b : PosNat) : PosNat :=
  ⟨a.val + b.val, by
    have ha := a.property
    have hb := b.property
    omega⟩

/-- Los números `PosNat` son cerrados bajo el producto -/
def mulPos (a b : PosNat) : PosNat :=
  ⟨a.val * b.val, Nat.mul_pos a.property b.property⟩

/-! ## Operaciones Intrínsecamente Verificadas sobre Intervalos `[lo, hi]` -/

/-- `clamp lo hi h x` recorta `x` al intervalo `[lo, hi]` y **certifica en su propio tipo de retorno**
    que el valor devuelto pertenece a `Interval lo hi`! -/
def clamp (lo hi : Nat) (h_valid : lo ≤ hi) (x : Nat) : Interval lo hi :=
  if h1 : x < lo then
    ⟨lo, by omega⟩
  else if h2 : hi < x then
    ⟨hi, by omega⟩
  else
    ⟨x, by omega⟩

/-- Punto medio verificado `midpoint a b` de dos elementos del intervalo `[lo, hi]`:
    demuestra intrínsecamente que el punto medio jamás se sale del intervalo `[lo, hi]`! -/
def midpoint {lo hi : Nat} (a b : Interval lo hi) : Interval lo hi :=
  ⟨(a.val + b.val) / 2, by
    have ⟨ha1, ha2⟩ := a.property
    have ⟨hb1, hb2⟩ := b.property
    omega⟩

/-- Además, si `x` ya estaba dentro de `[lo, hi]`, `clamp` actúa como la identidad exacta -/
theorem clamp_id_of_mem (lo hi : Nat) (h_valid : lo ≤ hi) (x : Interval lo hi) :
    (clamp lo hi h_valid x.val).val = x.val := by
  dsimp [clamp]
  have ⟨h1, h2⟩ := x.property
  split
  · omega
  · split
    · omega
    · rfl

#eval (clamp 10 50 (by decide) 99).val -- 50
#eval (midpoint (clamp 10 50 (by decide) 12) (clamp 10 50 (by decide) 40)).val -- 26

end LeanTT.M45
