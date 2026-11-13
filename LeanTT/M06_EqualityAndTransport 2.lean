/-!
# Módulo 06: Igualdad de Martin-Löf, Eliminador J (`Eq.rec`), Transporte y Cocientes
Guía teórica asociada: `docs/06_igualdad_transporte_y_hott.md`

En este módulo exploramos:
1. Construcción de la simetría, transitividad y congruencia directamente desde el eliminador `Eq.rec`.
2. Transporte dependiente sobre familias de tipos (`transport` / macro `▸`).
3. Extensionalidad funcional (`funext`) y proposicional (`propext`).
4. Tipos Cociente (`Quot` y `Quotient`): construcción de los Enteros `ℤ` como cociente de `Nat × Nat`.
5. Unicidad de Pruebas de Identidad (UIP / Axioma K).
-/

namespace LeanTT.M06

universe u v

/-! ## 1. El Eliminador J (`Eq.rec`) y Transporte Dependiente -/

/-- Transporte a lo largo de una igualdad en una familia dependiente `P : α → Sort v` -/
def transport {α : Sort u} (P : α → Sort v) {a b : α} (h : a = b) (pa : P a) : P b :=
  Eq.rec (motive := fun x _ => P x) pa h

/-- Simetría de la igualdad derivada únicamente de `transport` -/
theorem eq_symm_from_j {α : Sort u} {a b : α} (h : a = b) : b = a :=
  transport (fun x => x = a) h (Eq.refl a)

/-- Transitividad de la igualdad derivada únicamente de `transport` -/
theorem eq_trans_from_j {α : Sort u} {a b c : α} (h1 : a = b) (h2 : b = c) : a = c :=
  transport (fun x => a = x) h2 h1

/-- Acción de una función sobre caminos / congruencia (`ap` en HoTT, `congrArg` en Lean) -/
theorem ap {α : Sort u} {β : Sort v} (f : α → β) {a b : α} (h : a = b) : f a = f b :=
  transport (fun x => f a = f x) h (Eq.refl (f a))

/-- Demostración de que las leyes de grupoide para caminos (concatenación con `rfl`)
    se cumplen definicionalmente en un extremo: -/
theorem trans_refl_right {α : Type u} {a b : α} (p : a = b) :
    eq_trans_from_j p (Eq.refl b) = p :=
  rfl

/-! ## 2. Extensionalidad Funcional (`funext`) y Proposicional (`propext`) -/

/-- Las funciones `fun n => n + 0` y `fun n => 0 + n` no son definicionalmente iguales
    como términos abiertos, pero son proposicionalmente iguales por `funext`. -/
theorem suma_cero_fun_eq : (fun n : Nat => n + 0) = (fun n : Nat => 0 + n) := by
  funext n
  omega

/-- Por `propext`, dos proposiciones lógicamente equivalentes son iguales (`P = Q`) -/
theorem and_comm_eq (P Q : Prop) : (P ∧ Q) = (Q ∧ P) :=
  propext ⟨fun ⟨hp, hq⟩ => ⟨hq, hp⟩, fun ⟨hq, hp⟩ => ⟨hp, hq⟩⟩

/-! ## 3. Construcción de `ℤ` como Tipo Cociente de `(Nat × Nat)` (Construcción de Grothendieck) -/

/-- Representamos un entero como la diferencia formal `(a, b) ↦ a - b`.
    Dos pares `(a, b)` y `(c, d)` representan el mismo entero si y solo si `a + d = b + c`. -/
def IntRel (p q : Nat × Nat) : Prop :=
  p.1 + q.2 = p.2 + q.1

theorem intRel_refl (p : Nat × Nat) : IntRel p p := by
  dsimp [IntRel]; omega

theorem intRel_symm {p q : Nat × Nat} (h : IntRel p q) : IntRel q p := by
  dsimp [IntRel] at *; omega

theorem intRel_trans {p q r : Nat × Nat} (h1 : IntRel p q) (h2 : IntRel q r) : IntRel p r := by
  dsimp [IntRel] at *; omega

/-- Empaquetamos la relación de equivalencia en un `Setoid (Nat × Nat)` -/
instance intSetoid : Setoid (Nat × Nat) where
  r     := IntRel
  iseqv := ⟨intRel_refl, intRel_symm, intRel_trans⟩

/-- El tipo cociente `MiInt := Quotient intSetoid` -/
abbrev MiInt := Quotient intSetoid

/-- Constructor de un entero a partir de dos naturales `a - b` -/
def mkInt (a b : Nat) : MiInt :=
  Quotient.mk intSetoid (a, b)

/-- En el cociente, `(3, 1)` y `(10, 8)` (ambos iguales a `+2`) son **iguales** (`=`) -/
theorem dos_eq_dos : mkInt 3 1 = mkInt 10 8 :=
  Quotient.sound (by dsimp [HasEquiv.Equiv, Setoid.r, IntRel]; omega)

/-- Elevación de la negación `(a, b) ↦ (b, a)` al tipo cociente `MiInt → MiInt`,
    demostrando que respeta la relación de equivalencia. -/
def negInt : MiInt → MiInt :=
  Quotient.lift
    (fun (p : Nat × Nat) => mkInt p.2 p.1)
    (fun a b (h : IntRel a b) => Quotient.sound (by
      dsimp [HasEquiv.Equiv, Setoid.r, IntRel] at *
      omega))

/-- La reducción en `Quotient.lift` sobre un representante concreto es definicional (`rfl`) -/
example : negInt (mkInt 5 2) = mkInt 2 5 := rfl

end LeanTT.M06
