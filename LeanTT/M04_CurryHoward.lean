/-!
# Módulo 04: El Isomorfismo de Curry-Howard — Lógica Constructiva vs. Lógica Clásica
Guía teórica asociada: `docs/04_curry_howard_y_logica.md`

En este módulo exploramos:
1. Tautologías proposicionales demostradas como términos lambda puros.
2. Cuantificadores universales (`Π`) y existenciales (`Σ` en `Prop`) como términos puros.
3. Leyes de De Morgan constructivas vs. clásicas.
4. Teorema de Glivenko (`¬¬(P ∨ ¬P)`) demostrado sin axiomas clásicos.
5. Lógica clásica (`Classical.em`, `Classical.byContradiction`, Ley de Peirce).
-/

namespace LeanTT.M04

variable {P Q R : Prop}
variable {α : Type} {A B : α → Prop}

/-! ## 1. Lógica Proposicional Intuicionista como Términos Lambda Puros -/

/-- Implicación reflexiva = Combinador `I` -/
theorem imp_refl : P → P :=
  fun hp => hp

/-- Debilitamiento = Combinador `K` -/
theorem imp_weakening : P → Q → P :=
  fun hp _ => hp

/-- Distributividad de la implicación = Combinador `S` -/
theorem imp_dist : (P → Q → R) → (P → Q) → P → R :=
  fun hpqr hpq hp => hpqr hp (hpq hp)

/-- Conmutatividad y asociatividad de la conjunción (`∧`) -/
theorem and_comm_pure : P ∧ Q ↔ Q ∧ P :=
  ⟨fun ⟨hp, hq⟩ => ⟨hq, hp⟩, fun ⟨hq, hp⟩ => ⟨hp, hq⟩⟩

theorem and_assoc_pure : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) :=
  ⟨fun ⟨⟨hp, hq⟩, hr⟩ => ⟨hp, ⟨hq, hr⟩⟩,
   fun ⟨hp, ⟨hq, hr⟩⟩ => ⟨⟨hp, hq⟩, hr⟩⟩

/-- Distributividad de `∧` sobre `∨` usando términos lambda puros -/
theorem and_or_distrib : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
  Iff.intro
    (fun ⟨hp, hqr⟩ =>
      match hqr with
      | Or.inl hq => Or.inl ⟨hp, hq⟩
      | Or.inr hr => Or.inr ⟨hp, hr⟩)
    (fun h =>
      match h with
      | Or.inl ⟨hp, hq⟩ => ⟨hp, Or.inl hq⟩
      | Or.inr ⟨hp, hr⟩ => ⟨hp, Or.inr hr⟩)

/-! ## 2. Negación Constructiva, Contraposición y el Teorema de Glivenko -/

/-- Introducción de la doble negación (`P → ¬¬P`):
    Es simplemente la evaluación inversa `λ x f => f x`. -/
theorem dni : P → ¬¬P :=
  fun hp hnp => hnp hp

/-- Contraposición constructiva: `(P → Q) → (¬Q → ¬P)`
    Es simplemente la composición de funciones. -/
theorem contrapositive : (P → Q) → (¬Q → ¬P) :=
  fun hpq hnq hp => hnq (hpq hp)

/-- Reducción de la triple negación a negación simple (`¬¬¬P ↔ ¬P`)
    ¡100% constructivo! -/
theorem triple_neg : ¬¬¬P ↔ ¬P :=
  ⟨fun hnnnp hp => hnnnp (dni hp), dni⟩

/-- Teorema de Glivenko para el Tercio Excluso: `¬¬(P ∨ ¬P)`
    Aunque `P ∨ ¬P` no es demostrable constructivamente, su doble negación sí lo es. -/
theorem double_neg_excluded_middle : ¬¬(P ∨ ¬P) :=
  fun (h : ¬(P ∨ ¬P)) =>
    have hnp : ¬P := fun hp => h (Or.inl hp)
    h (Or.inr hnp)

/-! ## 3. Las Cuatro Leyes de De Morgan (3 Constructivas + 1 Clásica) -/

/-- Ley de De Morgan 1 (Constructiva): `¬(P ∨ Q) ↔ ¬P ∧ ¬Q` -/
theorem de_morgan_not_or : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
  Iff.intro
    (fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩)
    (fun ⟨hnp, hnq⟩ hpq =>
      match hpq with
      | Or.inl hp => hnp hp
      | Or.inr hq => hnq hq)

/-- Ley de De Morgan 2 (Dirección Constructiva): `¬P ∨ ¬Q → ¬(P ∧ Q)` -/
theorem de_morgan_or_not_imp_not_and : ¬P ∨ ¬Q → ¬(P ∧ Q) :=
  fun h ⟨hp, hq⟩ =>
    match h with
    | Or.inl hnp => hnp hp
    | Or.inr hnq => hnq hq

/-! ## 4. Cuantificadores de Primer Orden (Π y Σ en `Prop`) -/

/-- Intercambio de cuantificadores universales -/
theorem forall_comm {R : α → α → Prop} : (∀ x y, R x y) → (∀ y x, R x y) :=
  fun h y x => h x y

/-- Un existencial implica un universal: `(∃ x, ∀ y, R x y) → (∀ y, ∃ x, R x y)` -/
theorem exists_forall_imp_forall_exists {R : α → α → Prop} :
    (∃ x, ∀ y, R x y) → (∀ y, ∃ x, R x y) :=
  fun ⟨x, hx⟩ y => ⟨x, hx y⟩

/-- De Morgan constructiva para cuantificadores: `(¬∃ x, A x) ↔ (∀ x, ¬A x)` -/
theorem not_exists_iff_forall_not : (¬∃ x, A x) ↔ (∀ x, ¬A x) :=
  Iff.intro
    (fun hne x hax => hne ⟨x, hax⟩)
    (fun hfa ⟨x, hax⟩ => hfa x hax)

/-! ## 5. Lógica Clásica con `Classical.em` -/

/-- Eliminación de la Doble Negación (`¬¬P → P`) usando el Tercio Excluso `Classical.em` -/
theorem dne (h : ¬¬P) : P :=
  match Classical.em P with
  | Or.inl hp  => hp
  | Or.inr hnp => False.elim (h hnp)

/-- Ley de Peirce: `((P → Q) → P) → P` -/
theorem peirce : ((P → Q) → P) → P :=
  fun hpqp =>
    match Classical.em P with
    | Or.inl hp  => hp
    | Or.inr hnp => hpqp (fun hp => False.elim (hnp hp))

/-- Dirección clásica de De Morgan: `¬(P ∧ Q) → ¬P ∨ ¬Q` -/
theorem de_morgan_not_and_classical (h : ¬(P ∧ Q)) : ¬P ∨ ¬Q :=
  match Classical.em P with
  | Or.inl hp  => Or.inr (fun hq => h ⟨hp, hq⟩)
  | Or.inr hnp => Or.inl hnp

end LeanTT.M04
