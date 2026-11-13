/-!
# Módulo 03: Jerarquía de Universos (`Sort u`), `Prop`, Impredicatividad y Subsingletons
Guía teórica asociada: `docs/03_jerarquia_universos_y_prop.md`

En este módulo exploramos:
1. La cadena `Prop : Type 0 : Type 1 : Type 2 ...` (`Sort u`).
2. Polimorfismo de universos (`universe u v`) y elevación explícita (`ULift`).
3. Impredicatividad de `Prop` frente a la predicatividad de `Type u` (`imax`).
4. Irrelevancia de prueba (*Proof Irrelevance*) por reflexividad (`rfl`).
5. Eliminación de subsingletons: qué tipos en `Prop` pueden eliminarse hacia `Type`.
-/

namespace LeanTT.M03

universe u v

/-! ## 1. Inspección de la Jerarquía `Sort u` -/

-- `Prop` es un sinónimo sintáctico de `Sort 0`
example : Prop = Sort 0 := rfl

-- `Type` (o `Type 0`) es un sinónimo sintáctico de `Sort 1`
example : Type 0 = Sort 1 := rfl

-- `Type 1` es un sinónimo sintáctico de `Sort 2`
example : Type 1 = Sort 2 := rfl

#check (Prop : Type 0)
#check (Type 0 : Type 1)
#check (Type 1 : Type 2)

/-! ## 2. Polimorfismo de Universos y `ULift` -/

/-- Una lista o función identidad polimórfica en el nivel de universo `u`
    puede aplicarse tanto a `Nat : Type 0` como a `Type 0 : Type 1`. -/
def idUniv (α : Sort u) (a : α) : α := a

#check idUniv Nat 5          -- Nat
#check idUniv (Type 0) Nat   -- Type
#check idUniv Prop True      -- Prop

/-- Como Lean no tiene cumulatividad implícita, `ULift.{v, u}` eleva un tipo `α : Type u`
    al universo `Type (max u v)` mediante una estructura envoltorio `{ down : α }`. -/
def elevarAType1 (n : Nat) : ULift.{1, 0} Nat :=
  ULift.up n

example (n : Nat) : (elevarAType1 n).down = n := rfl

/-! ## 3. Impredicatividad de `Prop` vs. Predicatividad de `Type` -/

-- En `Type`, cuantificar sobre `Type 0` sube el nivel del universo a `Type 1`:
#check ((α : Type 0) → α → α : Type 1)

/-- En cambio, en `Prop`, cuantificar sobre cualquier `Type u` (¡o sobre todos los `Prop`!)
    permanece dentro de `Prop` (`Sort 0`) gracias a `imax(u, 0) = 0`: -/
def TodoTipoTieneIdentidad : Prop :=
  ∀ (α : Type 5) (x : α), x = x

def ImpredicativaSobreProp : Prop :=
  ∀ (P : Prop), P → P

theorem prueba_impredicativa : ImpredicativaSobreProp :=
  fun _ hp => hp

/-! ## 4. Irrelevancia de Prueba (*Proof Irrelevance*) -/

/-- En Lean 4, cualesquiera dos demostraciones `p1` y `p2` de una misma proposición `P : Prop`
    son definicionalmente iguales en el kernel. -/
theorem irrelevancia_de_prueba {P : Prop} (p1 p2 : P) : p1 = p2 :=
  rfl

/-- Consecuencia: si dos subtipos `{ x : α // P x }` tienen el mismo valor `.val`,
    son iguales aunque sus pruebas se hayan construido de manera distinta. -/
theorem subtype_ext {α : Type u} {P : α → Prop} {a b : { x : α // P x }}
    (h : a.val = b.val) : a = b := by
  cases a
  cases b
  simp at h
  subst h
  rfl

/-! ## 5. Eliminación de `Prop` hacia `Type` (Subsingleton Elimination) -/

/-- `False` tiene 0 constructores (es un subsingleton), por lo que puede eliminarse
    para producir un habitante de cualquier `Sort u` (Ex Falso Quodlibet computacional). -/
def exFalsoComputacional {α : Sort u} (h : False) : α :=
  False.elim h

/-- `And P Q` tiene un único constructor cuyos campos son ambos `Prop`, por lo que
    también permite eliminación hacia `Type`. -/
def extraerDeAnd (h : (1 = 1) ∧ (2 = 2)) : Nat :=
  match h with
  | ⟨_, _⟩ => 100

/-- `Nonempty α : Prop` afirma que el tipo `α` tiene al menos un elemento,
    pero borra computacionalmente cuál es ese elemento. -/
example : Nonempty Nat :=
  ⟨0⟩

end LeanTT.M03
