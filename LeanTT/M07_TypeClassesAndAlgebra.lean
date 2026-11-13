/-!
# Módulo 07: Estructuras como Tipos Σ, Clases de Tipos (*Typeclasses*), Coerciones y Álgebra
Guía teórica asociada: `docs/07_estructuras_clases_y_algebra.md`

En este módulo exploramos:
1. Estructuras dependientes y su extensionalidad definicional η.
2. Construcción de una jerarquía algebraica (`Semigroup` → `Monoid` → `Group`).
3. Demostración formal de la unicidad del neutro y de la involución del inverso `(a⁻¹)⁻¹ = a`.
4. Instancias polimórficas (el producto directo `G × H` de dos grupos es un grupo).
5. Coerciones (`CoeSort` y `CoeFun`) para estructuras matemáticas empaquetadas.
-/

namespace LeanTT.M07

universe u v

/-! ## 1. Jerarquía Algebraica con Clases de Tipos (`class`) -/

class Semigrupo (G : Type u) where
  op : G → G → G
  op_assoc : ∀ a b c : G, op (op a b) c = op a (op b c)

infixl:70 " ⋆ " => Semigrupo.op

class Monoide (M : Type u) extends Semigrupo M where
  e : M
  e_op : ∀ a : M, e ⋆ a = a
  op_e : ∀ a : M, a ⋆ e = a

class Grupo (G : Type u) extends Monoide G where
  inv : G → G
  inv_op : ∀ a : G, inv a ⋆ a = e
  op_inv : ∀ a : G, a ⋆ inv a = e

postfix:max "⁻¹" => Grupo.inv

/-! ## 2. Teoremas Generales sobre Cualquier Grupo `G` -/

section TeoriaDeGrupos
variable {G : Type u} [Grupo G]

/-- Teorema de Unicidad del Elemento Neutro en cualquier Monoide/Grupo -/
theorem neutro_unico (e' : G) (h : ∀ a : G, e' ⋆ a = a) : e' = Monoide.e := by
  calc
    e' = e' ⋆ Monoide.e := by rw [Monoide.op_e]
    _  = Monoide.e      := by rw [h]

/-- Ley de cancelación por la izquierda en un Grupo: `a ⋆ b = a ⋆ c → b = c` -/
theorem cancel_izq {a b c : G} (h : a ⋆ b = a ⋆ c) : b = c := by
  calc
    b = Monoide.e ⋆ b   := by rw [Monoide.e_op]
    _ = (a⁻¹ ⋆ a) ⋆ b   := by rw [Grupo.inv_op]
    _ = a⁻¹ ⋆ (a ⋆ b)   := by rw [Semigrupo.op_assoc]
    _ = a⁻¹ ⋆ (a ⋆ c)   := by rw [h]
    _ = (a⁻¹ ⋆ a) ⋆ c   := by rw [← Semigrupo.op_assoc]
    _ = Monoide.e ⋆ c   := by rw [Grupo.inv_op]
    _ = c               := by rw [Monoide.e_op]

/-- El inverso del inverso es el elemento original: `(a⁻¹)⁻¹ = a` -/
theorem inv_inv (a : G) : (a⁻¹)⁻¹ = a := by
  apply cancel_izq (a := a⁻¹)
  rw [Grupo.op_inv, Grupo.inv_op]

/-- Inverso de un producto (antimorfismo): `(a ⋆ b)⁻¹ = b⁻¹ ⋆ a⁻¹` -/
theorem mul_inv_rev (a b : G) : (a ⋆ b)⁻¹ = b⁻¹ ⋆ a⁻¹ := by
  apply cancel_izq (a := a ⋆ b)
  calc
    (a ⋆ b) ⋆ (a ⋆ b)⁻¹
      = Monoide.e               := by rw [Grupo.op_inv]
    _ = a ⋆ a⁻¹                 := by rw [← Grupo.op_inv a]
    _ = a ⋆ (Monoide.e ⋆ a⁻¹)   := by rw [Monoide.e_op]
    _ = a ⋆ ((b ⋆ b⁻¹) ⋆ a⁻¹)   := by rw [Grupo.op_inv b]
    _ = a ⋆ (b ⋆ (b⁻¹ ⋆ a⁻¹))   := by rw [Semigrupo.op_assoc]
    _ = (a ⋆ b) ⋆ (b⁻¹ ⋆ a⁻¹)   := by rw [← Semigrupo.op_assoc]

end TeoriaDeGrupos

/-! ## 3. Síntesis Automática: Producto Directo de Dos Grupos `G × H` -/

instance {G : Type u} {H : Type v} [Grupo G] [Grupo H] : Grupo (G × H) where
  op p q   := (p.1 ⋆ q.1, p.2 ⋆ q.2)
  op_assoc a b c := by
    cases a; cases b; cases c
    simp [Semigrupo.op_assoc]
  e        := (Monoide.e, Monoide.e)
  e_op a   := by cases a; simp [Monoide.e_op]
  op_e a   := by cases a; simp [Monoide.op_e]
  inv a    := (a.1⁻¹, a.2⁻¹)
  inv_op a := by cases a; simp [Grupo.inv_op]
  op_inv a := by cases a; simp [Grupo.op_inv]

/-! ## 4. Coerciones Dependientes (`CoeFun`) en Homomorfismos Empaquetados -/

/-- Un Homomorfismo de Semigrupos empaqueta una función `toFun : G → H`
    con la prueba de que preserva la operación binaria `⋆`. -/
structure HomSemigrupo (G : Type u) (H : Type v) [Semigrupo G] [Semigrupo H] where
  toFun    : G → H
  map_op   : ∀ a b : G, toFun (a ⋆ b) = toFun a ⋆ toFun b

/-- Registramos `CoeFun` para poder escribir `f x` directamente en lugar de `f.toFun x`. -/
instance {G : Type u} {H : Type v} [Semigrupo G] [Semigrupo H] :
    CoeFun (HomSemigrupo G H) (fun _ => G → H) where
  coe f := f.toFun

/-- El homomorfismo identidad -/
def idHom (G : Type u) [Semigrupo G] : HomSemigrupo G G where
  toFun  := fun x => x
  map_op := fun _ _ => rfl

example {G : Type u} [Semigrupo G] (x : G) : (idHom G) x = x := rfl

end LeanTT.M07
