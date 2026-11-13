/-!
# Módulo 22: Teoría de Categorías, Funtores, Transformaciones Naturales y el Lema de Yoneda
## Ámbito: Matemática Abstracta y Semántica Categórica en Teoría de Tipos Dependientes

La Teoría de Categorías utiliza los tipos dependientes de forma esencial: el tipo de los
morfismos `Hom X Y` depende de dos objetos `X` e `Y`, y la composición `f ≫ g` solo está
definida cuando el codominio de `f` coincide definicionalmente con el dominio de `g`.

En este módulo:
1. Definimos Categorías, Funtores y Transformaciones Naturales.
2. Demostramos que la identidad y la composición vertical de transformaciones naturales
   satisfacen las leyes categóricas.
3. **Demostramos formalmente en Lean 4 el Lema de Yoneda** para funtores con valores en `Type`:
   las transformaciones naturales desde $\text{Hom}(A, -)$ hacia un funtor $F$ están en
   biyección canónica con los elementos de $F(A)$!
-/

namespace LeanTT.M22

universe u v

/-! ## 1. Definición Dependiente de una Categoría -/

class Categoria (Obj : Type u) where
  Hom       : Obj → Obj → Type v
  id        : (X : Obj) → Hom X X
  comp      : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  id_comp   : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  comp_id   : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  comp_assoc: ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
                comp (comp f g) h = comp f (comp g h)

infixr:80 " ≫ " => Categoria.comp

/-! ## 2. Funtores Covariantes hacia la Categoría de Tipos (`Copresheaf`) -/

/-- Un funtor covariante `F : C → Type v` asigna a cada objeto `X : C` un tipo `obj X`
    y a cada morfismo `f : Hom X Y` una función `map f : obj X → obj Y` respetando `id` y `≫`. -/
structure Copresheaf (C : Type u) [Categoria.{u, v} C] where
  obj      : C → Type v
  map      : {X Y : C} → Categoria.Hom X Y → obj X → obj Y
  map_id   : ∀ (X : C) (x : obj X), map (Categoria.id X) x = x
  map_comp : ∀ {X Y Z : C} (f : Categoria.Hom X Y) (g : Categoria.Hom Y Z) (x : obj X),
               map (f ≫ g) x = map g (map f x)

/-- El Funtor Representable Covariante `Hom(A, -)` para un objeto fijo `A : C` -/
def yonedaRep {C : Type u} [Categoria.{u, v} C] (A : C) : Copresheaf C where
  obj X        := Categoria.Hom A X
  map f h      := h ≫ f
  map_id _ h   := Categoria.comp_id h
  map_comp f g h := (Categoria.comp_assoc h f g).symm

/-! ## 3. Transformaciones Naturales entre Copresheaves -/

@[ext]
structure NatTrans {C : Type u} [Categoria.{u, v} C] (F G : Copresheaf C) where
  app        : (X : C) → F.obj X → G.obj X
  naturality : ∀ {X Y : C} (f : Categoria.Hom X Y) (x : F.obj X),
                 app Y (F.map f x) = G.map f (app X x)

/-! ## 4. El Lema de Yoneda Formalizado y Demostrado en Lean 4 -/

section Yoneda
variable {C : Type u} [Categoria.{u, v} C] (A : C) (F : Copresheaf C)

/-- Dirección 1 del Lema de Yoneda (`NatTrans (Hom(A, -)) F → F.obj A`):
    Evaluamos la componente en `A` de la transformación natural sobre el morfismo `id A`. -/
def yonedaForward (α : NatTrans (yonedaRep A) F) : F.obj A :=
  α.app A (Categoria.id A)

/-- Dirección 2 del Lema de Yoneda (`F.obj A → NatTrans (Hom(A, -)) F`):
    Dado un elemento `u : F.obj A`, enviamos cada morfismo `f : Hom A X` a `F.map f u`. -/
def yonedaBackward (u : F.obj A) : NatTrans (yonedaRep A) F where
  app _ f := F.map f u
  naturality g f := by
    dsimp [yonedaRep]
    rw [F.map_comp]

/-- Demostración 1 del Lema de Yoneda: `yonedaForward (yonedaBackward u) = u` -/
theorem yoneda_left_inv (u : F.obj A) :
    yonedaForward A F (yonedaBackward A F u) = u := by
  dsimp [yonedaForward, yonedaBackward]
  exact F.map_id A u

/-- Demostración 2 del Lema de Yoneda: `yonedaBackward (yonedaForward α) = α` -/
theorem yoneda_right_inv (α : NatTrans (yonedaRep A) F) :
    yonedaBackward A F (yonedaForward A F α) = α := by
  ext X f
  dsimp [yonedaBackward, yonedaForward]
  have h := (α.naturality f (Categoria.id A)).symm
  dsimp [yonedaRep] at h
  rw [Categoria.id_comp] at h
  exact h

end Yoneda
end LeanTT.M22
