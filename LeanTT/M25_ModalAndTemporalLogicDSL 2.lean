/-!
# Módulo 25: Lógica Modal, Semántica de Kripke y Teoremas de Correspondencia Modal
## Ámbito: Lógicas No Clásicas, Inteligencia Artificial Simbólica y Verificación de Sistemas (Kripke)

En la verificación formal de sistemas concurrentes, protocolos distribuidos y lógica epistémica,
las proposiciones no son simplemente verdaderas o falsas en abstracto, sino que dependen de un
**estado o mundo posible `w : W`** conectado con otros mundos mediante una **relación de
accesibilidad `R : W → W → Prop`** (un **Marco de Kripke**).

En este módulo:
1. Formalizamos Marcos de Kripke (`KripkeFrame W`) y proposiciones modales `ModalProp W := W → Prop`.
2. Definimos los operadores modales $\Box P$ (*necesariamente / en todo estado alcanzable*) y
   $\Diamond P$ (*posiblemente / en algún estado alcanzable*).
3. Demostramos la regla de Necesitación y el **Axioma de Distribución $K$**.
4. **Demostramos los 3 Teoremas Clásicos de Correspondencia de Kripke (Sahlqvist):**
   - El Axioma $T$ ($\Box P \to P$) es válido en un marco $\iff R$ es **reflexiva**.
   - El Axioma $4$ ($\Box P \to \Box\Box P$) es válido en un marco $\iff R$ es **transitiva**.
   - El Axioma $B$ ($P \to \Box\Diamond P$) es válido en un marco $\iff R$ es **simétrica**.
-/

namespace LeanTT.M25

universe u

/-- Un Marco de Kripke consta de un tipo de mundos/estados `W` y una relación de accesibilidad `R` -/
structure KripkeFrame (W : Type u) where
  rel : W → W → Prop

/-- Una proposición modal sobre `W` es un predicado dependiente del mundo `W → Prop` -/
abbrev ModalProp (W : Type u) := W → Prop

namespace ModalProp

variable {W : Type u}

/-- Conectivas puntuales en cada mundo `w : W` -/
def mNot (P : ModalProp W) : ModalProp W := fun w => ¬ P w
def mAnd (P Q : ModalProp W) : ModalProp W := fun w => P w ∧ Q w
def mOr  (P Q : ModalProp W) : ModalProp W := fun w => P w ∨ Q w
def mImp (P Q : ModalProp W) : ModalProp W := fun w => P w → Q w

/-- Operador Modal `□ F P` ("Necesariamente P" / "En toda transición futura"):
    Es verdadero en el mundo `w` si `P v` se cumple en todo mundo `v` accesible desde `w`. -/
def box (F : KripkeFrame W) (P : ModalProp W) : ModalProp W :=
  fun w => ∀ v : W, F.rel w v → P v

/-- Operador Modal `◇ F P` ("Posiblemente P" / "Existe un estado alcanzable donde P"):
    Es verdadero en el mundo `w` si existe algún mundo `v` accesible desde `w` donde se cumple `P v`. -/
def diamond (F : KripkeFrame W) (P : ModalProp W) : ModalProp W :=
  fun w => ∃ v : W, F.rel w v ∧ P v

/-- Validez global en un Marco de Kripke (`⊨ P`): `P` es verdadera en todos los mundos `w : W` -/
def Valid (P : ModalProp W) : Prop :=
  ∀ w : W, P w

prefix:50 "⊨ₘ " => Valid

/-! ## 1. Leyes de la Lógica Modal Normal `K` -/

/-- Regla de Necesitación: Si `P` es globalmente válida (`⊨ₘ P`), entonces `⊨ₘ □ P` -/
theorem necessitation (F : KripkeFrame W) {P : ModalProp W} (h : ⊨ₘ P) :
    ⊨ₘ (box F P) :=
  fun _ v _ => h v

/-- Axioma `K` (Distribución de `□` sobre la implicación):
    `□(P → Q) → (□P → □Q)` es válido en CUALQUIER Marco de Kripke sin importar `R`! -/
theorem axiom_K (F : KripkeFrame W) (P Q : ModalProp W) :
    ⊨ₘ mImp (box F (mImp P Q)) (mImp (box F P) (box F Q)) :=
  fun _ h_imp h_p v hwv => h_imp v hwv (h_p v hwv)

/-! ## 2. Teoremas de Correspondencia Modal de Kripke (Bidireccionales `↔`) -/

/-- TEOREMA DE CORRESPONDENCIA 1 (Axioma `T`: `□P → P` ↔ Reflexividad de `R`):
    El esquema `∀ P, ⊨ₘ (□P → P)` se cumple en el marco `F` si y solo si `F.rel` es reflexiva. -/
theorem correspondence_T (F : KripkeFrame W) :
    (∀ P : ModalProp W, ⊨ₘ mImp (box F P) P) ↔ (∀ w : W, F.rel w w) := by
  constructor
  · -- Dirección (⇒): Instanciamos `P` con el predicado `fun v => F.rel w v`!
    intro hT w
    have hw := hT (fun v => F.rel w v) w
    exact hw (fun v hwv => hwv)
  · -- Dirección (⇐): Si `F.rel` es reflexiva, de `∀ v, F.rel w v → P v` obtenemos `P w` usando `w`:
    intro h_refl P w hbox
    exact hbox w (h_refl w)

/-- TEOREMA DE CORRESPONDENCIA 2 (Axioma `4`: `□P → □□P` ↔ Transitividad de `R`):
    El esquema `∀ P, ⊨ₘ (□P → □□P)` se cumple en `F` si y solo si `F.rel` es transitiva. -/
theorem correspondence_4 (F : KripkeFrame W) :
    (∀ P : ModalProp W, ⊨ₘ mImp (box F P) (box F (box F P))) ↔
    (∀ w v u : W, F.rel w v → F.rel v u → F.rel w u) := by
  constructor
  · -- Dirección (⇒): Instanciamos `P` con `fun z => F.rel w z`
    intro h4 w v u hwv hvu
    have hw := h4 (fun z => F.rel w z) w (fun z hwz => hwz)
    exact hw v hwv u hvu
  · -- Dirección (⇐): Aplicamos la transitividad de `F.rel`
    intro h_trans P w hbox v hwv u hvu
    exact hbox u (h_trans w v u hwv hvu)

/-- TEOREMA DE CORRESPONDENCIA 3 (Axioma `B`: `P → □◇P` ↔ Simetría de `R`):
    El esquema `∀ P, ⊨ₘ (P → □◇P)` se cumple en `F` si y solo si `F.rel` es simétrica. -/
theorem correspondence_B (F : KripkeFrame W) :
    (∀ P : ModalProp W, ⊨ₘ mImp P (box F (diamond F P))) ↔
    (∀ w v : W, F.rel w v → F.rel v w) := by
  constructor
  · -- Dirección (⇒): Instanciamos `P` con la igualdad al mundo inicial `fun z => z = w`
    intro hB w v hwv
    have ⟨u, hvu, huw⟩ := hB (fun z => z = w) w rfl v hwv
    subst huw
    exact hvu
  · -- Dirección (⇐): Si `F.rel w v`, por simetría `F.rel v w`, luego `w` es testigo de `◇P` en `v`
    intro h_symm P w hpw v hwv
    exact ⟨w, h_symm w v hwv, hpw⟩

end ModalProp
end LeanTT.M25
