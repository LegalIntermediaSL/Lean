/-!
# Módulo 41: Control de Flujo de Información y el Teorema de No-Interferencia
## Ámbito: Seguridad Basada en Lenguajes, Tipos de Confidencialidad y Criptografía de Sistemas

En un sistema de tipos convencional, los tipos garantizan que no habrá errores de memoria o de
operaciones inválidas, pero no impiden que un programa filtre una clave privada en un registro
público.
Los **Sistemas de Tipos de Flujo de Información** (Denning, 1976; Volpano, Smith & Irvine, 1996)
etiquetan cada variable y expresión con un nivel de un **retículo de seguridad**
($\mathsf{Public} \sqsubseteq \mathsf{Secret}$) para garantizar estáticamente el
**Teorema de No-Interferencia** (Goguen & Meseguer, 1982):
> *Variar arbitrariamente las entradas secretas ($\mathsf{Secret}$) jamás altera el resultado de
> ninguna expresión clasificada como pública ($\mathsf{Public}$).*
-/

namespace LeanTT.M41

/-- Retículo de seguridad de dos niveles: `pub` (Bajo / Público) y `sec` (Alto / Secreto) -/
inductive SecLevel where
  | pub : SecLevel
  | sec : SecLevel
  deriving Repr, DecidableEq

namespace SecLevel

/-- Supremo (`join` / `⊔`) en el retículo de confidencialidad:
    cualquier combinación que involucre un dato secreto produce un resultado secreto. -/
@[simp]
def join : SecLevel → SecLevel → SecLevel
  | .pub, .pub => .pub
  | _,    _    => .sec

infixl:65 " ⊔ₛ " => SecLevel.join

/-- Orden parcial del retículo de seguridad (`l1 ⊑ₛ l2`):
    la información puede fluir de `pub` a `sec`, pero NUNCA de `sec` a `pub`. -/
@[simp]
def flowsTo : SecLevel → SecLevel → Prop
  | .pub, _    => True
  | .sec, .sec => True
  | .sec, .pub => False

infix:50 " ⊑ₛ " => SecLevel.flowsTo

/-- Lema clave del retículo: `l1 ⊔ₛ l2 = .pub` si y solo si ambos niveles son `.pub`! -/
theorem join_eq_pub_iff (l1 l2 : SecLevel) :
    (l1 ⊔ₛ l2) = .pub ↔ (l1 = .pub ∧ l2 = .pub) := by
  cases l1 <;> cases l2 <;> decide

end SecLevel

/-! ## Lenguaje de Expresiones con Tipado Estático de Confidencialidad -/

inductive SecExpr where
  | const : Int → SecExpr
  | var   : String → SecExpr
  | add   : SecExpr → SecExpr → SecExpr
  | mul   : SecExpr → SecExpr → SecExpr
  deriving Repr, DecidableEq

/-- Contexto de seguridad `Γ` que asigna a cada variable su nivel `.pub` o `.sec` -/
abbrev SecCtx := String → SecLevel

/-- Memoria de ejecución `m` que asigna a cada variable su valor entero -/
abbrev SecMem := String → Int

/-- Evaluador denotacional estándar -/
@[simp]
def evalSec (m : SecMem) : SecExpr → Int
  | .const c   => c
  | .var x     => m x
  | .add e1 e2 => evalSec m e1 + evalSec m e2
  | .mul e1 e2 => evalSec m e1 * evalSec m e2

/-- Verificador estático de flujo de información (`inferSec Γ e`):
    calcula la etiqueta de confidencialidad mínima de la expresión `e` bajo `Γ`. -/
@[simp]
def inferSec (Γ : SecCtx) : SecExpr → SecLevel
  | .const _   => .pub
  | .var x     => Γ x
  | .add e1 e2 => inferSec Γ e1 ⊔ₛ inferSec Γ e2
  | .mul e1 e2 => inferSec Γ e1 ⊔ₛ inferSec Γ e2

/-! ## Indistinguibilidad Pública (`LowEquiv`) y el Teorema de No-Interferencia -/

/-- Dos memorias `m1` y `m2` son **públicamente indistinguibles** bajo `Γ` (`LowEquiv Γ m1 m2`)
    si coinciden en todas las variables públicas (`Γ x = .pub`), aunque difieran en las secretas! -/
def LowEquiv (Γ : SecCtx) (m1 m2 : SecMem) : Prop :=
  ∀ x : String, Γ x = .pub → m1 x = m2 x

theorem lowEquiv_refl (Γ : SecCtx) (m : SecMem) : LowEquiv Γ m m :=
  fun _ _ => rfl

theorem lowEquiv_symm {Γ : SecCtx} {m1 m2 : SecMem} (h : LowEquiv Γ m1 m2) :
    LowEquiv Γ m2 m1 :=
  fun x hx => (h x hx).symm

/-- TEOREMA FUNDAMENTAL DE NO-INTERFERENCIA (*Non-Interference Theorem*):
    Si el verificador de tipos certifica que una expresión `e` es pública (`inferSec Γ e = .pub`),
    entonces para cualesquiera dos memorias `m1` y `m2` que coincidan en las variables públicas,
    ¡evaluar `e` en `m1` y en `m2` produce **exactamente el mismo resultado**!
    Ningún bit de las variables `.sec` puede filtrarse al resultado de `e`. -/
theorem non_interference (Γ : SecCtx) (e : SecExpr) (m1 m2 : SecMem)
    (h_low : LowEquiv Γ m1 m2)
    (h_pub : inferSec Γ e = .pub) :
    evalSec m1 e = evalSec m2 e := by
  induction e with
  | const c =>
    rfl
  | var x =>
    exact h_low x h_pub
  | add e1 e2 ih1 ih2 =>
    dsimp [inferSec] at h_pub
    rcases (SecLevel.join_eq_pub_iff _ _).mp h_pub with ⟨h1, h2⟩
    dsimp [evalSec]
    rw [ih1 h1, ih2 h2]
  | mul e1 e2 ih1 ih2 =>
    dsimp [inferSec] at h_pub
    rcases (SecLevel.join_eq_pub_iff _ _).mp h_pub with ⟨h1, h2⟩
    dsimp [evalSec]
    rw [ih1 h1, ih2 h2]

end LeanTT.M41
