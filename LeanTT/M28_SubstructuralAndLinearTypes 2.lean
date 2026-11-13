/-!
# Módulo 28: Lógica Lineal y Sistemas de Tipos Subestructurales (Estilo Rust Borrow Checker)
## Ámbito: Gestión Segura de Recursos, Punteros Únicos y Criptografía Cuántica

En el cálculo lambda ordinario, una variable `x` puede:
- Usarse **dos o más veces** (Regla de *Contracción*: `fun x => (x, x)`).
- Usarse **cero veces** (Regla de *Debilitamiento*: `fun x => 42`).

En el **Cálculo Lambda Lineal** (Girard, 1987), **cada recurso lineal debe consumirse
exactamente una vez**: no puede duplicarse ni olvidarse sin liberarlo.
En este módulo usamos tipos dependientes para indexar términos por el **consumo exacto**
de cada variable del contexto, haciendo que duplicar u olvidar un recurso lineal sea un
**error de compilación en Lean 4**.
-/

namespace LeanTT.M28

/-- Tipos de nuestro lenguaje lineal -/
inductive LinTy where
  | handle : LinTy             -- Un descriptor de archivo / recurso único
  | lollipop : LinTy → LinTy → LinTy -- Función lineal `A ⊸ B` (consume A exactamente 1 vez)
  | tensor   : LinTy → LinTy → LinTy -- Par lineal `A ⊗ B` (ambos deben consumirse)
  deriving DecidableEq, Repr

infixr:70 " ⊸ " => LinTy.lollipop
infixr:75 " ⊗ " => LinTy.tensor

/-- Estado de una ranura del contexto lineal: `free` (disponible) o `used` (ya consumida) -/
inductive Slot where
  | free : LinTy → Slot
  | used : LinTy → Slot
  deriving DecidableEq, Repr

abbrev LinCtx := List Slot

/-- `ConsumeVar τ Γ1 Γ2` selecciona una variable `free τ` en el contexto de entrada `Γ1`
    y la marca como `used τ` en el contexto de salida `Γ2`, dejando el resto intacto. -/
inductive ConsumeVar : LinTy → LinCtx → LinCtx → Type where
  | here  : {Γ : LinCtx} → {τ : LinTy} →
            ConsumeVar τ (.free τ :: Γ) (.used τ :: Γ)
  | there : {Γ1 Γ2 : LinCtx} → {σ : Slot} → {τ : LinTy} →
            ConsumeVar τ Γ1 Γ2 → ConsumeVar τ (σ :: Γ1) (σ :: Γ2)

/-- Términos Lineales `LinTerm Γ_in Γ_out τ`:
    Un término recibe los recursos disponibles en `Γ_in` y devuelve el estado residual `Γ_out`.
    Observa la regla `.lam`: exige que al terminar el cuerpo de la función, el argumento recién
    introducido haya pasado de `.free σ` a `.used σ`! -/
inductive LinTerm : LinCtx → LinCtx → LinTy → Type where
  | var      : {Γ1 Γ2 : LinCtx} → {τ : LinTy} →
               ConsumeVar τ Γ1 Γ2 → LinTerm Γ1 Γ2 τ
  | lam      : {Γ1 Γ2 : LinCtx} → {σ τ : LinTy} →
               LinTerm (.free σ :: Γ1) (.used σ :: Γ2) τ →
               LinTerm Γ1 Γ2 (σ ⊸ τ)
  | app      : {Γ1 Γ2 Γ3 : LinCtx} → {σ τ : LinTy} →
               LinTerm Γ1 Γ2 (σ ⊸ τ) → LinTerm Γ2 Γ3 σ → LinTerm Γ1 Γ3 τ
  | pair     : {Γ1 Γ2 Γ3 : LinCtx} → {σ τ : LinTy} →
               LinTerm Γ1 Γ2 σ → LinTerm Γ2 Γ3 τ → LinTerm Γ1 Γ3 (σ ⊗ τ)
  | letPair  : {Γ1 Γ2 Γ3 : LinCtx} → {σ1 σ2 τ : LinTy} →
               LinTerm Γ1 Γ2 (σ1 ⊗ σ2) →
               LinTerm (.free σ1 :: .free σ2 :: Γ2) (.used σ1 :: .used σ2 :: Γ3) τ →
               LinTerm Γ1 Γ3 τ

/-! ## Ejemplos de Programas Lineales Verificados por el Sistema de Tipos -/

/-- 1. La Identidad Lineal `λ x. x : A ⊸ A` es VÁLIDA (consume `x` exactamente 1 vez): -/
def linId {A : LinTy} : LinTerm [] [] (A ⊸ A) :=
  .lam (.var .here)

/-- 2. Intercambio Simétrico del Producto Tensorial `λ p. let (x, y) := p in (y, x) : (A ⊗ B) ⊸ (B ⊗ A)`
    Consume el par `p` y luego consume tanto `x` como `y` exactamente una vez: -/
def linSwap {A B : LinTy} : LinTerm [] [] ((A ⊗ B) ⊸ (B ⊗ A)) :=
  .lam (
    .letPair (.var .here) (
      .pair (.var (.there .here)) (.var .here)
    )
  )

/-- 3. Currificación Lineal `(A ⊗ B ⊸ C) ⊸ (A ⊸ B ⊸ C)` -/
def linCurry {A B C : LinTy} : LinTerm [] [] (((A ⊗ B) ⊸ C) ⊸ (A ⊸ (B ⊸ C))) :=
  .lam (.lam (.lam (
    .app (.var (.there (.there .here)))
         (.pair (.var (.there .here)) (.var .here))
  )))

-- NOTA: Si intentáramos escribir el duplicador `λ x. (x, x) : A ⊸ (A ⊗ A)` o la constante
-- `λ x. λ y. x : A ⊸ B ⊸ A`, ¡no compilaría porque el primer `.var .here` cambia el slot
-- de `.free A` a `.used A`, impidiendo un segundo `.var .here`, y dejar `y` en `.free B`
-- impide cerrar el `.lam` que exige `.used B`!

end LeanTT.M28
