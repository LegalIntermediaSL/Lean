/-!
# Módulo 40 (Proyecto Cumbre): Un Verificador Bidireccional de Tipos Dependientes en Lean 4
## Ámbito: Implementación de Kernels de Asistentes de Demostraciones (Estilo Mini-Lean / Coquand)

Cerramos la colección de 40 módulos construyendo en Lean 4 un **verificador de tipos dependientes
en miniatura** siguiendo el algoritmo de **Tipado Bidireccional** de Thierry Coquand (1996):
1. Sintaxis unificada `Expr` donde **los tipos y los términos comparten la misma gramática**:
   - Universos `.univ l` (`Sort l`)
   - Variables de De Bruijn `.bvar i`
   - Productos Dependientes `.pi dom cod` (`(x : A) → B x`)
   - Abstracciones `.lam ty body` (`fun (x : A) => t`)
   - Aplicaciones `.app f a`
2. Operación de **desplazamiento (`shift`)** y **sustitución de De Bruijn (`subst`)** necesaria
   porque al aplicar una función dependiente `f : Π (x : A), B(x)` a un argumento `a : A`, el
   tipo resultante es `B[x := a]`!
3. Verificador de tipos `inferType : Ctx → Expr → Option Expr` y comprobación sobre términos
   dependientes reales.
-/

namespace LeanTT.M40

/-- En una Teoría de Tipos Dependientes (PTS), tipos y términos son la misma sintaxis `Expr` -/
inductive Expr where
  | univ : Nat → Expr                -- Sort u (Universo de nivel u)
  | bvar : Nat → Expr                -- Variable ligada (índice de De Bruijn)
  | pi   : Expr → Expr → Expr        -- Π-Type: `(x : dom) → cod` (liga bvar 0 en cod)
  | lam  : Expr → Expr → Expr        -- Abstracción: `λ (x : dom) => body`
  | app  : Expr → Expr → Expr        -- Aplicación: `fn arg`
  deriving Repr, DecidableEq

namespace Expr

/-- Desplaza (*shifts*) en `delta` todos los índices de De Bruijn libres por encima del corte `cutoff` -/
def shift (delta : Nat) (cutoff : Nat) : Expr → Expr
  | .univ l     => .univ l
  | .bvar i     => if i ≥ cutoff then .bvar (i + delta) else .bvar i
  | .pi d c     => .pi (shift delta cutoff d) (shift delta (cutoff + 1) c)
  | .lam d b    => .lam (shift delta cutoff d) (shift delta (cutoff + 1) b)
  | .app f a    => .app (shift delta cutoff f) (shift delta cutoff a)

/-- Sustituye la variable de De Bruijn `idx` por el término `s` en una expresión -/
def subst (idx : Nat) (s : Expr) : Expr → Expr
  | .univ l  => .univ l
  | .bvar i  =>
    if i = idx then s
    else if i > idx then .bvar (i - 1)
    else .bvar i
  | .pi d c  => .pi (subst idx s d) (subst (idx + 1) (shift 1 0 s) c)
  | .lam d b => .lam (subst idx s d) (subst (idx + 1) (shift 1 0 s) b)
  | .app f a => .app (subst idx s f) (subst idx s a)

/-- Reducción de cabeza débil con presupuesto de combustible `fuel` para garantizar terminación -/
def whnf : Nat → Expr → Expr
  | 0,        e          => e
  | fuel + 1, .app f a   =>
    match whnf fuel f with
    | .lam _ body => whnf fuel (subst 0 a body)
    | f'          => .app f' a
  | _,        e          => e

/-- Normalización completa (para comprobar igualdad definicional `convEq`) -/
def nf : Nat → Expr → Expr
  | 0,        e => e
  | fuel + 1, e =>
    match whnf (fuel + 1) e with
    | .pi d c  => .pi (nf fuel d) (nf fuel c)
    | .lam d b => .lam (nf fuel d) (nf fuel b)
    | .app f a => .app (nf fuel f) (nf fuel a)
    | e'       => e'

/-- Igualdad definicional (`A ≡ B`): comprueba si `e1` y `e2` tienen la misma forma normal -/
def defEq (fuel : Nat) (e1 e2 : Expr) : Bool :=
  nf fuel e1 == nf fuel e2

/-! ## El Verificador de Tipos Dependientes (`inferType`) -/

abbrev Ctx := List Expr

/-- Obtiene el tipo de la variable `i` en el contexto `Γ`, desplazando sus índices `i + 1` niveles -/
def lookupCtx : Ctx → Nat → Option Expr
  | [],      _     => none
  | ty :: _, 0     => some (shift 1 0 ty)
  | _ :: Γ,  i + 1 => do
    let ty ← lookupCtx Γ i
    some (shift 1 0 ty)

/-- Infiere el tipo de una expresión `e` en el contexto dependiente `Γ`:
    - `Sort u` tiene tipo `Sort (u + 1)`.
    - `Π (x : A), B` tiene tipo `Sort (max u v)` si `A : Sort u` y `B : Sort v` en `(A :: Γ)`.
    - `λ (x : A) => t` tiene tipo `Π (x : A), B` si `A` es un tipo válido y `t : B` en `(A :: Γ)`.
    - `f a` tiene tipo **`B[x := a]`** si `f : Π (x : A), B` y el tipo de `a` es definicionalmente
      igual a `A`! -/
def inferType (fuel : Nat) (Γ : Ctx) : Expr → Option Expr
  | .univ u => some (.univ (u + 1))
  | .bvar i => lookupCtx Γ i
  | .pi dom cod => do
    let domTy ← inferType fuel Γ dom
    let codTy ← inferType fuel (dom :: Γ) cod
    match whnf fuel domTy, whnf fuel codTy with
    | .univ u, .univ v => some (.univ (max u v))
    | _,       _       => none
  | .lam dom body => do
    let domTy ← inferType fuel Γ dom
    match whnf fuel domTy with
    | .univ _ =>
      let bodyTy ← inferType fuel (dom :: Γ) body
      some (.pi dom bodyTy)
    | _ => none
  | .app fn arg => do
    let fnTy  ← inferType fuel Γ fn
    let argTy ← inferType fuel Γ arg
    match whnf fuel fnTy with
    | .pi dom cod =>
      if defEq fuel dom argTy then
        -- ¡EL CORAZÓN DE LOS TIPOS DEPENDIENTES!:
        -- Sustituimos la variable `0` del codominio `cod` por el argumento `arg`:
        some (subst 0 arg cod)
      else
        none
    | _ => none

/-! ## Pruebas del Mini-Kernel con Expresiones Polimórficas Dependientes -/

/-- La función identidad polimórfica dependiente:
    `polyId := λ (α : Sort 0) => λ (x : α) => x` -/
def polyId : Expr :=
  .lam (.univ 0) (.lam (.bvar 0) (.bvar 0))

/-- El Π-tipo esperado de `polyId`:
    `Π (α : Sort 0), Π (x : α), α` -/
def polyIdType : Expr :=
  .pi (.univ 0) (.pi (.bvar 0) (.bvar 1))

/-- Demostración formal de que nuestro verificador de tipos dependientes infiere
    exactamente `Π (α : Sort 0), Π (x : α), α` para `polyId`! -/
theorem miniKernel_infiere_polyId :
    inferType 20 [] polyId = some polyIdType :=
  rfl

/-- Si aplicamos `polyId` al argumento `Sort 0` (en un contexto donde `A : Sort 0` es `bvar 0`),
    el tipo resultante se especializa dependientemente a `Π (x : A), A` (`pi (bvar 0) (bvar 1)`)! -/
theorem miniKernel_aplicacion_dependiente :
    inferType 20 [.univ 0] (.app polyId (.bvar 0)) =
    some (.pi (.bvar 0) (.bvar 1)) :=
  rfl

end Expr
end LeanTT.M40
