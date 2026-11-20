/-!
# Módulo 60 (Tercer Proyecto Cumbre): Mini-Kernel con Jerarquía de Universos `Sort u`, `imax` y *Large Elimination*
## Ámbito: Arquitectura Nuclear de Lean 4 (Ampliación de `M40` y `M50` con Polimorfismo de Universos e Inductivos)

En el **Módulo 40** construimos un verificador nuclear con un único universo `Type`, y en el
**Módulo 50** construimos su elaborador bidireccional.
Para completar la trilogía de arquitectura interna de **Lean 4**, en este **Módulo 60** ampliamos
el Kernel para soportar las dos características más sutiles del **Cálculo de Construcciones Inductivas (CIC)**:

1. **La Jerarquía Infinita de Universos `Sort u` (`u : Nat`) y la Función `imax`:**
   - `Sort 0` es **`Prop`** (el universo impredicativo de las proposiciones).
   - `Sort (u + 1)` es **`Type u`** (los universos predicativos de datos).
   - Para todo nivel `u`, el tipo de `Sort u` es `Sort (u + 1)`.
   - Si `A : Sort u` y `B : Sort v`, entonces el producto dependiente `Π (x : A), B` vive en
     `Sort (imaxLevel u v)`, donde `imaxLevel u 0 = 0` (impredicatividad de `Prop`) y
     `imaxLevel u (v + 1) = max u (v + 1)` (predicatividad de `Type v`).
2. **Eliminación Dependiente Booleana (`boolRec` / $\iota$-reducción y *Large Elimination*):**
   - El eliminador `boolRec motive tFalse tTrue scrut` permite que el motivo `motive : Bool → Sort u`
     aterrice en `Type 0` (`Sort 1`), calculando un **tipo distinto** para `false` y para `true`
     dentro del propio kernel!
-/

namespace LeanTT.M60

/-- Función `imax` del kernel de Lean 4 sobre niveles de universo `Nat`:
    - Si el codominio vive en `Sort 0` (`Prop`), todo el producto dependiente `Π x : A, B`
      aterriza en `Sort 0` (`Prop`), sin importar cuán grande sea el universo `u` del dominio `A`!
    - Si el codominio vive en `Sort (v + 1)` (`Type v`), el producto vive en `max u (v + 1)`. -/
@[simp]
def imaxLevel (u v : Nat) : Nat :=
  match v with
  | 0     => 0
  | v + 1 => max u (v + 1)

/-- TEOREMA 1 (Impredicatividad de `Prop = Sort 0` en el Kernel):
    Cuantificar sobre cualquier universo `Sort u` hacia una proposición `Sort 0` permanece en `Sort 0`. -/
@[simp]
theorem imaxLevel_zero_right (u : Nat) :
    imaxLevel u 0 = 0 :=
  rfl

/-- TEOREMA 2 (Idempotencia de `imaxLevel` en el mismo universo `u`): -/
@[simp]
theorem imaxLevel_self (u : Nat) :
    imaxLevel u u = u := by
  cases u with
  | zero   => rfl
  | succ k => simp [imaxLevel]

/-! ## 1. Sintaxis Unificada del Kernel con `Sort u`, `TrueProp` y Eliminador Dependiente `boolRec` -/

/-- Sintaxis unificada Términos/Tipos del Kernel CIC con índices de De Bruijn -/
inductive CicExpr where
  | bvar     : Nat → CicExpr                                   -- Variable ligada `#i`
  | sort     : Nat → CicExpr                                   -- Universo `Sort u` (`0 = Prop`, `1 = Type 0`, ...)
  | trueProp : CicExpr                                         -- Proposición `True : Prop` (`Sort 0`)
  | natTy    : CicExpr                                         -- `Nat : Sort 1` (`Type 0`)
  | natLit   : Nat → CicExpr                                   -- Literal natural
  | boolTy   : CicExpr                                         -- `Bool : Sort 1` (`Type 0`)
  | boolLit  : Bool → CicExpr                                  -- `false` / `true`
  | pi       : CicExpr → CicExpr → CicExpr                     -- `Π (x : A), B`
  | lam      : CicExpr → CicExpr → CicExpr                     -- `λ (x : A) => t`
  | app      : CicExpr → CicExpr → CicExpr                     -- Aplicación `f a`
  | boolRec  : CicExpr → CicExpr → CicExpr → CicExpr → CicExpr -- `Bool.rec motive tFalse tTrue scrut`
  deriving Repr, DecidableEq

namespace CicExpr

/-- Desplazamiento (`shift`) de índices de De Bruijn libres `≥ cutoff` -/
@[simp]
def shift (cutoff byAmount : Nat) : CicExpr → CicExpr
  | .bvar i =>
    if i < cutoff then .bvar i else .bvar (i + byAmount)
  | .sort u        => .sort u
  | .trueProp      => .trueProp
  | .natTy         => .natTy
  | .natLit n      => .natLit n
  | .boolTy        => .boolTy
  | .boolLit b     => .boolLit b
  | .pi dom cod    => .pi (shift cutoff byAmount dom) (shift (cutoff + 1) byAmount cod)
  | .lam dom body  => .lam (shift cutoff byAmount dom) (shift (cutoff + 1) byAmount body)
  | .app f a       => .app (shift cutoff byAmount f) (shift cutoff byAmount a)
  | .boolRec m tf tt s =>
    .boolRec (shift cutoff byAmount m) (shift cutoff byAmount tf)
             (shift cutoff byAmount tt) (shift cutoff byAmount s)

/-- Sustitución con captura evitada del índice `target` por `replacement` -/
@[simp]
def subst (target : Nat) (replacement : CicExpr) : CicExpr → CicExpr
  | .bvar i =>
    if i == target then
      replacement
    else if i > target then
      .bvar (i - 1)
    else
      .bvar i
  | .sort u        => .sort u
  | .trueProp      => .trueProp
  | .natTy         => .natTy
  | .natLit n      => .natLit n
  | .boolTy        => .boolTy
  | .boolLit b     => .boolLit b
  | .pi dom cod =>
    .pi (subst target replacement dom)
        (subst (target + 1) (shift 0 1 replacement) cod)
  | .lam dom body =>
    .lam (subst target replacement dom)
         (subst (target + 1) (shift 0 1 replacement) body)
  | .app f a =>
    .app (subst target replacement f) (subst target replacement a)
  | .boolRec m tf tt s =>
    .boolRec (subst target replacement m) (subst target replacement tf)
             (subst target replacement tt) (subst target replacement s)

@[simp]
def instantiate0 (body arg : CicExpr) : CicExpr :=
  subst 0 arg body

/-! ## 2. Reducción `whnf` del Kernel con $\beta$-Reducción y $\iota$-Reducción de `boolRec` -/

/-- Evaluador acotado por combustible `fuel` que ejecuta tanto $\beta$-reducción (`app (lam _) a`)
    como $\iota$-reducción del eliminador inductivo (`boolRec m tf tt (boolLit b)`): -/
@[simp]
def whnf : Nat → CicExpr → CicExpr
  | 0, e => e
  | fuel + 1, .app f a =>
    let f' := whnf fuel f
    match f' with
    | .lam _ body => whnf fuel (instantiate0 body a)
    | _           => .app f' a
  | fuel + 1, .boolRec m tf tt s =>
    let s' := whnf fuel s
    match s' with
    | .boolLit false => whnf fuel tf
    | .boolLit true  => whnf fuel tt
    | _              => .boolRec m tf tt s'
  | _ + 1, e => e

/-! ## 3. Inferencia Nuclear de Tipos con Jerarquía de Universos y *Large Elimination* -/

abbrev CicCtx := List CicExpr

@[simp]
def lookupCtx : CicCtx → Nat → Option CicExpr
  | [],      _     => none
  | ty :: _, 0     => some (shift 0 1 ty)
  | _ :: Γ,  i + 1 =>
    match lookupCtx Γ i with
    | some ty => some (shift 0 1 ty)
    | none    => none

@[simp]
def defEq (fuel : Nat) (e1 e2 : CicExpr) : Bool :=
  whnf fuel e1 == whnf fuel e2

/-- Verificador nuclear de tipos (`inferType`) del Cálculo de Construcciones Inductivas: -/
@[simp]
def inferType (fuel : Nat) (Γ : CicCtx) : CicExpr → Option CicExpr
  | .bvar i     => lookupCtx Γ i
  | .sort u     => some (.sort (u + 1)) -- Axioma de Russell: `Sort u : Sort (u + 1)`
  | .trueProp   => some (.sort 0)       -- `True : Prop ≡ Sort 0`
  | .natTy      => some (.sort 1)       -- `Nat : Type 0 ≡ Sort 1`
  | .natLit _   => some .natTy
  | .boolTy     => some (.sort 1)       -- `Bool : Type 0 ≡ Sort 1`
  | .boolLit _  => some .boolTy
  | .pi dom cod =>
    -- Regla Π-Form con `imaxLevel`: si `dom : Sort u` y `cod : Sort v`, entonces `Π dom cod : Sort (imax u v)`
    match inferType fuel Γ dom, inferType fuel (dom :: Γ) cod with
    | some domSort, some codSort =>
      match whnf fuel domSort, whnf fuel codSort with
      | .sort u, .sort v => some (.sort (imaxLevel u v))
      | _, _             => none
    | _, _ => none
  | .lam dom body =>
    match inferType fuel Γ dom with
    | some domSort =>
      match whnf fuel domSort with
      | .sort _ =>
        match inferType fuel (dom :: Γ) body with
        | some cod => some (.pi dom cod)
        | none     => none
      | _ => none
    | none => none
  | .app f a =>
    match inferType fuel Γ f, inferType fuel Γ a with
    | some fTy, some aTy =>
      match whnf fuel fTy with
      | .pi dom cod =>
        if defEq fuel dom aTy then
          some (instantiate0 cod a)
        else
          none
      | _ => none
    | _, _ => none
  | .boolRec motive tFalse tTrue scrut =>
    -- Regla de eliminación dependiente de `Bool`:
    -- Si `motive : Bool → Sort u`, `tFalse : motive false`, `tTrue : motive true` y `scrut : Bool`,
    -- entonces `boolRec motive tFalse tTrue scrut : motive scrut`!
    match inferType fuel Γ motive, inferType fuel Γ tFalse,
          inferType fuel Γ tTrue, inferType fuel Γ scrut with
    | some motiveTy, some tfTy, some ttTy, some scrutTy =>
      match whnf fuel motiveTy with
      | .pi dom cod =>
        match whnf fuel cod with
        | .sort _ =>
          if defEq fuel dom .boolTy &&
             defEq fuel scrutTy .boolTy &&
             defEq fuel tfTy (.app motive (.boolLit false)) &&
             defEq fuel ttTy (.app motive (.boolLit true)) then
            some (whnf fuel (.app motive scrut))
          else
            none
        | _ => none
      | _ => none
    | _, _, _, _ => none

/-! ## 4. Pruebas de Verificación del Kernel: Universos, `imax` y *Large Elimination* -/

/-- TEOREMA 3: El kernel verifica que:
    1. Una cuantificación impredicativa sobre tipos `∀ (α : Type 0), True` (`.pi (.sort 1) .trueProp`)
       vive en `Prop` (`Sort 0`), aunque su dominio `Type 0` viva en `Type 1` (`Sort 2`)!
    2. En cambio, un tipo de funciones entre tipos `(α : Type 0) → Type 0` (`.pi (.sort 1) (.sort 1)`)
       sube predicativamente a `Type 1` (`Sort 2`)! -/
theorem kernel_verifies_impredicative_prop_and_predicative_type :
    inferType 10 [] (.pi (.sort 1) .trueProp) = some (.sort 0) ∧
    inferType 10 [] (.pi (.sort 1) (.sort 1)) = some (.sort 2) := by
  decide

/-- Definimos dentro de nuestro mini-kernel una familia de tipos por *Large Elimination*:
    `MotiveLarge := λ (b : Bool) => boolRec (λ _ => Type 0) Nat Bool b`
    que devuelve el tipo `Nat` cuando `b = false` y el tipo `Bool` cuando `b = true`! -/
def motiveLarge : CicExpr :=
  .lam .boolTy (.boolRec (.lam .boolTy (.sort 1)) .natTy .boolTy (.bvar 0))

/-- Y definimos una sección dependiente `depTerm (b : Bool) : MotiveLarge b` que devuelve
    `42 : Nat` cuando `b = false` y `true : Bool` cuando `b = true`: -/
def depTerm (b : Bool) : CicExpr :=
  .boolRec motiveLarge (.natLit 42) (.boolLit true) (.boolLit b)

/-- TEOREMA CUMBRE (`M60`):
    Nuestro mini-kernel evalúa `MotiveLarge` en tiempo de chequeo de tipos (*Large Elimination*)
    y deduce que:
    - `depTerm false` tiene tipo `.natTy` (`Nat`)!
    - `depTerm true`  tiene tipo `.boolTy` (`Bool`)! -/
theorem kernel_verifies_large_elimination_dependent_types :
    inferType 15 [] (depTerm false) = some .natTy ∧
    inferType 15 [] (depTerm true)  = some .boolTy := by
  decide

end CicExpr
end LeanTT.M60
