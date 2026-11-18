/-!
# Módulo 43: Motor de Políticas de Autorización Verificado (Inspirado en AWS Cedar)
## Ámbito: Seguridad en la Nube, Control de Acceso Formal y Verificación Industrial

**[Cedar (`cedar-policy/cedar-spec`)](https://github.com/cedar-policy/cedar-spec)** es el lenguaje
industrial de políticas de autorización de Amazon Web Services cuyo modelo semántico y validador
están formalizados y demostrados en **Lean 4**.

El diseño de Cedar se apoya en dos principios de oro de seguridad:
1. **Denegación por Defecto (*Default Deny*):** Si ninguna regla `permit` coincide con la
   solicitud, el acceso es denegado automáticamente.
2. **Prohibición Prevalece sobre Permiso (*Forbid Overrides Permit*):** Si al menos una regla
   `forbid` coincide con la solicitud, el acceso es **denegado sin excepción**, incluso si cien
   reglas `permit` autorizan la operación.

En este módulo construimos un motor ejecutable de políticas de autorización y **demostramos
formalmente en Lean 4 sus invariantes de seguridad fundamentales**.
-/

namespace LeanTT.M43

/-- Efecto declarativo de una regla de política (`permit` o `forbid`) -/
inductive Effect where
  | permit : Effect
  | forbid : Effect
  deriving Repr, DecidableEq

/-- Decisión final emitida por el motor de autorización (`allow` o `deny`) -/
inductive Decision where
  | allow : Decision
  | deny  : Decision
  deriving Repr, DecidableEq

/-- Solicitud de acceso `(principal, action, resource)` -/
structure Request where
  principal : Nat
  action    : Nat
  resource  : Nat
  deriving Repr, DecidableEq

/-- Una regla de autorización con comodines opcionales (`none` significa `*`, cualquier valor) -/
structure Rule where
  effect    : Effect
  principal : Option Nat
  action    : Option Nat
  resource  : Option Nat
  deriving Repr, DecidableEq

/-- Comprueba si un patrón opcional `pat` coincide con un identificador concreto `val` -/
@[simp]
def matchesField (pat : Option Nat) (val : Nat) : Bool :=
  match pat with
  | none   => true
  | some p => p == val

/-- Comprueba si una regla `r` es aplicable a la solicitud `req` -/
@[simp]
def matchesRule (r : Rule) (req : Request) : Bool :=
  matchesField r.principal req.principal &&
  matchesField r.action    req.action    &&
  matchesField r.resource  req.resource

/-- ¿Existe en la política al menos una regla de efecto `eff` que coincida con `req`? -/
@[simp]
def hasMatchingEffect (eff : Effect) (req : Request) : List Rule → Bool
  | []      => false
  | r :: rs => ((r.effect == eff) && matchesRule r req) || hasMatchingEffect eff req rs

/-- Evaluador oficial del motor de autorización:
    Concede `.allow` si y solo si hay al menos un `.permit` aplicable y NINGÚN `.forbid` aplicable. -/
@[simp]
def evaluatePolicy (policy : List Rule) (req : Request) : Decision :=
  if hasMatchingEffect .permit req policy && !(hasMatchingEffect .forbid req policy) then
    .allow
  else
    .deny

/-! ## Teoremas de Seguridad del Motor de Autorización (Estilo `cedar-spec`) -/

/-- INVARIANTE 1 (Default Deny):
    Una política vacía `[]` deniega absolutamente todas las solicitudes posibles. -/
theorem default_deny (req : Request) :
    evaluatePolicy [] req = .deny :=
  rfl

/-- INVARIANTE 2 (Explicit Forbid Always Overrides Permit):
    Si la función `hasMatchingEffect .forbid req policy` es `true`, entonces el motor
    devuelve `.deny` sin importar cuántas reglas `.permit` haya en `policy`! -/
theorem forbid_overrides_permit (policy : List Rule) (req : Request)
    (h_forbid : hasMatchingEffect .forbid req policy = true) :
    evaluatePolicy policy req = .deny := by
  simp [evaluatePolicy, h_forbid]

/-- INVARIANTE 3 (Imposibilidad de Escalada al Añadir un `forbid` Global):
    Encabezar cualquier política `policy` con una regla `forbid` universal (`none, none, none`)
    revoca instantáneamente el acceso para cualquier solicitud `req`. -/
def globalFreezeRule : Rule :=
  { effect := .forbid, principal := none, action := none, resource := none }

theorem global_freeze_denies_all (policy : List Rule) (req : Request) :
    evaluatePolicy (globalFreezeRule :: policy) req = .deny := by
  apply forbid_overrides_permit
  simp [globalFreezeRule]

/-- INVARIANTE 4 (Certificado Necesario de Autorización):
    Si el motor devuelve `.allow`, entonces está garantizado matemáticamente que:
    1) Existe un `.permit` que coincide, y
    2) No existe ningún `.forbid` que coincida. -/
theorem allow_implies_permit_and_no_forbid (policy : List Rule) (req : Request)
    (h_allow : evaluatePolicy policy req = .allow) :
    hasMatchingEffect .permit req policy = true ∧
    hasMatchingEffect .forbid req policy = false := by
  dsimp [evaluatePolicy] at h_allow
  cases hp : hasMatchingEffect .permit req policy <;>
  cases hf : hasMatchingEffect .forbid req policy <;>
  simp [hp, hf] at h_allow
  exact ⟨rfl, rfl⟩

end LeanTT.M43
