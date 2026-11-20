/-!
# Módulo 54: Cálculo de Procesos Concurrentes y Dualidad de Tipos de Sesión (*Session Types*)
## Ámbito: Concurrencia Tipada, $\pi$-Cálculo / CCS y Ausencia Estática de *Deadlocks*

En los sistemas concurrentes y de paso de mensajes (inspirados en el cálculo CCS de Robin Milner
y en los **Tipos de Sesión Binarios** de Kohei Honda, 1993), dos procesos que se comunican por un
canal bidireccional nunca sufren errores de protocolo ni *deadlocks* de comunicación si el tipo de
sesión de un extremo es exactamente el **dual** (`dualSession`) del otro extremo.

En este módulo:
1. Definimos tipos de datos transmitidos `PayloadTy` y el álgebra inductiva de **Tipos de Sesión Binarios**
   (`SessionTy`: envío `send`, recepción `recv`, elección interna `select`, elección externa `branch` y cierre `endS`).
2. Definimos la operación de dualización `dual` y demostramos que es una **involución perfecta** (`dual_dual`).
3. Definimos cuándo dos extremos de un canal son compatibles (`Compatible s1 s2`) y demostramos que
   un paso de sincronización (`syncStep`) preserva la dualidad entre cliente y servidor.
-/

namespace LeanTT.M54

/-- Tipos de carga útil (*payload*) que pueden enviarse por un canal -/
inductive PayloadTy where
  | nat  : PayloadTy
  | bool : PayloadTy
  | unit : PayloadTy
  deriving Repr, DecidableEq

/-- Tipos de Sesión Binarios de Honda (1993):
    describen la secuencia estructurada de operaciones permitidas en un extremo de un canal. -/
inductive SessionTy where
  | endS   : SessionTy                         -- Canal cerrado (fin del protocolo)
  | send   : PayloadTy → SessionTy → SessionTy -- `!T.S`: enviar un valor de tipo `T` y continuar como `S`
  | recv   : PayloadTy → SessionTy → SessionTy -- `?T.S`: recibir un valor de tipo `T` y continuar como `S`
  | select : SessionTy → SessionTy → SessionTy -- `S₁ ⊕ S₂`: elección interna (el proceso elige rama izq. o der.)
  | branch : SessionTy → SessionTy → SessionTy -- `S₁ & S₂`: elección externa (el proceso ofrece ambas ramas)
  deriving Repr, DecidableEq

namespace SessionTy

/-- Calcula el tipo de sesión dual (el protocolo complementario visto desde el otro extremo del canal): -/
@[simp]
def dual : SessionTy → SessionTy
  | .endS         => .endS
  | .send t cont  => .recv t (dual cont)
  | .recv t cont  => .send t (dual cont)
  | .select s1 s2 => .branch (dual s1) (dual s2)
  | .branch s1 s2 => .select (dual s1) (dual s2)

/-! ## 1. Propiedades Algebraicas de la Dualidad de Sesiones -/

/-- TEOREMA 1 (Involutividad de la Dualidad: `dual (dual S) = S`):
    El dual del protocolo dual recupera exactamente el protocolo original. -/
@[simp]
theorem dual_dual (s : SessionTy) :
    dual (dual s) = s := by
  induction s with
  | endS                 => rfl
  | send t cont ih       => dsimp [dual]; rw [ih]
  | recv t cont ih       => dsimp [dual]; rw [ih]
  | select s1 s2 ih1 ih2 => dsimp [dual]; rw [ih1, ih2]
  | branch s1 s2 ih1 ih2 => dsimp [dual]; rw [ih1, ih2]

/-- Dos extremos de un canal `sClient` y `sServer` son compatibles si uno es el dual del otro -/
def Compatible (sClient sServer : SessionTy) : Prop :=
  sServer = dual sClient

/-- TEOREMA 2 (Simetría de la Compatibilidad de Canales):
    Si el servidor es compatible con el cliente, el cliente es compatible con el servidor. -/
theorem compatible_symm {s1 s2 : SessionTy} (h : Compatible s1 s2) :
    Compatible s2 s1 := by
  dsimp [Compatible] at h ⊢
  rw [h, dual_dual]

/-! ## 2. Semántica de Reducción de Canales y Preservación de Compatibilidad (*Session Fidelity*) -/

/-- Un paso de sincronización entre el extremo izquierdo y el extremo derecho de un canal:
    devuelve `some (s1', s2')` cuando ambos extremos realizan acciones complementarias válidas. -/
@[simp]
def syncStep : SessionTy → SessionTy → Bool → Option (SessionTy × SessionTy)
  | .send t1 c1,     .recv t2 c2,     _     => if t1 == t2 then some (c1, c2) else none
  | .recv t1 c1,     .send t2 c2,     _     => if t1 == t2 then some (c1, c2) else none
  | .select l1 _r1,  .branch l2 _r2,  true  => some (l1, l2)
  | .select _l1 r1,  .branch _l2 r2,  false => some (r1, r2)
  | .branch l1 _r1,  .select l2 _r2,  true  => some (l1, l2)
  | .branch _l1 r1,  .select _l2 r2,  false => some (r1, r2)
  | _,               _,               _     => none

/-- TEOREMA 3 (Progreso Libre de Interbloqueo y Preservación de Dualidad):
    Para cualquier sesión activa `s` que comienza por un envío `.send t cont`,
    el par compatible `(s, dual s)` SIEMPRE puede dar un paso de sincronización sin bloqueo,
    y los tipos de continuación resultantes `(cont, dual cont)` siguen siendo compatibles! -/
theorem send_syncStep_progress_and_preservation (t : PayloadTy) (cont : SessionTy) (choice : Bool) :
    syncStep (.send t cont) (dual (.send t cont)) choice = some (cont, dual cont) ∧
    Compatible cont (dual cont) := by
  refine ⟨?_, rfl⟩
  dsimp [dual, syncStep]
  simp

end SessionTy
end LeanTT.M54
