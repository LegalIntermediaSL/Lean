/-!
# Módulo 19: Máquinas de Estados Finitos y Protocolos de Comunicación Tipados
## Ámbito: Sistemas Concurrentes, Protocolos de Red y Tipos Sesión (*Session Types*)

Los tipos dependientes permiten indexar el tipo de un recurso o conexión de red por su
**estado actual en el protocolo** (`Disconnected`, `Connected`, `Authenticated`, `Closed`).
De este modo:
- Enviar un mensaje sin haberse autenticado antes **no es una excepción en tiempo de ejecución**,
  sino un **error de tipos en tiempo de compilación**.
- Olvidar cerrar una sesión antes de finalizar tampoco compila.
-/

namespace LeanTT.M19

/-- Estados del protocolo de una sesión segura cliente-servidor -/
inductive SessionState where
  | disconnected
  | connected
  | authenticated
  | closed
  deriving DecidableEq, Repr

/-- Transiciones elementales permitidas en el protocolo:
    `Step s1 s2` representa una acción atómica que lleva la sesión del estado `s1` al `s2`. -/
inductive Step : SessionState → SessionState → Type where
  | connect   : String → Step .disconnected .connected
  | login     : String → String → Step .connected .authenticated
  | sendQuery : String → Step .authenticated .authenticated
  | logout    : Step .authenticated .connected
  | close     : Step .connected .closed

/-- Un programa de protocolo completo `Protocol s1 s2 α` es una mónada indexada (Atkey Indexed Monad)
    que comienza en el estado `s1`, termina en el estado `s2` y produce un valor de tipo `α`. -/
inductive Protocol : SessionState → SessionState → Type → Type 1 where
  | pure : {s : SessionState} → {α : Type} → α → Protocol s s α
  | bind : {s1 s2 s3 : SessionState} → {α : Type} →
           Step s1 s2 → (Unit → Protocol s2 s3 α) → Protocol s1 s3 α

/-- Constructores ergonómicos para pasos del protocolo -/
def doStep {s1 s2 : SessionState} (st : Step s1 s2) : Protocol s1 s2 Unit :=
  .bind st (fun _ => .pure ())

def seqProtocol {s1 s2 s3 : SessionState} {α β : Type}
    (p1 : Protocol s1 s2 α) (p2 : α → Protocol s2 s3 β) : Protocol s1 s3 β :=
  match p1 with
  | .pure a       => p2 a
  | .bind st next => .bind st (fun u => seqProtocol (next u) p2)

infixl:55 " >>>= " => seqProtocol

/-- Una sesión completa válida DEBE empezar en `.disconnected` y terminar en `.closed`: -/
abbrev CompleteSession (α : Type) := Protocol .disconnected .closed α

/-- Ejemplo de sesión bien tipada: conecta, inicia sesión, envía dos consultas,
    cierra sesión de usuario y cierra la conexión TCP. -/
def sesionValida : CompleteSession String :=
  doStep (.connect "192.168.1.10") >>>= fun _ =>
  doStep (.login "admin" "secreto42") >>>= fun _ =>
  doStep (.sendQuery "SELECT * FROM usuarios") >>>= fun _ =>
  doStep (.sendQuery "COMMIT") >>>= fun _ =>
  doStep .logout >>>= fun _ =>
  doStep .close >>>= fun _ =>
  .pure "Transacción completada y conexión cerrada con éxito"

/-- Intérprete de auditoría que genera el registro de trazas de cualquier protocolo tipado -/
def traceStep {s1 s2 : SessionState} : Step s1 s2 → String
  | .connect host    => s!"[CONNECT {host}]"
  | .login user _    => s!"[LOGIN {user}]"
  | .sendQuery q     => s!"[QUERY '{q}']"
  | .logout          => "[LOGOUT]"
  | .close           => "[CLOSE]"

def runAudit {s1 s2 : SessionState} {α : Type} : Protocol s1 s2 α → List String × α
  | .pure a       => ([], a)
  | .bind st next =>
    let (logs, res) := runAudit (next ())
    (traceStep st :: logs, res)

#eval runAudit sesionValida

/-! ## Leyes Algebraicas de Mónada Indexada de Atkey y Homomorfismo de Auditoría -/

/-- LEY 1 (Identidad Izquierda de la Mónada Indexada): `.pure a >>>= k = k a` -/
@[simp]
theorem seqProtocol_pure_left {s1 s2 : SessionState} {α β : Type}
    (a : α) (k : α → Protocol s1 s2 β) :
    (.pure a >>>= k) = k a :=
  rfl

/-- LEY 2 (Identidad Derecha de la Mónada Indexada): `p >>>= Protocol.pure = p` -/
@[simp]
theorem seqProtocol_pure_right {s1 s2 : SessionState} {α : Type}
    (p : Protocol s1 s2 α) :
    (p >>>= fun a => .pure a) = p := by
  induction p with
  | pure a          => rfl
  | bind st next ih =>
    dsimp [seqProtocol]
    congr 1
    funext u
    exact ih u

/-- LEY 3 (Asociatividad de la Composición de Sesiones Tipadas):
    `((p >>>= f) >>>= g) = (p >>>= fun a => f a >>>= g)` -/
theorem seqProtocol_assoc {s1 s2 s3 s4 : SessionState} {α β γ : Type}
    (p : Protocol s1 s2 α)
    (f : α → Protocol s2 s3 β)
    (g : β → Protocol s3 s4 γ) :
    ((p >>>= f) >>>= g) = (p >>>= fun a => f a >>>= g) := by
  induction p with
  | pure a          => rfl
  | bind st next ih =>
    dsimp [seqProtocol]
    congr 1
    funext u
    exact ih u f

/-- TEOREMA DE HOMOMORFISMO DE AUDITORÍA:
    Auditar la composición secuencial `p >>>= k` concatena exactamente las trazas de auditoría
    de `p` con las trazas de `k` aplicado al resultado intermedio! -/
theorem runAudit_seqProtocol {s1 s2 s3 : SessionState} {α β : Type}
    (p : Protocol s1 s2 α) (k : α → Protocol s2 s3 β) :
    runAudit (p >>>= k) =
      let (logs1, res1) := runAudit p
      let (logs2, res2) := runAudit (k res1)
      (logs1 ++ logs2, res2) := by
  induction p with
  | pure a          => rfl
  | bind st next ih =>
    simp only [seqProtocol, runAudit, ih (), List.cons_append]

end LeanTT.M19
