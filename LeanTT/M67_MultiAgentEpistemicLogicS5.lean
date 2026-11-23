/-!
# Módulo 67: Lógica Epistémica Multi-Agente ($S5_n$) — Conocimiento Individual, Compartido y Distribuido
## Ámbito: Inteligencia Artificial Distribuida y Razonamiento sobre el Conocimiento (Fagin-Halpern-Moses-Vardi)

En sistemas multi-agente, protocolos criptográficos y sistemas distribuidos (*Reasoning About Knowledge*,
Fagin, Halpern, Moses & Vardi, 1995), la **Lógica Epistémica Multi-Agente ($S5_n$)** modela qué sabe
cada agente $a \in \text{Agent}$ mediante una relación de indistinguibilidad epistémica $\sim_a$
entre estados globales del mundo (`World`):
- **Conocimiento Individual ($K_a \varphi$):** El agente $a$ sabe $\varphi$ en el mundo $w$ si $\varphi$
  es verdadera en todos los mundos $w'$ que el agente $a$ no puede distinguir de $w$ ($w \sim_a w'$).
- **Conocimiento de Todos ($E \varphi$):** Todo agente $a$ sabe $\varphi$.
- **Conocimiento Distribuido ($D \varphi$):** Es lo que sabría un observador ideal que combinara
  toda la información de todos los agentes a la vez ($\forall a,\, w \sim_a w' \implies \varphi(w')$).

En este módulo:
1. Formalizamos marcos epistémicos `EpistemicFrame Agent World` y predicados de equivalencia ($S5$:
   reflexiva, simétrica y transitiva).
2. Definimos los operadores epistémicos `knows` ($K_a$), `everyoneKnows` ($E$) y `distributedKnows` ($D$).
3. Demostramos los **4 Axiomas Fundamentales del Conocimiento ($S5_n$)**:
   - **Axioma $K$ (Omnisciencia Lógica / Distribución):** $K_a(\varphi \to \psi) \to K_a\varphi \to K_a\psi$.
   - **Axioma $T$ (Veracidad del Conocimiento):** $K_a\varphi \to \varphi$ (bajo reflexividad).
   - **Axioma $4$ (Introspección Positiva):** $K_a\varphi \to K_a(K_a\varphi)$ (bajo transitividad).
   - **Axioma $5$ (Introspección Negativa):** $\neg K_a\varphi \to K_a(\neg K_a\varphi)$ (bajo simetría y transitividad).
4. Demostramos la jerarquía epistémica: $E\varphi \to K_a\varphi \to D\varphi$.
-/

namespace LeanTT.M67

/-- Marco epistémico multi-agente: asigna a cada agente `a : Agent` su relación de indistinguibilidad
    entre mundos posibles `World → World → Prop`. -/
structure EpistemicFrame (Agent World : Type) where
  indist : Agent → World → World → Prop

abbrev EProp (World : Type) := World → Prop

/-- Operador de Conocimiento Individual `K_a φ` (`knows F a φ`):
    El agente `a` sabe `φ` en el mundo `w` si en todo mundo `w'` indistinguible de `w` para `a` se cumple `φ w'`. -/
@[simp]
def knows {Agent World : Type} (F : EpistemicFrame Agent World) (a : Agent) (φ : EProp World) : EProp World :=
  fun w => ∀ w' : World, F.indist a w w' → φ w'

/-- Operador "Todos Saben" `E φ` (`everyoneKnows F φ`): todo agente individual `a` sabe `φ`. -/
@[simp]
def everyoneKnows {Agent World : Type} (F : EpistemicFrame Agent World) (φ : EProp World) : EProp World :=
  fun w => ∀ a : Agent, knows F a φ w

/-- Operador de Conocimiento Distribuido `D φ` (`distributedKnows F φ`):
    `φ` se cumple en todo mundo `w'` que sea simultáneamente indistinguible de `w` para TODOS los agentes
    (la intersección de las relaciones de equivalencia de todos los agentes). -/
@[simp]
def distributedKnows {Agent World : Type} (F : EpistemicFrame Agent World) (φ : EProp World) : EProp World :=
  fun w => ∀ w' : World, (∀ a : Agent, F.indist a w w') → φ w'

/-! ## 1. Los Axiomas de la Lógica Epistémica $S5_n$ -/

/-- TEOREMA 1 (Axioma K — Distribución del Conocimiento sobre la Implicación): -/
theorem epistemic_axiom_K {Agent World : Type} (F : EpistemicFrame Agent World)
    (a : Agent) (φ ψ : EProp World) (w : World)
    (hImp : knows F a (fun v => φ v → ψ v) w)
    (hPhi : knows F a φ w) :
    knows F a ψ w :=
  fun w' hRel => hImp w' hRel (hPhi w' hRel)

/-- TEOREMA 2 (Axioma T — Veracidad del Conocimiento: `K_a φ → φ`):
    Si el mundo real `w` es siempre indistinguible de sí mismo (reflexividad),
    ningún agente puede "saber" algo falso! -/
theorem epistemic_axiom_T {Agent World : Type} (F : EpistemicFrame Agent World)
    (a : Agent) (φ : EProp World)
    (hRefl : ∀ w : World, F.indist a w w)
    (w : World) (hK : knows F a φ w) :
    φ w :=
  hK w (hRefl w)

/-- TEOREMA 3 (Axioma 4 — Introspección Positiva: `K_a φ → K_a (K_a φ)`):
    Si la indistinguibilidad del agente `a` es transitiva, cuando `a` sabe `φ`, sabe que sabe `φ`. -/
theorem epistemic_axiom_4 {Agent World : Type} (F : EpistemicFrame Agent World)
    (a : Agent) (φ : EProp World)
    (hTrans : ∀ u v z : World, F.indist a u v → F.indist a v z → F.indist a u z)
    (w : World) (hK : knows F a φ w) :
    knows F a (knows F a φ) w :=
  fun w' h1 w'' h2 => hK w'' (hTrans w w' w'' h1 h2)

/-- TEOREMA 4 (Axioma 5 — Introspección Negativa: `¬ K_a φ → K_a (¬ K_a φ)`):
    Si la relación de indistinguibilidad de `a` es simétrica y transitiva (euclídea),
    cuando el agente `a` NO sabe `φ`, ¡sabe con certeza que no sabe `φ`! -/
theorem epistemic_axiom_5 {Agent World : Type} (F : EpistemicFrame Agent World)
    (a : Agent) (φ : EProp World)
    (hSymm  : ∀ u v : World, F.indist a u v → F.indist a v u)
    (hTrans : ∀ u v z : World, F.indist a u v → F.indist a v z → F.indist a u z)
    (w : World) (hNotK : ¬ knows F a φ w) :
    knows F a (fun v => ¬ knows F a φ v) w := by
  intro w' hww' hKw'
  apply hNotK
  intro w'' hww''
  exact hKw' w'' (hTrans w' w w'' (hSymm w w' hww') hww'')

/-! ## 2. Jerarquía entre Conocimiento Compartido ($E$), Individual ($K_a$) y Distribuido ($D$) -/

/-- TEOREMA 5 (`E φ → K_a φ` y `K_a φ → D φ`):
    Lo que todos saben lo sabe cualquier agente `a`, y lo que sabe cualquier agente `a`
    forma automáticamente parte del conocimiento distribuido de la comunidad! -/
theorem epistemic_hierarchy {Agent World : Type} (F : EpistemicFrame Agent World)
    (a : Agent) (φ : EProp World) (w : World) :
    (everyoneKnows F φ w → knows F a φ w) ∧
    (knows F a φ w → distributedKnows F φ w) := by
  refine ⟨fun hE => hE a, ?_⟩
  intro hKa w' hAll
  exact hKa w' (hAll a)

end LeanTT.M67
