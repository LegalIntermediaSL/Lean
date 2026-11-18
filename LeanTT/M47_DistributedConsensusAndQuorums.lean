/-!
# Módulo 47: Sistemas Distribuidos Verificados, Intersección de Quórums y Seguridad de Consenso
## Ámbito: Protocolos de Consenso (Paxos / Raft / Tendermint / BFT) y Seguridad Distribuida

El corazón de todo protocolo de consenso distribuido (Lamport, *Paxos*, 1998; Ongaro & Ousterhout,
*Raft*, 2014; Castro & Liskov, *PBFT*, 1999) es la propiedad de **Seguridad (*Agreement / Safety*)**:
> *Dos nodos nunca pueden decidir valores distintos $v_1 \neq v_2$ en una misma época (vista/ronda).*

¿Cómo se demuestra matemáticamente esta propiedad? Reduciéndola a la **Propiedad de Intersección
de Quórums**:
1. Un valor $v$ es elegido en una ronda si todos los miembros de un quórum $Q$ votaron por $v$.
2. Cualesquiera dos quórums $Q_1$ y $Q_2$ se intersecan en al menos un nodo **honesto** $n \in Q_1 \cap Q_2$.
3. Todo nodo honesto vota a lo sumo por un único valor por ronda (*Single-Vote Invariant*).
4. Por tanto, el nodo honesto $n$ en la intersección obliga a que $v_1 = v_2$!
-/

namespace LeanTT.M47

abbrev NodeId := Nat
abbrev Value  := Nat

/-- Un sistema de votación en una ronda (época/ballot) con conjuntos de nodos honestos y quórums -/
structure ConsensusSystem where
  /-- ¿Es el nodo `n` honesto (no bizantino)? -/
  Honest : NodeId → Prop
  /-- ¿Es el subconjunto de nodos `Q` un quórum válido? -/
  IsQuorum : (NodeId → Prop) → Prop
  /-- Registro de votos emitidos: `Voted n v` significa que el nodo `n` votó por el valor `v` -/
  Voted : NodeId → Value → Prop
  /-- AXIOMA 1 (Integridad de Voto Honesto): Un nodo honesto jamás vota por dos valores distintos -/
  honest_single_vote :
    ∀ {n : NodeId} {v1 v2 : Value}, Honest n → Voted n v1 → Voted n v2 → v1 = v2
  /-- AXIOMA 2 (Intersección de Quórums): Cualesquiera dos quórums `Q1` y `Q2` comparten al menos
      un nodo honesto `n`. -/
  quorum_intersection :
    ∀ {Q1 Q2 : NodeId → Prop}, IsQuorum Q1 → IsQuorum Q2 →
      ∃ n : NodeId, Q1 n ∧ Q2 n ∧ Honest n

namespace ConsensusSystem

variable (sys : ConsensusSystem)

/-- Un quórum `Q` certifica unánimemente el valor `v` si todo nodo de `Q` ha votado por `v` -/
def QuorumCertifies (Q : NodeId → Prop) (v : Value) : Prop :=
  sys.IsQuorum Q ∧ ∀ n : NodeId, Q n → sys.Voted n v

/-- Un valor `v` alcanza el consenso (`Chosen v`) si existe algún quórum que lo certifica -/
def Chosen (v : Value) : Prop :=
  ∃ Q : NodeId → Prop, sys.QuorumCertifies Q v

/-- TEOREMA FUNDAMENTAL DE SEGURIDAD DEL CONSENSO (*Single-Value Agreement*):
    Si el valor `v1` es certificado por un quórum `Q1` y el valor `v2` es certificado por un
    quórum `Q2`, entonces **`v1 = v2`**! Es imposible que el sistema bifurque (*fork*) la decisión. -/
theorem quorum_agreement {Q1 Q2 : NodeId → Prop} {v1 v2 : Value}
    (hc1 : sys.QuorumCertifies Q1 v1)
    (hc2 : sys.QuorumCertifies Q2 v2) :
    v1 = v2 := by
  rcases hc1 with ⟨hq1, hv1⟩
  rcases hc2 with ⟨hq2, hv2⟩
  -- Por intersección de quórums, extraemos el nodo testigo honesto `n ∈ Q1 ∩ Q2`:
  rcases sys.quorum_intersection hq1 hq2 with ⟨n, hn1, hn2, h_honest⟩
  -- Como `n ∈ Q1`, `n` votó por `v1`; como `n ∈ Q2`, `n` votó por `v2`:
  have vote1 : sys.Voted n v1 := hv1 n hn1
  have vote2 : sys.Voted n v2 := hv2 n hn2
  -- Como `n` es honesto, ambos votos deben ser para el mismo valor:
  exact sys.honest_single_vote h_honest vote1 vote2

/-- COROLARIO DE UNICIDAD DE DECISIÓN (`chosen_unique`):
    La relación `sys.Chosen` define a lo sumo un único valor consensuado. -/
theorem chosen_unique {v1 v2 : Value}
    (h1 : sys.Chosen v1) (h2 : sys.Chosen v2) :
    v1 = v2 := by
  rcases h1 with ⟨Q1, hc1⟩
  rcases h2 with ⟨Q2, hc2⟩
  exact sys.quorum_agreement hc1 hc2

end ConsensusSystem
end LeanTT.M47
