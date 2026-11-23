# Lección 01: Aritmetización de Programas y Puertas de Circuitos ZK (R1CS y PlonKish) en Lean 4

> **Navegación del Mini-Curso:** [⬅️ Índice del Mini-Curso ZK](00_indice_minicurso_zk_y_cripto.md) | [➡️ Lección 02: Polinomios Computables y Sum-Check](02_polinomios_computables_y_sumcheck.md)
>
> **Módulos ejecutables relacionados:** [`LeanTT/M21_NumberTheoryAndCryptography.lean`](../../LeanTT/M21_NumberTheoryAndCryptography.lean), [`LeanTT/Exercises/E03_WorkoutVerificationAndCryptography.lean`](../../LeanTT/Exercises/E03_WorkoutVerificationAndCryptography.lean) y [`LeanTT/Solutions/S03_WorkoutVerificationAndCryptography.lean`](../../LeanTT/Solutions/S03_WorkoutVerificationAndCryptography.lean).

---

## 1. ¿Qué es la «Aritmetización» en una Prueba de Conocimiento Cero (ZK-SNARK / STARK)?

Un procesador convencional (o la máquina virtual de Ethereum, EVM) ejecuta instrucciones booleanas y de flujo de control (`AND`, `XOR`, `IF-ELSE`, `MUX`, comparaciones) sobre bits.
Sin embargo, los sistemas criptográficos de pruebas sucintas (como Groth16, PlonK, Halo2 o los zkVMs como RISC Zero y SP1) no operan directamente sobre bits, sino sobre **ecuaciones polinómicas en un cuerpo finito $\mathbb{F}_p$**.

El proceso de traducir un programa computacional a un sistema de ecuaciones polinómicas cuadráticas (**R1CS** — *Rank-1 Constraint System*) o polinómicas personalizadas (**PlonKish**) se denomina **Aritmetización**.

### Los Dos Errores Catastróficos al Diseñar un Circuito ZK
Cuando un ingeniero criptográfico escribe las ecuaciones $C(w) = 0$ que deben cumplir los cables (*wires*) $w$ de un circuito para modelar una función $y = f(x)$, pueden ocurrir dos fallos:

1. **Circuito Sub-Restringido (*Under-Constrained Circuit* — Fallo de *Soundness*):**
   Las ecuaciones son demasiado débiles y admiten soluciones espurias $y' \neq f(x)$. **Es la vulnerabilidad más grave y frecuente en auditorías ZK reales**: permite a un Prover malicioso falsificar una prueba de conocimiento cero para un estado inválido (p. ej., acuñar monedas de la nada).
2. **Circuito Sobre-Restringido (*Over-Constrained Circuit* — Fallo de *Completeness*):**
   Las ecuaciones son demasiado restrictivas y rechazan entradas honestas válidas $y = f(x)$, bloqueando a los usuarios legítimos (*denial of service*).

Por eso, verificar formalmente una puerta o subcircuito ZK en **Lean 4** (tal como hace la librería **[Clean](https://github.com/Verified-zkEVM/clean)** de `Verified-zkEVM`) consiste siempre en demostrar una **doble implicación ($\iff$, *Soundness & Completeness*)**:

$$\underbrace{\text{RestriccionesPolinómicas}(x, y) = 0}_{\text{Ecuaciones del Circuito ZK}} \;\Longleftrightarrow\; \underbrace{y = f_{\text{especificación}}(x)}_{\text{Semántica Funcional Esperada}}$$

---

## 2. Tabla de Puertas Aritméticas R1CS / PlonK Verificadas en Lean 4

Todas las puertas siguientes están demostradas sin `sorry` en [`M21`](../../LeanTT/M21_NumberTheoryAndCryptography.lean), [`E03`](../../LeanTT/Exercises/E03_WorkoutVerificationAndCryptography.lean) y [`S03`](../../LeanTT/Solutions/S03_WorkoutVerificationAndCryptography.lean):

| Puerta / Restricción | Ecuación Polinómica en el Circuito | Grado | Propiedad Formal Demostrada en Lean 4 |
| :--- | :--- | :---: | :--- |
| **Cable Booleano (`BitConstraint`)** | $b \cdot (1 - b) = 0$ | $2$ | $b \cdot (1 - b) = 0 \iff (b = 0 \lor b = 1)$ |
| **Puerta `NOT` Booleana** | $y = 1 - b$ | $1$ | Si $b \in \{0, 1\}$, entonces $1 - b \in \{0, 1\}$ e invierte el bit |
| **Puerta `AND` Booleana** | $y = a \cdot b$ | $2$ | Si $a, b \in \{0, 1\}$, entonces $a \cdot b \in \{0, 1\}$ y vale $1 \iff a=1 \land b=1$ |
| **Puerta `OR` Booleana** | $y = a + b - a \cdot b$ | $2$ | Si $a, b \in \{0, 1\}$, entonces $a + b - a\cdot b \in \{0, 1\}$ |
| **Puerta `XOR` Booleana** | $y = a + b - 2 \cdot a \cdot b$ | $2$ | Si $a, b \in \{0, 1\}$, entonces $a + b - 2ab \in \{0, 1\}$ |
| **Multiplexor (`if s then x₁ else x₀`)** | $y - x_0 = s \cdot (x_1 - x_0)$ | $2$ | Si $s \in \{0, 1\}$, entonces $y = x_1$ (cuando $s=1$) e $y = x_0$ (cuando $s=0$) |

---

## 3. Laboratorio en Lean 4: Verificación de *Soundness & Completeness* de un Circuito ZK

Veamos cómo se demuestra en Lean 4 la equivalencia exacta (*Soundness* + *Completeness*) de un subcircuito de selección condicional con comprobación de bit integrada:

```lean
namespace CursoZK.Leccion01

/-- Restricción cuadrática que fuerza a un cable `b : Int` a ser un bit booleano (`0` o `1`): -/
def BitConstraint (b : Int) : Prop :=
  b * (1 - b) = 0

/-- Restricción cuadrática de un Multiplexor (`y = if s = 1 then a else b`): -/
def MuxConstraint (s a b y : Int) : Prop :=
  y = b + s * (a - b)

/-- Especificación funcional de alto nivel de lo que DEBE hacer el circuito completo: -/
def MuxSpec (s a b y : Int) : Prop :=
  (s = 0 ∧ y = b) ∨ (s = 1 ∧ y = a)

/-- Lema fundamental: `b * (1 - b) = 0 ↔ (b = 0 ∨ b = 1)` -/
theorem bitConstraint_iff (b : Int) :
    BitConstraint b ↔ (b = 0 ∨ b = 1) := by
  dsimp [BitConstraint]
  constructor
  · intro h
    rcases Int.mul_eq_zero.mp h with h0 | h1
    · left; exact h0
    · right; omega
  · rintro (rfl | rfl) <;> rfl

/-- TEOREMA CUMBRE DE LA LECCIÓN 01 (Soundness & Completeness del Subcircuito Multiplexor):
    El sistema de dos ecuaciones polinómicas `BitConstraint s ∧ MuxConstraint s a b y`
    es exactamente equivalente a la especificación funcional `MuxSpec s a b y`! -/
theorem mux_circuit_sound_and_complete (s a b y : Int) :
    (BitConstraint s ∧ MuxConstraint s a b y) ↔ MuxSpec s a b y := by
  rw [bitConstraint_iff]
  dsimp [MuxConstraint, MuxSpec]
  constructor
  · rintro ⟨rfl | rfl, hy⟩
    · left; refine ⟨rfl, by omega⟩
    · right; refine ⟨rfl, by omega⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨Or.inl rfl, by omega⟩
    · refine ⟨Or.inr rfl, by omega⟩

end CursoZK.Leccion01
```

---

## 4. Ejercicio Práctico de la Lección 01

### Ejercicio 1.1: Peligro de un Circuito Sub-Restringido (*Under-Constrained Bug*)
Supongamos que un programador ZK olvida incluir `BitConstraint s` en el circuito del multiplexor y solo impone `MuxConstraint s a b y` ($y = b + s \cdot (a - b)$). Demuestra en Lean 4 que si las entradas son $a = 10$ y $b = 0$, un Prover malicioso puede elegir $s = 5$ y hacer que la salida sea $y = 50$ (un valor que no es ni $a$ ni $b$) cumpliendo la ecuación del multiplexor.

<details>
<summary>💡 <b>Ver Solución Comentada en Lean 4</b></summary>

```lean
open CursoZK.Leccion01

/-- Ataque a un multiplexor donde se olvidó restringir `s` con `BitConstraint s`: -/
theorem ataque_mux_sin_bitConstraint :
    MuxConstraint 5 10 0 50 ∧ (50 ≠ 10 ∧ 50 ≠ 0) := by
  dsimp [MuxConstraint]
  decide
```
</details>

---

👉 **Siguiente lección:** [**Lección 02 — Polinomios Computables (Esquema de Horner, `CompPoly`) y el Protocolo Interactivo Sum-Check (`ArkLib`)**](02_polinomios_computables_y_sumcheck.md)
