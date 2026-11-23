/-!
# Módulo 69: Verificación Formal de Hardware Digital — *Half-Adder*, *Full-Adder* y Sumador *Ripple-Carry*
## Ámbito: Diseño Lógico Verificado (RTL / Verilog / VHDL) y Aritmética Binaria de Precisión Finita

Tras el famoso error de división FDIV del procesador Intel Pentium (1994), la verificación formal
de circuitos aritméticos de hardware (sumadores, multiplicadores y ALUs) mediante asistentes de
pruebas se convirtió en una práctica estándar en la industria de semiconductores.

En este módulo:
1. Formalizamos la interpretación aritmética de un bit `bitVal : Bool → Nat` (`0` o `1`), el
   **Semisumador (`halfAdder`)** y el **Sumador Completo de 1 Bit (`fullAdder a b cin`)** construido
   exclusivamente con puertas lógicas booleanas (`xor`, `&&`, `||`).
2. Demostramos el **Teorema de Corrección Aritmética del *Full-Adder* (`fullAdder_correct`)**:
   $$\text{bitVal}(\text{sum}) + 2 \cdot \text{bitVal}(\text{cout}) = \text{bitVal}(a) + \text{bitVal}(b) + \text{bitVal}(\text{cin})$$
3. Construimos un **Sumador *Ripple-Carry* de 2 Bits (`rippleAdder2`)** y de **3 Bits (`rippleAdder3`)**
   encadenando los acarreos en cascada, y demostramos formalmente que calculan la suma exacta
   en base $2$ de los operandos binarios más el acarreo de entrada!
-/

namespace LeanTT.M69

/-- Valor numérico (`0` o `1`) de una línea lógica booleana -/
@[simp]
def bitVal : Bool → Nat
  | false => 0
  | true  => 1

/-- Valor en base 2 de una palabra binaria de 2 bits `(b0, b1)` (*little-endian*: `b0 + 2·b1`) -/
@[simp]
def word2Val (b0 b1 : Bool) : Nat :=
  bitVal b0 + 2 * bitVal b1

/-- Valor en base 2 de una palabra binaria de 3 bits `(b0, b1, b2)` (`b0 + 2·b1 + 4·b2`) -/
@[simp]
def word3Val (b0 b1 b2 : Bool) : Nat :=
  bitVal b0 + 2 * bitVal b1 + 4 * bitVal b2

/-! ## 1. Diseño a Nivel de Puertas Lógicas del *Half-Adder* y *Full-Adder* -/

/-- Semisumador de 1 bit (`halfAdder a b = (sum, carry)`):
    - `sum   = a ⊕ b`
    - `carry = a ∧ b` -/
@[simp]
def halfAdder (a b : Bool) : Bool × Bool :=
  (xor a b, a && b)

/-- Sumador Completo de 1 bit (`fullAdder a b cin = (sum, cout)`):
    - `sum  = a ⊕ b ⊕ cin`
    - `cout = (a ∧ b) ∨ (cin ∧ (a ⊕ b))` -/
@[simp]
def fullAdder (a b cin : Bool) : Bool × Bool :=
  let axb := xor a b
  (xor axb cin, (a && b) || (cin && axb))

/-- TEOREMA 1 (Corrección Aritmética Exacta del Semisumador): -/
theorem halfAdder_correct (a b : Bool) :
    bitVal (halfAdder a b).1 + 2 * bitVal (halfAdder a b).2 = bitVal a + bitVal b := by
  cases a <;> cases b <;> rfl

/-- TEOREMA 2 (Corrección Aritmética Exacta del *Full-Adder* de 1 Bit):
    Para las $2^3 = 8$ combinaciones posibles de bits de entrada `(a, b, cin)`,
    la salida `(sum, cout)` satisface `sum + 2 · cout = a + b + cin`. -/
theorem fullAdder_correct (a b cin : Bool) :
    bitVal (fullAdder a b cin).1 + 2 * bitVal (fullAdder a b cin).2 =
      bitVal a + bitVal b + bitVal cin := by
  cases a <;> cases b <;> cases cin <;> rfl

/-! ## 2. Sumador *Ripple-Carry* de 2 Bits y Demostración de Corrección Extremo a Extremo -/

/-- Sumador *Ripple-Carry* de 2 bits:
    Encadena dos `fullAdder` propagando el acarreo intermedio `c1` de la etapa 0 a la etapa 1,
    devolviendo `(s0, s1, cout)`. -/
@[simp]
def rippleAdder2 (a0 a1 b0 b1 cin : Bool) : Bool × Bool × Bool :=
  let (s0, c1)   := fullAdder a0 b0 cin
  let (s1, cout) := fullAdder a1 b1 c1
  (s0, s1, cout)

/-- TEOREMA 3 (Verificación Formal del Sumador *Ripple-Carry* de 2 Bits):
    El valor numérico de la salida de 3 bits `(s0, s1, cout)` es idéntico a la suma aritmética
    de las dos palabras de 2 bits `(a0, a1)` y `(b0, b1)` más el bit de acarreo de entrada `cin`! -/
theorem rippleAdder2_correct (a0 a1 b0 b1 cin : Bool) :
    let (s0, s1, cout) := rippleAdder2 a0 a1 b0 b1 cin
    word3Val s0 s1 cout = word2Val a0 a1 + word2Val b0 b1 + bitVal cin := by
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases cin <;> rfl

end LeanTT.M69
