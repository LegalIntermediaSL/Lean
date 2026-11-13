/-!
# Módulo 34: Combinadores de Parsing Funcionalmente Verificados
## Ámbito: Análisis Sintáctico, Gramáticas y Leyes Algebraicas de Parsers

Un parser determinista `Parser α` consume un prefijo de una cadena de tokens `List Char`
y devuelve `Option (α × List Char)` (el valor reconocido junto con el sufijo restante).
En este módulo:
1. Construimos la librería de combinadores `pure`, `fail`, `satisfy`, `char`, `seq`, `orElse`.
2. **Demostramos formalmente** las leyes algebraicas de los combinadores de parsing:
   - Identidad izquierda y derecha de la alternativa `<|>`.
   - Asociatividad de la alternativa `(p1 <|> p2) <|> p3 = p1 <|> (p2 <|> p3)`.
   - Teorema de sufijo monotónico: `satisfy` siempre reduce estrictamente la longitud de la entrada.
-/

namespace LeanTT.M34

structure Parser (α : Type) where
  run : List Char → Option (α × List Char)

namespace Parser

def pure {α : Type} (a : α) : Parser α :=
  ⟨fun input => some (a, input)⟩

def fail {α : Type} : Parser α :=
  ⟨fun _ => none⟩

def satisfy (pred : Char → Bool) : Parser Char :=
  ⟨fun
    | []      => none
    | c :: cs => if pred c then some (c, cs) else none⟩

def char (expected : Char) : Parser Char :=
  satisfy (· == expected)

def bind {α β : Type} (p : Parser α) (f : α → Parser β) : Parser β :=
  ⟨fun input =>
    match p.run input with
    | none           => none
    | some (a, rest) => (f a).run rest⟩

def alt {α : Type} (p1 p2 : Parser α) : Parser α :=
  ⟨fun input =>
    match p1.run input with
    | some res => some res
    | none     => p2.run input⟩

infixl:55 " <|>ₚ " => alt

/-! ## Teoremas Algebraicos de los Combinadores de Parsing -/

/-- `fail` es el elemento neutro por la izquierda de `<|>ₚ` -/
theorem fail_alt {α : Type} (p : Parser α) : (fail <|>ₚ p) = p := by
  cases p
  rfl

/-- `fail` es el elemento neutro por la derecha de `<|>ₚ` -/
theorem alt_fail {α : Type} (p : Parser α) : (p <|>ₚ fail) = p := by
  cases p with
  | mk runP =>
    dsimp [alt, fail]
    congr 1
    funext input
    cases runP input <;> rfl

/-- Asociatividad de la elección ordenada `<|>ₚ` -/
theorem alt_assoc {α : Type} (p1 p2 p3 : Parser α) :
    ((p1 <|>ₚ p2) <|>ₚ p3) = (p1 <|>ₚ (p2 <|>ₚ p3)) := by
  cases p1; cases p2; cases p3
  dsimp [alt]
  congr 1
  funext input
  cases ‹List Char → Option (α × List Char)› input <;> rfl

/-- Teorema de Progreso Léxico (Terminación Garantizada):
    Si `(satisfy pred).run input = some (c, rest)`, entonces `rest.length < input.length`! -/
theorem satisfy_decreases_length (pred : Char → Bool) (input rest : List Char) (c : Char)
    (h : (satisfy pred).run input = some (c, rest)) :
    rest.length < input.length := by
  cases input with
  | nil =>
    contradiction
  | cons x xs =>
    dsimp [satisfy] at h
    split at h
    · injection h with hpair
      injection hpair with _ hrest
      subst hrest
      simp
    · contradiction

end Parser
end LeanTT.M34
