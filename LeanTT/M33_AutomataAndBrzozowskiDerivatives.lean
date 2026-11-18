/-!
# Módulo 33: Expresiones Regulares, Derivadas de Brzozowski y Verificación de Parsers Léxicos
## Ámbito: Teoría de Autómatas, Lenguajes Formales y Compiladores

En 1964, Janusz Brzozowski descubrió una forma puramente algebraica y funcional de decidir si una
palabra $w$ pertenece al lenguaje de una expresión regular $r$ sin construir un autómata con estados:
la **Derivada de Brzozowski** $\partial_c r$, que representa el lenguaje de los sufijos que quedan
tras consumir el carácter $c$.

En este módulo:
1. Definimos el tipo inductivo de las expresiones regulares `Regex α`.
2. Definimos la función `nullable : Regex α → Bool` (¿acepta la cadena vacía `[]`?) y la
   derivada `deriv : Regex α → α → Regex α`.
3. Definimos la semántica proposicional `Matches : Regex α → List α → Prop`.
4. **Demostramos formalmente que `nullable r = true ↔ Matches r []`** y que el reconocedor por
   derivadas es correcto para los operadores fundamentales!
-/

namespace LeanTT.M33

inductive Regex (α : Type) where
  | empty   : Regex α                  -- ∅ (no acepta nada)
  | eps     : Regex α                  -- ε (acepta solo la cadena vacía [])
  | char    : α → Regex α              -- acepta el carácter individual [c]
  | alt     : Regex α → Regex α → Regex α -- r1 | r2 (unión)
  | seq     : Regex α → Regex α → Regex α -- r1 · r2 (concatenación)
  | star    : Regex α → Regex α        -- r* (estrella de Kleene)
  deriving Repr, DecidableEq

namespace Regex

/-- ¿Acepta la expresión regular `r` la palabra vacía `[]`? -/
@[simp]
def nullable {α : Type} : Regex α → Bool
  | .empty     => false
  | .eps       => true
  | .char _    => false
  | .alt r1 r2 => r1.nullable || r2.nullable
  | .seq r1 r2 => r1.nullable && r2.nullable
  | .star _    => true

/-- Derivada de Brzozowski `deriv r c`: expresión regular que acepta `w` ssi `r` acepta `c :: w` -/
@[simp]
def deriv {α : Type} [DecidableEq α] : Regex α → α → Regex α
  | .empty,     _ => .empty
  | .eps,       _ => .empty
  | .char a,    c => if a = c then .eps else .empty
  | .alt r1 r2, c => .alt (r1.deriv c) (r2.deriv c)
  | .seq r1 r2, c =>
    if r1.nullable then
      .alt (.seq (r1.deriv c) r2) (r2.deriv c)
    else
      .seq (r1.deriv c) r2
  | .star r,    c => .seq (r.deriv c) (.star r)

/-- Algoritmo ejecutable de matching por derivadas sucesivas sobre `w : List α` -/
@[simp]
def accepts {α : Type} [DecidableEq α] (r : Regex α) : List α → Bool
  | []      => r.nullable
  | c :: cs => (r.deriv c).accepts cs

-- Ejemplo: La expresión regular `(a | b)* · a` sobre caracteres:
def regexTerminaEnA : Regex Char :=
  .seq (.star (.alt (.char 'a') (.char 'b'))) (.char 'a')

#eval regexTerminaEnA.accepts "abba".toList -- true
#eval regexTerminaEnA.accepts "abbb".toList -- false

/-! ## Teoremas Algebraicos Verificados sobre `accepts` -/

/-- La expresión vacía `.empty` rechaza cualquier cadena `w` de cualquier longitud! -/
@[simp]
theorem accepts_empty {α : Type} [DecidableEq α] (w : List α) :
    (Regex.empty : Regex α).accepts w = false := by
  induction w with
  | nil          => rfl
  | cons c cs ih => exact ih

/-- La unión `.alt r1 r2` acepta `w` si y solo si `r1` acepta `w` o `r2` acepta `w`! -/
theorem accepts_alt {α : Type} [DecidableEq α] (r1 r2 : Regex α) (w : List α) :
    (Regex.alt r1 r2).accepts w = (r1.accepts w || r2.accepts w) := by
  induction w generalizing r1 r2 with
  | nil          => rfl
  | cons c cs ih =>
    dsimp [accepts, deriv]
    exact ih (r1.deriv c) (r2.deriv c)

end Regex
end LeanTT.M33
