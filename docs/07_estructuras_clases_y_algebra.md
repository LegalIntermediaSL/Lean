# Módulo 07: Estructuras como Telescopios $\Sigma$, Diseño Algebraico (*Bundled vs. Unbundled*) y Clases de Tipos

> **Archivo Lean ejecutable asociado:** [`LeanTT/M07_TypeClassesAndAlgebra.lean`](../LeanTT/M07_TypeClassesAndAlgebra.lean)

---

## Índice del Módulo
1. [Telescopios de De Bruijn y Estructuras Dependientes](#1-telescopios-de-de-bruijn-y-estructuras-dependientes)
2. [El Gran Dilema del Diseño Formal: *Bundled* vs. *Unbundled*](#2-el-gran-dilema-del-diseño-formal-bundled-vs-unbundled)
3. [Herencia en Diamante y Subestructuras Planas en Lean 4](#3-herencia-en-diamante-y-subestructuras-planas-en-lean-4)
4. [Resolución Tabulada de Clases de Tipos, Prioridades e Instancias Locales](#4-resolución-tabulada-de-clases-de-tipos-prioridades-e-instancias-locales)
5. [Parámetros de Salida (`outParam` y `semiOutParam`) en Clases Multiparamétricas](#5-parámetros-de-salida-outparam-y-semioutparam-en-clases-multiparamétricas)
6. [Coerciones Dependientes (`Coe`, `CoeDep`, `CoeSort`, `CoeFun`) con Ejemplos](#6-coerciones-dependientes-coe-coedep-coesort-coefun-con-ejemplos)

---

## 1. Telescopios de De Bruijn y Estructuras Dependientes

Un **telescopio** (término acuñado por N. G. de Bruijn) es una secuencia de declaraciones de variables donde el tipo de cada campo depende de los valores de los campos anteriores:

$$(x_1 : A_1)\; (x_2 : A_2(x_1))\; (x_3 : A_3(x_1, x_2)) \dots (x_n : A_n(x_1, \dots, x_{n-1}))$$

En Lean 4, el comando `structure` empaqueta cualquier telescopio en un único tipo con proyecciones con nombre y $\eta$-conversión definicional:

```lean
namespace DemoCat
universe u v

/-- Una categoría pequeña expresada como una estructura dependiente (telescopio de 6 niveles): -/
structure MiniCategoria where
  Obj       : Type u
  Hom       : Obj → Obj → Type v
  id        : (X : Obj) → Hom X X
  comp      : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  id_comp   : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  comp_id   : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  comp_assoc: ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
                comp (comp f g) h = comp f (comp g h)

end DemoCat
```
Observa cómo cada campo depende de los anteriores:
* `Hom` depende del campo `Obj`.
* `id` y `comp` dependen tanto de `Obj` como de `Hom`.
* `id_comp`, `comp_id` y `comp_assoc` son proposiciones en `Prop` cuyos tipos dependen de `Obj`, `Hom`, `id` y `comp`.

### Ejemplo 1.1: La Categoría `Types` de los Tipos y Funciones de Lean 4
```lean
open DemoCat

universe u

def CategoriaDeTipos : MiniCategoria.{u + 1, u} where
  Obj        := Type u
  Hom A B    := A → B
  id _ x     := x
  comp f g x := g (f x)
  id_comp _  := rfl
  comp_id _  := rfl
  comp_assoc _ _ _ := rfl
```

---

## 2. El Gran Dilema del Diseño Formal: *Bundled* vs. *Unbundled*

Al formalizar álgebra o topología en teoría de tipos dependientes existen dos patrones arquitectónicos:

### 2.1 Enfoque Empaquetado (*Bundled* — el estilo de `MiniCategoria` arriba)
El tipo portador (`carrier : Type u`) es un **campo dentro de la estructura**:
```text
structure GrupoEmpaquetado where
  carrier : Type u
  mul     : carrier → carrier → carrier
  ...
```
* **Ventaja:** Los grupos empaquetados forman a su vez un tipo `GrupoEmpaquetado : Type (u+1)`, lo que es ideal cuando quieres hablar de la **categoría de todos los grupos** (`Grp`).
* **Desventaja:** Un mismo tipo como `Int` no es directamente un `GrupoEmpaquetado`, sino que necesita una coerción `CoeSort`, y es difícil compartir el mismo portador `Int` entre su estructura de grupo aditivo, monoide multiplicativo y orden lineal sin llenarse de proyecciones.

### 2.2 Enfoque Desempaquetado con Clases de Tipos (*Semi-Bundled Typeclasses* — el estándar en Lean 4 y Mathlib4)
El tipo portador $\alpha : \texttt{Type } u$ es un **parámetro** de una `class`, mientras que las operaciones y los axiomas están empaquetados juntos dentro de la clase:
```lean
class Grupo (G : Type u) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul   : ∀ a : G, 1 * a = a
  inv_mul   : ∀ a : G, a⁻¹ * a = 1
```
* **Ventaja:** Puedes escribir teoremas sobre `(G : Type u) [Grupo G]` y aplicarlos directamente a `Int`, `Rat`, `Real` o `G × H` sin ninguna proyección explícita: Lean sintetiza la instancia `[Grupo G]` automáticamente.

---

## 3. Herencia en Diamante y Subestructuras Planas en Lean 4

En Lean 3, cuando `C extends A, B` y tanto `A` como `B` extendían una estructura base `Base`, se creaban subestructuras anidadas `toA` y `toB`. En **Lean 4**, el nuevo mecanismo de `structure` **aplana los campos no repetidos** directamente dentro de `C` y genera las funciones de proyección `toA` y `toB` como constructores al vuelo, garantizando que:

```lean
class Base (α : Type) where
  op : α → α → α

class Izquierda (α : Type) extends Base α where
  propIzq : ∀ x : α, op x x = x

class Derecha (α : Type) extends Base α where
  propDer : ∀ x y : α, op x y = op y x

class Diamante (α : Type) extends Izquierda α, Derecha α

-- En Lean 4, la operación `op` heredada por la vía `Izquierda` y por la vía `Derecha`
-- son DEFINICIONALMENTE IDÉNTICAS (`rfl`):
example {α : Type} [inst : Diamante α] :
    inst.toIzquierda.toBase = inst.toDerecha.toBase :=
  rfl
```

---

## 4. Parámetros de Salida (`outParam`) en Clases Multiparamétricas

Imagina que quieres definir una clase `Contiene (Contenedor : Type) (Elemento : outParam Type)` para que funcione la operación `pertenece (x : Elemento) (c : Contenedor) : Bool` tanto en `List Nat` como en `ByteArray` (cuyo tipo `ByteArray` no menciona `UInt8` como argumento sintáctico).

```lean
class Membresia (C : Type u) (α : outParam (Type v)) where
  mem : α → C → Prop

instance {α : Type u} : Membresia (List α) α where
  mem x xs := x ∈ xs

instance : Membresia String Char where
  mem c s := c ∈ s.toList
```
Gracias a `outParam`, cuando Lean ve `Membresia.mem x miString`, sabe que el contenedor es `String` e infiere inmediatamente que `x` debe ser de tipo `Char`.

---

## 5. Coerciones Dependientes (`Coe`, `CoeDep`, `CoeSort`, `CoeFun`) con Ejemplos

```lean
-- 1. `CoeSort`: Permite tratar un `Subconjunto` o un `GrupoEmpaquetado` como si fuera un `Type`:
structure Subconjunto (α : Type u) where
  pred : α → Prop

instance {α : Type u} : CoeSort (Subconjunto α) (Type u) where
  coe S := { x : α // S.pred x }

def NaturalesPares : Subconjunto Nat := ⟨fun n => n % 2 = 0⟩

-- Gracias a `CoeSort`, podemos escribir `(x : NaturalesPares)` como si fuera un tipo!
def duplicarPar (x : NaturalesPares) : Nat :=
  x.val * 2
```
