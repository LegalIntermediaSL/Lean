/-!
# Módulo 24: Bases de Datos Relacionales y Álgebra Relacional Dependientemente Tipada
## Ámbito: Ingeniería de Datos, Consultas Tipadas y Compiladores de SQL

En este módulo usamos tipos dependientes para construir un **motor de álgebra relacional en memoria**
donde:
1. Un esquema `Schema` es una lista de pares `(nombreColumna, TipoColumna)`.
2. El tipo de una fila `Row s` es una función dependiente que calcula el tipo exacto de la tupla
   a partir del esquema `s`.
3. Las operaciones `selectWhere`, `crossJoin` y `projectFirst` calculan **estáticamente** el
   esquema de la tabla resultante. ¡Un error de tipos en una columna es imposible en ejecución!
-/

namespace LeanTT.M24

/-- Universo de tipos soportados por nuestras columnas de base de datos -/
inductive DBType where
  | nat  : DBType
  | str  : DBType
  | bool : DBType
  deriving DecidableEq, Repr

/-- Interpretación dependiente de un `DBType` como un `Type` real de Lean 4 -/
@[simp]
def DBType.denote : DBType → Type
  | .nat  => Nat
  | .str  => String
  | .bool => Bool

/-- Un esquema de tabla es una lista de atributos `(nombre, tipo)` -/
abbrev Schema := List (String × DBType)

/-- El tipo dependiente `Row s` calcula el tipo de una fila que cumple el esquema `s` -/
@[simp]
def Row : Schema → Type
  | []           => Unit
  | (_, t) :: s' => t.denote × Row s'

/-- Una tabla con esquema `s` es una lista de filas de tipo `Row s` -/
abbrev Table (s : Schema) := List (Row s)

/-! ## Operaciones del Álgebra Relacional Tipada -/

/-- 1. Selección (`WHERE`): Filtra las filas de una tabla manteniendo su esquema `s` -/
def selectWhere {s : Schema} (pred : Row s → Bool) (tbl : Table s) : Table s :=
  tbl.filter pred

/-- 2. Concatenación de dos filas para el `CROSS JOIN`:
    Concatena una fila de esquema `s1` con una fila de esquema `s2` produciendo una fila
    del esquema combinado `s1 ++ s2`. -/
def appendRow : {s1 s2 : Schema} → Row s1 → Row s2 → Row (s1 ++ s2)
  | [],          _,  (),      r2 => r2
  | (_, _) :: _, _,  (x, r1), r2 => (x, appendRow r1 r2)

/-- 3. Producto Cartesiano (`CROSS JOIN`) tipado entre dos tablas de esquemas `s1` y `s2` -/
def crossJoin {s1 s2 : Schema} (t1 : Table s1) (t2 : Table s2) : Table (s1 ++ s2) :=
  t1.flatMap (fun r1 => t2.map (fun r2 => appendRow r1 r2))

/-- Teorema verificado sobre nuestra operación relacional `selectWhere`:
    Filtrar con dos predicados consecutivos es equivalente a filtrar con su conjunción `&&`. -/
theorem selectWhere_and {s : Schema} (p q : Row s → Bool) (tbl : Table s) :
    selectWhere p (selectWhere q tbl) = selectWhere (fun r => q r && p r) tbl := by
  dsimp [selectWhere]
  rw [List.filter_filter]
  congr 1
  funext r
   exact Bool.and_comm (p r) (q r)

/-! ## Ejemplo Práctico de Consulta Relacional Tipada -/

def UsuariosSchema : Schema :=
  [("id", .nat), ("nombre", .str), ("premium", .bool)]

def tablaUsuarios : Table UsuariosSchema :=
  [ (1, ("Alonzo Church", (true, ())))
  , (2, ("Haskell Curry", (false, ())))
  , (3, ("Per Martin-Löf", (true, ())))
  ]

def usuariosPremium : Table UsuariosSchema :=
  selectWhere (fun (_, (_, (esPremium, ()))) => esPremium) tablaUsuarios

#eval usuariosPremium.length -- 2

end LeanTT.M24
