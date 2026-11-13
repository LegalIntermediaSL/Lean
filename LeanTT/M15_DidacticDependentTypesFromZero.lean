/-!
# Módulo 15 (Especialmente Didáctico): Tipos Dependientes con Ejemplos Cotidianos
## Del Mundo Real a los Tipos Π, Σ, Familias Inductivas y Subtipos

¿Por qué querría un programador o matemático que un **tipo dependa de un valor**?
Aquí lo vemos con 4 metáforas y ejemplos cotidianos inmediatamente comprensibles:
1. **El Menú del Restaurante (`Π-Type`):** El tipo del plato que te sirven depende de lo que pides.
2. **La Caja Sorpresa Etiquetada (`Σ-Type`):** Una caja que por fuera dice qué contiene y por dentro guarda un objeto de ese tipo exacto.
3. **Listas No Vacías y Cajeros sin Descubierto (`Subtype`):** Prohibir errores de ejecución por diseño.
4. **El Ascensor Seguro (`Familia Inductiva Indexada`):** No se puede bajar desde la planta 0 ni subir más allá de la azotea.
-/

namespace LeanTT.M15

/-! ## Ejemplo Cotidiano 1: El Menú del Restaurante (Función Dependiente / Π-Type) -/

inductive Pedido where
  | bebida
  | postre
  | cuenta
  deriving Repr, DecidableEq

inductive Bebida where | agua | cafe deriving Repr
inductive Postre where | flan | fruta deriving Repr

/-- ¡Esta función recibe un VALOR (`p : Pedido`) y devuelve un TIPO (`Type`)! -/
def TipoDeRespuesta : Pedido → Type
  | .bebida => Bebida
  | .postre => Postre
  | .cuenta => Nat       -- El importe a pagar en euros

/-- `servirPedido` tiene el Π-tipo `(p : Pedido) → TipoDeRespuesta p`:
    - Si pides `.bebida`, está OBLIGADA por el compilador a devolver una `Bebida`.
    - Si pides `.postre`, está OBLIGADA a devolver un `Postre`.
    - Si pides `.cuenta`, está OBLIGADA a devolver un `Nat`. -/
def servirPedido : (p : Pedido) → TipoDeRespuesta p
  | .bebida => Bebida.cafe
  | .postre => Postre.flan
  | .cuenta => 15

#eval servirPedido .bebida -- Bebida.cafe : Bebida
#eval servirPedido .postre -- Postre.flan : Postre
#eval servirPedido .cuenta -- 15 : Nat

/-! ## Ejemplo Cotidiano 2: La Caja Etiquetada (Par Dependiente / Σ-Type) -/

/-- Una `CajaDeRestaurante` es un par dependiente `(p : Pedido) × TipoDeRespuesta p`:
    su primer elemento es la etiqueta `p : Pedido`, y su segundo elemento tiene tipo
    `TipoDeRespuesta p`. ¡No puedes meter un `Postre` si la etiqueta dice `.bebida`! -/
abbrev CajaDeRestaurante := (p : Pedido) × TipoDeRespuesta p

def bandejaDelCamarero : List CajaDeRestaurante :=
  [ ⟨.bebida, Bebida.agua⟩
  , ⟨.postre, Postre.fruta⟩
  , ⟨.cuenta, 28⟩
  ]

/-! ## Ejemplo Cotidiano 3: Cuenta Bancaria sin Descubierto (Refinamiento y Pruebas) -/

/-- Una `CuentaBancaria` cuyo saldo es un número natural siempre no negativo -/
structure CuentaBancaria where
  titular : String
  saldo   : Nat
  deriving Repr

/-- `retirarDinero` exige como tercer argumento una **demostración formal** `h : monto ≤ c.saldo`.
    ¡Es imposible llamar a `retirarDinero` para sacar más dinero del que hay en la cuenta! -/
def retirarDinero (c : CuentaBancaria) (monto : Nat) (_h : monto ≤ c.saldo) : CuentaBancaria :=
  { c with saldo := c.saldo - monto }

def cuentaAda : CuentaBancaria := ⟨"Ada Lovelace", 500⟩

-- Esta llamada compila porque `200 ≤ 500` es verdadero (`by decide`):
#eval retirarDinero cuentaAda 200 (by decide)

-- Si intentáramos escribir `retirarDinero cuentaAda 900 (by decide)`,
-- el compilador rechazaría el programa en tiempo de compilación!

/-- Demostración formal de que tras retirar `monto`, el saldo nuevo más `monto`
    es exactamente igual al saldo original (conservación del dinero): -/
theorem conservacion_del_dinero (c : CuentaBancaria) (monto : Nat) (h : monto ≤ c.saldo) :
    (retirarDinero c monto h).saldo + monto = c.saldo := by
  dsimp [retirarDinero]
  omega

/-! ## Ejemplo Cotidiano 4: El Ascensor de 5 Plantas (`0..4`) Indexado por Planta -/

/-- `AccionAscensor plantaActual plantaDestino` modela los botones válidos desde cada planta
    en un edificio de plantas 0, 1, 2, 3, 4: -/
inductive AccionAscensor : Nat → Nat → Type where
  | subir   : {p : Nat} → (h : p < 4) → AccionAscensor p (p + 1)
  | bajar   : {p : Nat} → AccionAscensor (p + 1) p
  | esperar : {p : Nat} → AccionAscensor p p

/-- Una secuencia válida de movimientos del ascensor desde la planta `p1` hasta `p2` -/
inductive RutaAscensor : Nat → Nat → Type where
  | fin  : {p : Nat} → RutaAscensor p p
  | paso : {p1 p2 p3 : Nat} → AccionAscensor p1 p2 → RutaAscensor p2 p3 → RutaAscensor p1 p3

/-- Ejemplo de ruta válida desde la planta 0 hasta la planta 1 (sube a 1, sube a 2, baja a 1):
    Observa que intentar poner `.bajar` estando en la planta 0 ni siquiera compilaría. -/
def rutaValida : RutaAscensor 0 1 :=
  .paso (.subir (by decide))
    (.paso (.subir (by decide))
      (.paso .bajar .fin))

end LeanTT.M15
