# Cuaderno 05: Plantillas de Prompts, `AGENTS.md` y Auditoría Formal Anti-Trampas

> **Jupyter Notebook (`.ipynb`) correspondiente:** [`notebooks/05_prompts_agents_y_auditoria_formal.ipynb`](../../notebooks/05_prompts_agents_y_auditoria_formal.ipynb)
> **Navegación:** [⬅ Cuaderno 04: Bucle IA ↔ Compilador](04_cuaderno_bucle_ia_compilador_autoreparacion.md) | [🎓 Volver al Artículo Principal 24](../24_articulo_anatomia_demostracion_lean4_e_ia.md)

---

## 🎯 Objetivo del Cuaderno

Cuando delegas la formalización y demostración de un sistema crítico a una IA, ¿cómo garantizas al 100 % que **no ha hecho trampas sutiles** aunque el archivo `.lean` compile sin errores?

En este último cuaderno aprenderás las **3 auditorías mecánicas obligatorias** (*Spec-Audit*) y tendrás las **3 plantillas de prompts listas para usar**.

---

## Celda 1 — La Trampa Más Peligrosa de una IA: El Teorema Vacuamente Cierto (*Vacuous Truth*)

Observa este código Lean 4. **Compila sin errores, sin `sorry` y sin warnings**, pero la especificación contiene un bug sutil que convierte el teorema de seguridad en papel mojado:

```lean
namespace AuditoriaTrampa

-- ¡CUIDADO! El autor/IA escribió `amount < 0` Y `amount > 100` sobre `Nat`/enteros incompatibles:
def PrecondicionDefectuosa (amount : Int) : Prop :=
  amount < 0 ∧ 100 < amount

-- ¡Este "teorema" demuestra una afirmación FALSA (`2 + 2 = 5` o que nunca se pierden fondos)
-- porque ninguna entrada cumple jamás `PrecondicionDefectuosa`!
theorem teorema_enganoso (amount : Int) (h : PrecondicionDefectuosa amount) :
    amount = 999999 := by
  dsimp [PrecondicionDefectuosa] at h
  omega

end AuditoriaTrampa
```

### 🛡️ Cómo Bloquear Esta Trampa Mecánicamente: El Certificado de No-Vacuidad

En tus instrucciones a la IA, exige siempre que cada precondición `Pre` venga acompañada de un teorema `∃ x, Pre x` probado constructivamente! Si la precondición tenía una contradicción oculta, es **matemáticamente imposible** que la IA demuestre `∃ x, Pre x`:

```lean
namespace AuditoriaSegura

structure Transfer where
  saldoOrigen  : Nat
  saldoDestino : Nat
  importe      : Nat

abbrev PrecondicionValida (tx : Transfer) : Prop :=
  0 < tx.importe ∧ tx.importe ≤ tx.saldoOrigen

def ejecutar (tx : Transfer) : Nat × Nat :=
  (tx.saldoOrigen - tx.importe, tx.saldoDestino + tx.importe)

-- 1. Teorema de seguridad: conservación exacta de fondos
theorem conservacion_fondos (tx : Transfer) (h : PrecondicionValida tx) :
    let (s', r') := ejecutar tx
    s' + r' = tx.saldoOrigen + tx.saldoDestino := by
  dsimp [ejecutar, PrecondicionValida] at *
  omega

-- 2. CERTIFICADO ANTI-VACUIDAD OBLIGATORIO: demuestra que `PrecondicionValida` es satisfacible!
theorem precondicion_no_vacua : ∃ tx : Transfer, PrecondicionValida tx :=
  ⟨⟨500, 100, 120⟩, by decide⟩

-- 3. AUDITORÍA DE AXIOMAS DEL KERNEL: confirma que no se usó `sorryAx` ni `axiom` espurios:
#print axioms conservacion_fondos
#print axioms precondicion_no_vacua

end AuditoriaSegura
```

---

## Celda 2 — Las 3 Plantillas de Prompts Profesionales para Dirigir una IA en Lean 4

### Plantilla A — Prompt de Creación desde Cero con *Blueprint*
```markdown
Quiero formalizar y demostrar en Lean 4 (toolchain v4.35.0, sin `sorry` y con 0 warnings) el
siguiente resultado: [DESCRIPCIÓN DEL TEOREMA].

Sigue estrictamente este protocolo en 4 pasos:
1. ESPECIFICACIÓN Y SANITY CHECK: Define las estructuras y funciones evitando divisiones truncadas
   en `Nat`, y añade 2 pruebas `#eval` sobre ejemplos concretos.
2. BLUEPRINT DE LEMAS: Antes de demostrar el teorema principal, enuncia y demuestra por separado
   los lemas algebraicos o invariantes intermedios (`generalizing` cualquier acumulador o estado).
3. DEMOSTRACIÓN MODULAR: Usa bloques `calc`, `dsimp` y `simp only [...]` acotados.Compila con
   `lean` / `lake build` tras cada bloque y repara cualquier diagnóstico leyendo literalmente la
   meta `⊢` del error.
4. AUDITORÍA FINAL: Demuestra un teorema `∃ x, Pre x` de no-vacuidad y verifica `#print axioms`
   confirmando que no aparece `sorryAx` ni ningún `axiom` ad hoc.
```

### Plantilla B — Prompt de Desbloqueo / Auto-Reparación ante un Error de `lean`
```markdown
La compilación en Lean 4 ha devuelto el siguiente diagnóstico exacto:
<PEGAR SALIDA DEL COMPILADOR LEAN>

NO cambies el enunciado del teorema ni añadas `sorry`. Analiza primero en 3 líneas:
1. Cómo asocia Lean los operadores en la expresión `⊢ ...` mostrada por el error.
2. Si falta generalizar alguna variable en `induction` o alinear factores conmutativos antes de `omega`.
3. Aplica únicamente la reparación mínima necesaria sobre ese bloque y vuelve a verificar con `lake build`.
```

### Plantilla C — Prompt de Revisor Adversario (*Spec-Audit* estilo `TauCeti`)
```markdown
Actúa como auditor formal adversario del archivo `<archivo.lean>` recién compilado:
1. Comprueba que las definiciones corresponden fielmente al concepto matemático/físico real (por
   ejemplo, que no simplifican casos degenerados ni fuerzan constantes triviales).
2. Verifica que todo teorema condicional `P → Q` cuenta con un testigo satisfacible `∃ x, P x`.
3. Comprueba `#print axioms` sobre los teoremas exportados (solo se permiten cero axiomas o los
   axiomas estándar `propext`, `Quot.sound`, `Classical.choice` cuando la prueba requiera lógica
   clásica explícita).
```
