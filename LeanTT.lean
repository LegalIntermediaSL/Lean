/-!
# LeanTT: Cálculo Lambda, Teoría de Tipos Dependientes y Demostración Interactiva en Lean 4

Módulo raíz que importa los 25 módulos ejecutables del repositorio.
-/

-- Bloque I: Fundamentos del Cálculo Lambda, Tipos Dependientes y Lógica (M01 - M07)
import LeanTT.M01_LambdaCalculus
import LeanTT.M02_DependentTypes
import LeanTT.M03_UniversesAndProp
import LeanTT.M04_CurryHoward
import LeanTT.M05_InductiveFamilies
import LeanTT.M06_EqualityAndTransport
import LeanTT.M07_TypeClassesAndAlgebra

-- Bloque II: Tácticas, Mónadas, Metateoría de Lenguajes y Metaprogramación (M08 - M13)
import LeanTT.M08_TacticsAndCalculationalProofs
import LeanTT.M09_MonadsAndEffects
import LeanTT.M10_MetatheorySTLC
import LeanTT.M11_OperationalSemantics
import LeanTT.M12_MetaprogrammingAndTactics
import LeanTT.M13_FoundationsOfDependentTypeTheory

-- Bloque III: Módulos Especialmente Didácticos Paso a Paso (M14 - M16)
import LeanTT.M14_DidacticStepByStepProofs
import LeanTT.M15_DidacticDependentTypesFromZero
import LeanTT.M16_DidacticLambdaCubeAndPTS

-- Bloque IV: Ámbitos Avanzados de Aplicación y Verificación Formal (M17 - M25)
import LeanTT.M17_VerifiedDataStructuresBST
import LeanTT.M18_VerifiedSortingAlgorithms
import LeanTT.M19_FiniteStateMachinesAndProtocols
import LeanTT.M20_VerifiedCompilerAndStackMachine
import LeanTT.M21_NumberTheoryAndCryptography
import LeanTT.M22_CategoryTheoryAndFunctors
import LeanTT.M23_HoTTAndHomotopyPaths
import LeanTT.M24_RelationalDatabasesAndTypedSQL
import LeanTT.M25_ModalAndTemporalLogicDSL
