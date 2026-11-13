-- Bloque I: Fundamentos del Cálculo Lambda, Tipos Dependientes y Lógica (M01 - M07, M13)
import LeanTT.M01_LambdaCalculus
import LeanTT.M02_DependentTypes
import LeanTT.M03_UniversesAndProp
import LeanTT.M04_CurryHoward
import LeanTT.M05_InductiveFamilies
import LeanTT.M06_EqualityAndTransport
import LeanTT.M07_TypeClassesAndAlgebra
import LeanTT.M13_FoundationsOfDependentTypeTheory

-- Bloque II: Tácticas, Mónadas, Metateoría de Lenguajes y Metaprogramación (M08 - M12)
import LeanTT.M08_TacticsAndCalculationalProofs
import LeanTT.M09_MonadsAndEffects
import LeanTT.M10_MetatheorySTLC
import LeanTT.M11_OperationalSemantics
import LeanTT.M12_MetaprogrammingAndTactics

-- Bloque III: Módulos Especialmente Didácticos Paso a Paso (M14 - M16) y Ejercicios
import LeanTT.M14_DidacticStepByStepProofs
import LeanTT.M15_DidacticDependentTypesFromZero
import LeanTT.M16_DidacticLambdaCubeAndPTS
import LeanTT.Exercises.E01_WorkoutLambdaAndLogic
import LeanTT.Solutions.S01_WorkoutLambdaAndLogic

-- Bloque IV: 24 Ámbitos Avanzados de Aplicación y Verificación Formal (M17 - M40)
import LeanTT.M17_VerifiedDataStructuresBST
import LeanTT.M18_VerifiedSortingAlgorithms
import LeanTT.M19_FiniteStateMachinesAndProtocols
import LeanTT.M20_VerifiedCompilerAndStackMachine
import LeanTT.M21_NumberTheoryAndCryptography
import LeanTT.M22_CategoryTheoryAndFunctors
import LeanTT.M23_HoTTAndHomotopyPaths
import LeanTT.M24_RelationalDatabasesAndTypedSQL
import LeanTT.M25_ModalAndTemporalLogicDSL
import LeanTT.M26_SystemFAndParametricity
import LeanTT.M27_NormalizationByEvaluation
import LeanTT.M28_SubstructuralAndLinearTypes
import LeanTT.M29_SeparationLogicAndHeap
import LeanTT.M30_SmartContractsAndEVMState
import LeanTT.M31_SumCheckProtocolAndOracles
import LeanTT.M32_ComputablePolynomialsAndFields
import LeanTT.M33_AutomataAndBrzozowskiDerivatives
import LeanTT.M34_VerifiedParserCombinators
import LeanTT.M35_SQLQueryOptimizerCorrectness
import LeanTT.M36_GaloisConnectionsAndLattices
import LeanTT.M37_StreamsAndBisimulation
import LeanTT.M38_VerifiedAutomaticDifferentiation
import LeanTT.M39_ProofByReflectionAndBitVectors
import LeanTT.M40_MiniDependentTypeChecker

/-!
# LeanTT: Cálculo Lambda, Teoría de Tipos Dependientes y Demostración Interactiva en Lean 4

Módulo raíz que importa los **40 módulos ejecutables (`M01`–`M40`)** y los talleres de
ejercicios y soluciones (`E01` / `S01`).
-/
