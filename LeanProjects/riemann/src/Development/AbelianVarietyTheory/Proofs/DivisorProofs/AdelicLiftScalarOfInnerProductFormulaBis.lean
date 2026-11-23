import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelCOfInnerProductFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLift_scalar_of_innerProductFormula : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), LiftIsCuspC R F → SourceLevelLawC R F → InnerProductFormulaC R F → FockCoefficientC R F → DeltaNorm D → FiniteZetaC R F → LevelIndexNormC R F → MassLower D → FormalDegreeUpperC R F → AdelC R F := by
  first | exact @GlobalTheory.LowRow.adelC_of_innerProductFormula | exact GlobalTheory.LowRow.adelC_of_innerProductFormula | (intros; apply GlobalTheory.LowRow.adelC_of_innerProductFormula <;> assumption)
