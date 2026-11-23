import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLowestKTypeMatrixCoeffSqPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoMulRankWLt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_lowestKTypeMatrixCoeff_sq_pos : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, LevProd R i → ∀ v, IsUnitVec R i v → IntegrableOn (lowCoefSq R i v) (realLev R i) (R.νW i) → 0 < ∫ h in realLev R i, lowCoefSq R i v h ∂(R.νW i) := by
  first | exact @GlobalTheory.LowCoefPos.integral_lowCoefSq_pos | exact GlobalTheory.LowCoefPos.integral_lowCoefSq_pos | (intros; apply GlobalTheory.LowCoefPos.integral_lowCoefSq_pos <;> assumption)
