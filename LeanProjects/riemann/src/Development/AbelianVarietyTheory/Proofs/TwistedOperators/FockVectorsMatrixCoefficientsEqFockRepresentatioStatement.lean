import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsMatrixCoefficientsEqFockRepresentatio
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_matrixCoefficients_eq_fockRepresentation : ∀ (p q r s n : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q) (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (ι Z : Type) (G fr : Mn n) (ε : Fin n → Bool) (br : Bool) (e : Ix p q ≃ Fin n) (A : Mn n → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (ip : (Z → ℂ) → (Z → ℂ) → ℂ) (Θ : Submodule ℂ (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] Pol p q r s) (c : ℚ) (m : ℤ) (N : ℝ), 1 ≤ p + q → IsUnit fr → frᴴ * Formalism.REAL.Jm ε * fr = G → SignCompat ε e → (m : ℚ) = 2 * c → Side A pt κ (phiFr fr br e) c (fockAct1 p q r s) → L2UnitaryRepresentationData G A pt ip Θ → Fischer pt ip κ N → Coef F A pt ip κ (phiFr fr br e) m N := by
  first | exact @GlobalTheory.ArchRec.FockCoef.coef_of_side | exact GlobalTheory.ArchRec.FockCoef.coef_of_side | (intros; apply GlobalTheory.ArchRec.FockCoef.coef_of_side <;> assumption)
