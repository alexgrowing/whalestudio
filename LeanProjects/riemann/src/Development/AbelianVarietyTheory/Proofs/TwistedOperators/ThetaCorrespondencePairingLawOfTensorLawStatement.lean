import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondencePairingLawOfTensorLaw
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
theorem _root_.GlobalTheory.T.thetaCorrespondence_pairingLaw_of_tensorLaw : ∀ (p q r s : ℕ) (T₁ : GrpData p q) (σ : Type) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (R₁ : DSRep T₁) (T₂ : GrpData r s) (R₂ : DSRep T₂) (Λ₁ : Ix p q → ℚ) (Λ₂ : Ix r s → ℚ), IsGK a₁ → IsGK a₂ → AdmGK R₁.HK → Module.finrank ℂ ↥(hwSub R₁.HK.act Λ₁) = 1 → TensLaw a₁ a₂ R₁ R₂ Λ₁ Λ₂ → PairLaw a₁ a₂ R₁ R₂ Λ₁ Λ₂ := by
  first | exact @GlobalTheory.ArchRec.PairOfTens.pairLaw_of_tensLaw | exact GlobalTheory.ArchRec.PairOfTens.pairLaw_of_tensLaw | (intros; apply GlobalTheory.ArchRec.PairOfTens.pairLaw_of_tensLaw <;> assumption)
