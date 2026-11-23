import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaMapModelsOfNoPairingCovers
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
theorem _root_.GlobalTheory.T.noThetaMap_models_of_noPairing_covers : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q : ℕ) (T₁ : GrpData p q) (R₁ : DSRep T₁) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (c₁ : ℚ) (b₁ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (u₁ : kfin M τ → R₁.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → PairNo a₁ R₁ → NoLift M τ A pt := by
  first | exact @GlobalTheory.ArchRec.NoLiftTransfer.noLift_of_pairNo | exact GlobalTheory.ArchRec.NoLiftTransfer.noLift_of_pairNo | (intros; apply GlobalTheory.ArchRec.NoLiftTransfer.noLift_of_pairNo <;> assumption)
