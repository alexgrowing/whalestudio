import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockJointHarmonicVectorsIffPolynomials
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
theorem _root_.GlobalTheory.T.fockJointHarmonic_vectors_iff_polynomials : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : HSp D) (S' : D.what₂.Tau → SPar) (N : DSModel W S') (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (B : Mn W.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (l₂ : Ix r s → ℚ) (c₁ c₂ : ℚ) (b₁ b₂ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (e₂ : Ix r s ≃ Fin W.rank) (u₁ : kfin M τ → R₁.HK.V) (u₂ : kfin N τ → R₂.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → KTie R₂ N τ l₂ c₂ b₂ false e₂ u₂ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → Side B pt κ (phiFr (N.fr τ) b₂ e₂) c₂ a₂ → Graded κ → ∀ Φ, IsJoint M τ A pt N B Φ ↔ CJoint a₁ a₂ (blattner l₁) (blattner l₂) (κ Φ) := by
  first | exact @GlobalTheory.ArchRec.JointTransfer.isJoint_iff_cJoint | exact GlobalTheory.ArchRec.JointTransfer.isJoint_iff_cJoint | (intros; apply GlobalTheory.ArchRec.JointTransfer.isJoint_iff_cJoint <;> assumption)
