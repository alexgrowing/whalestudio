import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bilinearFischerPairing_matrixEntryPolynomialRing : ∀ (ι : Type) [Fintype ι] (m n : ℕ), ∃ B : Pol ι m n →ₗ[ℂ] Pol ι m n →ₗ[ℂ] ℂ, (∀ Q, (∀ P, B P Q = 0) → Q = 0) ∧ (∀ a b P Q, B (subst a b P) Q = B P (subst (fun τ => (a τ).transpose) (fun τ => (b τ).transpose) Q)) ∧ ∀ (ℓ : Pol ι m n →ₗ[ℂ] ℂ) (d : ℕ), (∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → ℓ (MvPolynomial.monomial α 1) = 0) → ∃ Q, ∀ P, B P Q = ℓ P := by
  first | exact @GlobalTheory.DefLift.BilFischer.exists_pair | exact GlobalTheory.DefLift.BilFischer.exists_pair | (intros; apply GlobalTheory.DefLift.BilFischer.exists_pair <;> assumption)
