import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCountProdOfIdempotentSeparable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCount_prod_of_idempotent_separable : ∀ (K : UQ) (B₁ B₂ : InvAlg K), ((1, 0) : B₁.A × B₂.A) ∈ Algebra.adjoin K.O ({(B₁.g, B₂.g)} : Set (B₁.A × B₂.A)) → (B₁.P * B₂.P).Separable → ∀ (x₁ : B₁.A) (x₂ : B₂.A), IsUnit x₁ → IsUnit x₂ → B₁.σ x₁ = x₁ → B₂.σ x₂ = x₂ → (B₁.prod B₂).N (x₁, x₂) = B₁.N x₁ * B₂.N x₂ := by
  first | exact @GlobalTheory.UnitLemma.ProdCount.N_prod | exact GlobalTheory.UnitLemma.ProdCount.N_prod | (intros; apply GlobalTheory.UnitLemma.ProdCount.N_prod <;> assumption)
