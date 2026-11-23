import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianVectorEigenDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Formalism.BasicNotions.TH Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_vector_eigen_decomposition : ∀ {n : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ), Mᴴ = M → IsCartan M θ → x ≠ 0 →
    x ⬝ᵥ M *ᵥ star x = 0 →
    ∃ (e f : Fin n → ℂ) (k : ℂ), k ≠ 0 ∧ x = k • (e + f) ∧ θ *ᵥ x = k • (e - f) ∧ θ *ᵥ e = e ∧ θ *ᵥ f = -f ∧
      e ⬝ᵥ M *ᵥ star e = 1 ∧ f ⬝ᵥ M *ᵥ star f = -1 ∧ e ⬝ᵥ M *ᵥ star f = 0 ∧ f ⬝ᵥ M *ᵥ star e = 0 ∧
      ∀ u : Fin n → ℂ, u ⬝ᵥ M *ᵥ star x = 0 → u ⬝ᵥ M *ᵥ star (θ *ᵥ x) = 0 →
        u ⬝ᵥ M *ᵥ star e = 0 ∧ u ⬝ᵥ M *ᵥ star f = 0 ∧ e ⬝ᵥ M *ᵥ star u = 0 ∧ f ⬝ᵥ M *ᵥ star u = 0 := by
  first | exact @GlobalTheory.hyperbolic_pair_of_cartan_isotropic | exact GlobalTheory.hyperbolic_pair_of_cartan_isotropic | (intros; apply GlobalTheory.hyperbolic_pair_of_cartan_isotropic <;> assumption)
