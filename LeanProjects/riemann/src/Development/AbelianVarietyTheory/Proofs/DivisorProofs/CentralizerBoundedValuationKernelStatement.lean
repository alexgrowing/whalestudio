import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerBoundedValuationKernel
import Mathlib
open Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_bounded_valuation_kernel : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] L →
    ∀ (n : ℕ) (N : GL (Fin n) L), N.val.charpoly.Separable →
    ∃ (v : Subgroup.centralizer {N} →* Multiplicative (Fin n → ℤ)) (c : ℝ),
      ∀ z : Subgroup.centralizer {N}, v z = 1 → ∀ i j,
        ‖((((z : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ c := by
  first | (exact @GlobalTheory.CentValHom.centralizer_valHom_bounded_ker) | (exact GlobalTheory.CentValHom.centralizer_valHom_bounded_ker) | (intros; apply GlobalTheory.CentValHom.centralizer_valHom_bounded_ker  <;> assumption)
