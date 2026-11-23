import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoZeroOfOpenSetLinearRoots
import Mathlib
import Formalism.DegreeFormula.FlagDegFormula
open MvPolynomial Formalism.DegreeFormula Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_zero_of_open_set_linear_roots : ∀ {α : Type} (l : Filter α) {ι : Type} [Fintype ι] {N : ℕ} (Λ : α → MvPolynomial (ι × Fin N) ℝ →ₗ[ℝ] ℝ) (d : ℕ) (U : Set (ι → Fin N → ℝ)), IsOpen U → U.Nonempty → (∀ u ∈ U, Tendsto (fun a => Λ a (linRoot u ^ d)) l (𝓝 0)) → ∀ v : ι → Fin N → ℝ, Tendsto (fun a => Λ a (linRoot v ^ d)) l (𝓝 0) := by
  first | exact @GlobalTheory.tendsto_zero_linRoot_pow_of_isOpen | exact GlobalTheory.tendsto_zero_linRoot_pow_of_isOpen | (intros; apply GlobalTheory.tendsto_zero_linRoot_pow_of_isOpen <;> assumption)
