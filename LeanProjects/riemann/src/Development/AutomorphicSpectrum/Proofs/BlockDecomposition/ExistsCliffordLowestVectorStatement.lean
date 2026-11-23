import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCliffordLowestVector
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clifford_lowest_vector : ∀ n : ℕ, ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (c : Fin n → Fin n → Matrix ι ι ℂ),
    IsCliff c ∧ ∃ q : ι → ℂ, q ≠ 0 ∧ ∀ a b, a < b → c b a *ᵥ q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CliffModel.exists_cliff_model | exact GlobalTheory.CompanionTheory.CliffModel.exists_cliff_model | (intros; apply GlobalTheory.CompanionTheory.CliffModel.exists_cliff_model <;> assumption)
