import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroHermOfSkew
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_herm_of_skew : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (G : Matrix (Fin N) (Fin N) E) (κ : E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → cc κ = -κ → κ ≠ 0 → ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n → n ≠ 0 → ∃ x, herm G (n.mulVec x) x ≠ 0 := by
  first | exact @GlobalTheory.UnipKill.exists_herm_mulVec_self_ne_zero | exact GlobalTheory.UnipKill.exists_herm_mulVec_self_ne_zero | (intros; apply GlobalTheory.UnipKill.exists_herm_mulVec_self_ne_zero <;> assumption)
