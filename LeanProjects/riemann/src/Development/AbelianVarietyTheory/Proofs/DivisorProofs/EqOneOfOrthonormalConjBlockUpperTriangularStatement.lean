import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfOrthonormalConjBlockUpperTriangular
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_orthonormal_conj_block_upper_triangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ γ ∈ X.Γ, (∀ τ, (KU.gm X x0 γ τ).toBlocks₁₂ = 0) → γ = 1 := by
  first | exact @GlobalTheory.ScalarPoin.BlockFree.eq_one_of_gm_toBlocks₁₂ | exact GlobalTheory.ScalarPoin.BlockFree.eq_one_of_gm_toBlocks₁₂ | (intros; apply GlobalTheory.ScalarPoin.BlockFree.eq_one_of_gm_toBlocks₁₂ <;> assumption)
