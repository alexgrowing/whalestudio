import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsometryConjTransvectionScale
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_conj_transvection_scale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (G g : Matrix (Fin N) (Fin N) E) (ξ : Fin N → E) (ε : E), IsIsom G g → g.mulVec ξ = ε • ξ → cc ε = ε → ε ≠ 0 → ∀ α : E, g * transvMat G ξ α = transvMat G ξ (ε ^ 2 * α) * g := by
  first | exact @GlobalTheory.UnipKill.mul_transvMat_of_scale | exact GlobalTheory.UnipKill.mul_transvMat_of_scale | (intros; apply GlobalTheory.UnipKill.mul_transvMat_of_scale <;> assumption)
