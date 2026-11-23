import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowMemArithmeticSubgroupOfStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mem_arithmetic_subgroup_of_stabilizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (g : GL (Fin N) E), IsUStab X.Gm X.Λ g → ∃ k : ℕ, 0 < k ∧ g ^ k ∈ X.Γ := by
  first | exact @GlobalTheory.UnipKill.pow_mem_of_isUStab | exact GlobalTheory.UnipKill.pow_mem_of_isUStab | (intros; apply GlobalTheory.UnipKill.pow_mem_of_isUStab <;> assumption)
