import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryStabilizerScalingIsotropic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_stabilizer_scaling_isotropic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (ξ η : Fin N → E) (d : ℕ) (ε : E) (c : 𝓞 E), 0 < d → ξ ∈ X.Λ → η ∈ X.Λ → herm X.Gm ξ ξ = 0 → herm X.Gm η η = 0 → herm X.Gm ξ η = d → cc ε = ε → ε ≠ 0 → IsIntegral ℤ ε → IsIntegral ℤ ε⁻¹ → ε - 1 = d * X.den * c → ∃ g : GL (Fin N) E, IsUStab X.Gm X.Λ g ∧ (g : Matrix (Fin N) (Fin N) E).mulVec ξ = ε • ξ := by
  first | exact @GlobalTheory.UnipKill.exists_isUStab_hypRot | exact GlobalTheory.UnipKill.exists_isUStab_hypRot | (intros; apply GlobalTheory.UnipKill.exists_isUStab_hypRot <;> assumption)
