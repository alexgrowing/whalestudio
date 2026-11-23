import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsotropicDualLatticeVector
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_dual_lattice_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (ξ : Fin N → E), ξ ∈ X.Λ → ξ ≠ 0 → herm X.Gm ξ ξ = 0 → ∃ (η : Fin N → E) (d : ℕ), 0 < d ∧ η ∈ X.Λ ∧ herm X.Gm ξ η = d ∧ herm X.Gm η η = 0 := by
  first | exact @GlobalTheory.UnipKill.exists_isotropic_partner | exact GlobalTheory.UnipKill.exists_isotropic_partner | (intros; apply GlobalTheory.UnipKill.exists_isotropic_partner <;> assumption)
