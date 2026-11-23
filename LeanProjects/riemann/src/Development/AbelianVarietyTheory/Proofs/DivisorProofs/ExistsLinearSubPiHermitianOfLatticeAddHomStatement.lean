import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSubPiHermitianOfLatticeAddHom
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_sub_pi_hermitian_of_lattice_addHom : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (H : Matrix (Fin g) (Fin g) ℂ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) → ∀ p : Λ →+ ℂ, ∃ (f : (Fin g → ℂ) →L[ℂ] ℂ) (v : Fin g → ℂ), ∀ l : Λ, p l = f l - Real.pi * (v ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) := by
  first | exact @GlobalTheory.exists_linear_sub_pi_mul_form_of_addMonoidHom | exact GlobalTheory.exists_linear_sub_pi_mul_form_of_addMonoidHom | (intros; apply GlobalTheory.exists_linear_sub_pi_mul_form_of_addMonoidHom <;> assumption)
