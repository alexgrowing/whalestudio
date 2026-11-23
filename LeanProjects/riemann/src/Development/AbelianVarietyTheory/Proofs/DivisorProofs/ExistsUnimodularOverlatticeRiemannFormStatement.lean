import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularOverlatticeRiemannForm
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unimodular_overlattice_riemannForm : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (hermForm Hm l l').im = n) →
    ∃ (Λ₁ : Submodule ℤ (Fin g → ℂ)) (Ef : LinearMap.BilinForm ℤ Λ₁) (N : ℕ), Λ ≤ Λ₁ ∧ DiscreteTopology Λ₁ ∧
      Submodule.span ℝ (Λ₁ : Set (Fin g → ℂ)) = ⊤ ∧ (∀ a b : Λ₁, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧
      Function.Bijective Ef ∧ 0 < N ∧ ∀ x ∈ Λ₁, N • x ∈ Λ := by
  first | exact @GlobalTheory.Overlattice.exists_unimodular_overlattice | exact GlobalTheory.Overlattice.exists_unimodular_overlattice | (intros; apply GlobalTheory.Overlattice.exists_unimodular_overlattice <;> assumption)
