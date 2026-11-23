import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeDiagonalOfNotUnitTransitionEntry
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_diagonal_of_not_unit_transitionEntry : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)) (z : W.Z), ∀ A₁ ∈ E'.S (W.p₁ z), ∀ A₂ ∈ E'.S (W.p₂ z), AlmostLow τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) → ¬ UnitAt z ((A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b) → z ∈ Set.range W.δ := by
  first | exact @GlobalTheory.FlagPush.mem_range_section_of_not_unitAt | exact GlobalTheory.FlagPush.mem_range_section_of_not_unitAt | (intros; apply GlobalTheory.FlagPush.mem_range_section_of_not_unitAt <;> assumption)
