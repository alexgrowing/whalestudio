import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitStalkTransitionPulledBackFlagFrames
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_stalk_transition_pulledBack_flagFrames : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ z : W.Z, ∀ A₁ ∈ E'.S (W.p₁ z), ∀ A₂ ∈ E'.S (W.p₂ z), Par 0 (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) := by
  first | exact @GlobalTheory.FlagPush.Dbl.transition_par_stalk | exact GlobalTheory.FlagPush.Dbl.transition_par_stalk | (intros; apply GlobalTheory.FlagPush.Dbl.transition_par_stalk <;> assumption)
