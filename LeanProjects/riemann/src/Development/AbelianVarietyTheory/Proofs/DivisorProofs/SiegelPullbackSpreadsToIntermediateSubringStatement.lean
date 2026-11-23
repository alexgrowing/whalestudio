import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackSpreadsToIntermediateSubring
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelPullback_spreads_to_intermediate_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE), SiegPB e d₀ (spMap R₀.subtype) → SiegPB e u (spMap R₀.subtype ≫ h₀) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁), SiegPB d₁ d₀ (spMap (Subring.inclusion hle)) → SiegPB d₁ u (spMap (Subring.inclusion hle) ≫ h₀) := by
  first | exact @GlobalTheory.SiegSpreadCore.siegPB_spread_subring | exact GlobalTheory.SiegSpreadCore.siegPB_spread_subring | (intros; apply GlobalTheory.SiegSpreadCore.siegPB_spread_subring <;> assumption)
