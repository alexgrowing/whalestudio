import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackCompSpreadToSubring
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_isGrpPullback_comp_of_subring_le : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → IsGrpPullback e.A d₀.A (spMap R₀.subtype) j → IsGrpPullback e.A u.A (spMap R₀.subtype ≫ h₀) (j ≫ ψ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (φ₁ : A₁.left ⟶ d₀.A.left), IsGrpPullback A₁ d₀.A (spMap (Subring.inclusion hle)) φ₁ → IsGrpPullback A₁ u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) := by
  first | exact @GlobalTheory.GrpMulSpread.isGrpPullback_comp_spread_to_subring | exact GlobalTheory.GrpMulSpread.isGrpPullback_comp_spread_to_subring | (intros; apply GlobalTheory.GrpMulSpread.isGrpPullback_comp_spread_to_subring; all_goals assumption)
