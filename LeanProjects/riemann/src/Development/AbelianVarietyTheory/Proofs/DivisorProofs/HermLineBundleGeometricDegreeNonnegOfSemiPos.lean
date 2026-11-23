import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

noncomputable section

namespace GlobalTheory.HSNef

open MeasureTheory

theorem gdeg_nonneg_of_semiPos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ L : HermLB p, L.SemiPos D → 0 ≤ gdeg L D := by
  intro k _ X _ p D _ L hL
  unfold gdeg chInt
  refine finsum_nonneg fun σ => ?_
  rw [Weight.chernInt, Weight.chernPart_neg_eq_zero (L.cInf σ) (hL σ)]
  simp only [Measure.restrict_zero, integral_zero_measure, sub_zero]
  exact integral_nonneg fun _ => zero_le_one

end GlobalTheory.HSNef
