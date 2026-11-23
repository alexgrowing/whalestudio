import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair.Place

variable {k K : Type} [Field k] [Field K] {c : k →+* K}

theorem ord_eq_zero_iff (E : Place c) {f : K} (hf : f ≠ 0) :
    E.ord f = 0 ↔ f ∈ E.ring ∧ f⁻¹ ∈ E.ring := by
  rw [← E.ord_nonneg_iff hf, ← E.ord_nonneg_iff (inv_ne_zero hf), E.ord_inv]
  omega

end GlobalTheory.FieldPair.Place
