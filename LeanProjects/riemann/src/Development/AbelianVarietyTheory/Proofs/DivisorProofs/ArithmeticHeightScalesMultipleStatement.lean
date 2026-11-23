import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightScalesMultiple
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HermLB GlobalTheory.ArInt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_height_scales_multiple : GlobalTheory.Published.CycleHeights → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (m : ℕ) (h h' : X → ℝ),
    (comb L n).IsArithHeight h → (comb L (fun i => (m : ℤ) * n i)).IsArithHeight h' →
    ∀ x : X, ArInt.IsAlgPt x → h' x = m * h x := by
  first | exact @GlobalTheory.PtHtComb.height_comb_mul | exact GlobalTheory.PtHtComb.height_comb_mul | (intros; apply GlobalTheory.PtHtComb.height_comb_mul <;> assumption)
