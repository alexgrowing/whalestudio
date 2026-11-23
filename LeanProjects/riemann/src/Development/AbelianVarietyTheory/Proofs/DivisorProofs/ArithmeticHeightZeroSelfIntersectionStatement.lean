import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightZeroSelfIntersection
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HermLB GlobalTheory.ArInt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_height_zero_self_intersection : GlobalTheory.Published.CycleHeights → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (k' : Type) [CommRing k'] [IsDomain k'] [Algebra k k'] (ρ : X ⟶ Sp k') (hρ : ρ ≫ spMap (algebraMap k k') = p)
    (M : HermLB (spMap (algebraMap k k'))), IsArithVar (spMap (algebraMap k k')) 0 →
    ∀ (h : X → ℝ) (x : X), (M.pull ρ hρ).IsArithHeight h → ArInt.IsAlgPt x → h x = 0 → M.IsSelfInter 0 := by
  first | exact @GlobalTheory.CurveDegZero.isSelfInter_zero | exact GlobalTheory.CurveDegZero.isSelfInter_zero | (intros; apply GlobalTheory.CurveDegZero.isSelfInter_zero <;> assumption)
