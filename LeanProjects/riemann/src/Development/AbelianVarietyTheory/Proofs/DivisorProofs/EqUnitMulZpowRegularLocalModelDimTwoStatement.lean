import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqUnitMulZpowRegularLocalModelDimTwo
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_unit_mul_zpow_regularLocalModel_dimTwo : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∀ E : Place cL, E.IsPrimeOf Q → E.ord (u : L) = 1 →
  ∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
  ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G := by
  first | exact @GlobalTheory.FieldPair.AdjUnit.eq_unit_mul_zpow | exact GlobalTheory.FieldPair.AdjUnit.eq_unit_mul_zpow | (intros; apply GlobalTheory.FieldPair.AdjUnit.eq_unit_mul_zpow <;> assumption)
