import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvrPlace_topForm_orders_api : ∀ {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ) (x : Fin n → K), TrBasis c x →
  IsFreeGen K (dForm c x) ∧
  ∀ E : Place c, (∃ ω : Forms E.const n, IsFreeGen E.ring ω) ∧
    (∀ η : Forms c n, η ≠ 0 → E.IsFormOrd η (E.formOrd η)) ∧
    (∀ (η : Forms c n) (f : K), η ≠ 0 → f ≠ 0 → E.formOrd (f • η) = E.ord f + E.formOrd η) ∧
    (∀ (η : Forms c n) (a : ℤ), η ≠ 0 → E.IsFormOrd η a → E.formOrd η = a) := by
  first | exact @GlobalTheory.FieldPair.formOrd_api | exact GlobalTheory.FieldPair.formOrd_api | (intros; apply GlobalTheory.FieldPair.formOrd_api <;> assumption)
