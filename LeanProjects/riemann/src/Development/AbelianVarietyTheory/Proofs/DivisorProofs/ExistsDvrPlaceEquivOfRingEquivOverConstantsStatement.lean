import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPlaceEquivOfRingEquivOverConstants
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvrPlace_equiv_of_ringEquiv_over_constants : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∃ Φ : Place c ≃ Place c', ∀ E : Place c, (∀ a, e a ∈ (Φ E).ring ↔ a ∈ E.ring) ∧ (∀ a, (Φ E).ord (e a) = E.ord a) ∧ (∀ φ : K →₀ ℚ, (Φ E).ordQ (Finsupp.mapDomain e φ) = E.ordQ φ) ∧ ∀ (n : ℕ) (x : Fin n → K), TrBasis c x → (Φ E).formOrd (dForm c' (e ∘ x)) = E.formOrd (dForm c x) := by
  first | exact @GlobalTheory.FieldPair.placeEquiv_ringEquiv | exact GlobalTheory.FieldPair.placeEquiv_ringEquiv | (intros; apply GlobalTheory.FieldPair.placeEquiv_ringEquiv <;> assumption)
