import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kltAlongPlaceNeighbours_ringEquiv : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∀ (n : ℕ) (x : Fin n → K) (T : Subring K) (φ : K →₀ ℚ) (S : Place c) (S' : Place c'), TrBasis c x → (∀ a, e a ∈ S'.ring ↔ a ∈ S.ring) → AdjKlt c n T S (dForm c x) φ → AdjKlt c' n (T.map e.toRingHom) S' (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ) := by
  first | exact @GlobalTheory.FieldPair.adjKlt_ringEquiv | exact GlobalTheory.FieldPair.adjKlt_ringEquiv | (intros; apply GlobalTheory.FieldPair.adjKlt_ringEquiv <;> assumption)
