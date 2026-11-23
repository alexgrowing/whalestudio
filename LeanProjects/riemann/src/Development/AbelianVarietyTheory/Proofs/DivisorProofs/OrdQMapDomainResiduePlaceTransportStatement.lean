import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdQMapDomainResiduePlaceTransport
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordQ_mapDomain_residuePlace_transport : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (u : Q)
  (S E : Place cL) (ψ : S.ring →+* K) (F : Place cK),
  S.Contains Q → S.ord (u : L) = 0 → (u : L) ≠ 0 → Function.Surjective ψ →
  (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) →
  (∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1) →
  (∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
    ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G) →
  ∀ φ : S.ring →₀ ℚ, (∀ g ∈ φ.support, ψ g ≠ 0) →
  (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
    P.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) = 0) →
  F.ordQ (Finsupp.mapDomain ψ φ) = E.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) := by
  first | exact @GlobalTheory.FieldPair.ordQ_mapDomain_residue_eq | exact GlobalTheory.FieldPair.ordQ_mapDomain_residue_eq | (intros; apply GlobalTheory.FieldPair.ordQ_mapDomain_residue_eq <;> assumption)
