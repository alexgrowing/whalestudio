import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationRingCentreInChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DomBy
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_ring_centre_in_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω Ω' : Type) [Field Ω] [Field Ω'] (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (i : Ω →+* Ω') (W : ValuationSubring Ω') (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k j, i (y ⟨k, j⟩ / y ⟨k, c k⟩) ∈ W) → ∃ q : Cpt ξ, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c q ∧ DomBy W.toSubring i ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrVert.exists_domBy_chart | exact GlobalTheory.CompanionTheory.Ar.OrVert.exists_domBy_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.OrVert.exists_domBy_chart <;> assumption)
