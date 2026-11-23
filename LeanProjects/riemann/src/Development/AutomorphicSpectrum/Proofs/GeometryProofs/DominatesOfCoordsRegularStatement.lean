import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegular
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominates_of_coords_regular : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω'), CoordTie o ξ x → IsCptGen ξ' → (∀ q : X', genPt ξ' ⤳ q) → (∀ (r : o) (p' : Cpt ξ'), i (algebraMap o Ω r) ∈ regAt ξ' p') → (∀ p' : Cpt ξ', ∃ c, InChart ξ' (fun k => i (x k)) c p') → ∃ f : X' ⟶ X, Dominates ξ' ξ f i ∧ ∀ (p' : Cpt ξ') (c : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => i (x k)) c p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordMap.exists_dominating_map | exact GlobalTheory.CompanionTheory.Ar.CoordMap.exists_dominating_map | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordMap.exists_dominating_map <;> assumption)
