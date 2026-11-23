import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubringCoordsComplexValue
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subring_coords_complex_value : ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (W : Subring Ω') (φ : W →+* ℂ), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordsAt ξ y z w → (∀ a : W, φ a ≠ 0 → IsUnit a) → (∀ (k : K) (c e : J k), w ⟨k, c⟩ ≠ 0 → ∃ h : i (y ⟨k, e⟩ / y ⟨k, c⟩) ∈ W, φ ⟨_, h⟩ * w ⟨k, c⟩ = w ⟨k, e⟩) → ∀ (a : Ω) (r : ℂ), ValAt ξ z a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RegVal.contains_localRing | exact GlobalTheory.CompanionTheory.Ar.RegVal.contains_localRing | (intros; apply GlobalTheory.CompanionTheory.Ar.RegVal.contains_localRing <;> assumption)
