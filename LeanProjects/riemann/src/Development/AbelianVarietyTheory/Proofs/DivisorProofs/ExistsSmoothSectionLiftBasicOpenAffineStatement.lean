import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSectionLiftBasicOpenAffine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAt
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_section_lift_basicOpen_affine : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ V : X.left.Opens, IsAffineOpen V ∧ GlobalTheory.SecLift.LiftIn π X g₀ f V := by
  first | exact @GlobalTheory.SecLift.exists_liftIn | exact GlobalTheory.SecLift.exists_liftIn | (intros; apply GlobalTheory.SecLift.exists_liftIn <;> assumption)
