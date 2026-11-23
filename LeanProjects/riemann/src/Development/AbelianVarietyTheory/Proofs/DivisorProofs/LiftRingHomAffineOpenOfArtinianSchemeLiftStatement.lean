import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRingHomAffineOpenOfArtinianSchemeLift
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_ringHom_affine_open_of_artinian_scheme_lift : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → ∀ (U : (Sp B).Opens), IsAffineOpen U → ∀ (V : X.Opens), IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : Γ(Sp B, U) →+* C) (φ₀ : Γ(X, V) →+* C₀), φ₀.comp ((s.appLE U V e).hom) = π.comp β → ∃ φ : Γ(X, V) →+* C, π.comp φ = φ₀ ∧ φ.comp ((s.appLE U V e).hom) = β) := by
  first | exact @GlobalTheory.lift_ringHom_of_scheme_lift | exact GlobalTheory.lift_ringHom_of_scheme_lift | (intros; apply GlobalTheory.lift_ringHom_of_scheme_lift <;> assumption)
