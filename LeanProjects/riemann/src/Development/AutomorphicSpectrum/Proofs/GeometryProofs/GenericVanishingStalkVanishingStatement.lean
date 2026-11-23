import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericVanishingStalkVanishing
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_vanishing_stalk_vanishing : ∀ (X : Scheme.{0}) [IsReduced X] (Ω O : Type) [Field Ω] [CommRing O] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, ξ (IsLocalRing.closedPoint Ω) ⤳ q) → ∀ (s₀ : X ⟶ Spec (CommRingCat.of O)) (gm : O →+* Ω), ξ ≫ s₀ = Spec.map (CommRingCat.ofHom gm) → ∀ (x : X) (a : O), gm a = 0 → (Spec.preimage (X.fromSpecStalk x ≫ s₀)).hom a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.germ_vanish_of_generic_dominated | exact GlobalTheory.CompanionTheory.Ggeo.germ_vanish_of_generic_dominated | (intros; apply GlobalTheory.CompanionTheory.Ggeo.germ_vanish_of_generic_dominated <;> assumption)
