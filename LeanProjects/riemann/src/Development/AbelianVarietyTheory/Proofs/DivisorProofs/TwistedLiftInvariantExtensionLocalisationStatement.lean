import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLiftInvariantExtensionLocalisation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_lift_invariantExtension_localisation : ∀ (A B A₂ : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] [CommRing A₂] [IsLocalRing A₂] (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G] (f : B →+* A₂), IsLocalHom (f.comp (algebraMap A B)) → (∀ y : A₂, ∃ b s : B, IsUnit (f s) ∧ y * f s = f b) → (∀ b : B, f b = 0 → ∃ s : B, IsUnit (f s) ∧ s * b = 0) → ∀ (V' : Type) [CommRing V'] [IsLocalRing V'] (e₁ : A →+* V') (β : B →+* V'), IsLocalHom e₁ → β.comp (algebraMap A B) = e₁ → ∃ ev₂ : A₂ →+* V', IsLocalHom ev₂ ∧ ev₂.comp (f.comp (algebraMap A B)) = e₁ := by
  first | exact @GlobalTheory.twisted_lift_to_localisation | exact GlobalTheory.twisted_lift_to_localisation | (intros; apply GlobalTheory.twisted_lift_to_localisation <;> assumption)
