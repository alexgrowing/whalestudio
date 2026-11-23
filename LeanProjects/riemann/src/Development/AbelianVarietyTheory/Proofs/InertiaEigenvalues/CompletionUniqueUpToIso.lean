import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionUniversalLocalHomStatement
open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

theorem isCplAt_unique : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] (q : Ideal R) [q.IsPrime] (φ : R →+* S) (φ' : R →+* S'), IsCplAt q φ → IsCplAt q φ' → ∃ e : S ≃+* S', (e : S →+* S').comp φ = φ' := by
  intro R S S' _ _ _ _ _ q _ φ φ' h h'
  haveI := h.complete
  haveI := h'.complete
  obtain ⟨θ, ⟨hθl, hθ⟩, -⟩ := GlobalTheory.T.completion_universal_local_hom R S S' q φ φ' h h'.comap_eq
  obtain ⟨η, ⟨hηl, hη⟩, -⟩ := GlobalTheory.T.completion_universal_local_hom R S' S q φ' φ h' h.comap_eq
  have u := (GlobalTheory.T.completion_universal_local_hom R S S q φ φ h h.comap_eq).unique
    (y₁ := η.comp θ) (y₂ := RingHom.id S)
    ⟨RingHom.isLocalHom_comp η θ, by rw [RingHom.comp_assoc, hθ, hη]⟩
    ⟨inferInstance, RingHom.id_comp φ⟩
  have u' := (GlobalTheory.T.completion_universal_local_hom R S' S' q φ' φ' h' h'.comap_eq).unique
    (y₁ := θ.comp η) (y₂ := RingHom.id S')
    ⟨RingHom.isLocalHom_comp θ η, by rw [RingHom.comp_assoc, hη, hθ]⟩
    ⟨inferInstance, RingHom.id_comp φ'⟩
  exact ⟨RingEquiv.ofRingHom θ η u' u, hθ⟩

end GlobalTheory.Pat
