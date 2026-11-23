import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def LocAwaySpec.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Φ : Type) [Field Φ] (φ : R →+* Φ) (S : Finset Φ),
    (∀ c : Φ, ∃ f g : R, φ g ≠ 0 ∧ c = φ f / φ g) →
    ∃ (E : R) (hE : IsUnit (φ E)),
      (∀ c ∈ S, c ∈ Set.range (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ)) ∧
      ∀ (B : Type) [CommRing B] (ψ : R →+* B) (hψ : IsUnit (ψ E)), RingHom.ker φ ≤ RingHom.ker ψ →
        RingHom.ker (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ≤
          RingHom.ker (IsLocalization.Away.lift E hψ : Localization.Away E →+* B)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
