import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrLocPrincipalPrime
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDVR_of_principal_prime_localization : ∀ {L : Type} [Field L] (A : Subring L) (t : A), IsNoetherianRing A → (t : L) ≠ 0 →
    (Ideal.span {t}).IsPrime → (∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (V : ValuationSubring L) (hA : ∀ a ∈ A, a ∈ V),
      IsDiscreteValuationRing V ∧ Irreducible (⟨t, hA _ t.2⟩ : V) ∧
      (∀ s : A, s ∉ Ideal.span {t} → IsUnit (⟨s, hA _ s.2⟩ : V)) ∧
      (∀ f : V, ∃ a s : A, s ∉ Ideal.span {t} ∧ (f : L) * s = a) ∧
      (A.subtype.codRestrict V fun a => hA _ a.2).EssFiniteType := by
  first | exact @GlobalTheory.dvr_loc_principal_prime | exact GlobalTheory.dvr_loc_principal_prime | (intros; apply GlobalTheory.dvr_loc_principal_prime <;> assumption)
