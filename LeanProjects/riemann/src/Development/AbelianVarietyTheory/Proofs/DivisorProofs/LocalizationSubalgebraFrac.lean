import Mathlib
open IsLocalRing

namespace GlobalTheory

theorem localization_subalgebra_frac :
  ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (C : Subalgebra R B), (∀ c ∈ C, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C, s ∉ Q ∧ s * c = 0) → ∃ V : Subalgebra R (Localization.AtPrime Q), (∀ x : Localization.AtPrime Q, x ∈ V ↔ ∃ a ∈ C, ∃ s ∈ C, s ∉ Q ∧ x * algebraMap B (Localization.AtPrime Q) s = algebraMap B (Localization.AtPrime Q) a) ∧ Nonempty (Localization.AtPrime (Q.comap (C.val : C →ₐ[R] B)) ≃ₐ[R] V) := by
  intro R B _ _ _ Q _ C hann
  set P : Ideal C := Q.comap (C.val : C →ₐ[R] B) with hP
  let φ0 : Localization.AtPrime P →+* Localization.AtPrime Q :=
    Localization.localRingHom P Q (C.val : C →+* B) rfl
  have hmk : ∀ (c : C) (s : P.primeCompl), φ0 (IsLocalization.mk' _ c s) =
      IsLocalization.mk' (Localization.AtPrime Q) (c : B) (⟨(s : C), s.2⟩ : Q.primeCompl) := by
    intro c s
    exact Localization.localRingHom_mk' P Q (C.val : C →+* B) rfl c s
  let φ : Localization.AtPrime P →ₐ[R] Localization.AtPrime Q :=
    { φ0 with
      commutes' := by
        intro r
        have h1 : algebraMap R (Localization.AtPrime P) r = algebraMap C (Localization.AtPrime P) (algebraMap R C r) :=
          IsScalarTower.algebraMap_apply R C _ r
        have h2 := Localization.localRingHom_to_map P Q (C.val : C →+* B) rfl (algebraMap R C r)
        show φ0 (algebraMap R (Localization.AtPrime P) r) = _
        rw [h1, h2, IsScalarTower.algebraMap_apply R B (Localization.AtPrime Q) r]
        rfl }
  have hφ : ∀ x, φ x = φ0 x := fun _ => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [hφ, hmk, IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨t, ht⟩, htc⟩ := hx
    obtain ⟨s', hs'C, hs'Q, hs'c⟩ := hann c c.2 t ht htc
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨⟨s', hs'C⟩, hs'Q⟩, ?_⟩
    apply Subtype.ext
    simpa using hs'c
  refine ⟨φ.range, ?_, ⟨(AlgEquiv.ofInjective φ hinj)⟩⟩
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    refine ⟨c, c.2, (s : C), (s : C).2, s.2, ?_⟩
    show φ0 (IsLocalization.mk' (Localization.AtPrime P) c s) * _ = _
    rw [hmk]
    exact IsLocalization.mk'_spec (Localization.AtPrime Q) (c : B) (⟨(s : C), s.2⟩ : Q.primeCompl)
  · rintro ⟨a, ha, s, hs, hsQ, hx⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime P) (⟨a, ha⟩ : C) (⟨⟨s, hs⟩, hsQ⟩ : P.primeCompl), ?_⟩
    show φ0 _ = x
    rw [hmk]
    symm
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    exact hx

end GlobalTheory
