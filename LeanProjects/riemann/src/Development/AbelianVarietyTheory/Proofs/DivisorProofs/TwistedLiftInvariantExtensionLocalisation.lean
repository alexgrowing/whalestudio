import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

open IsLocalRing

namespace GlobalTheory

theorem twisted_lift_to_localisation (A B A₂ : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [CommRing A₂] [IsLocalRing A₂] (G : Type) [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G] (f : B →+* A₂) :
    IsLocalHom (f.comp (algebraMap A B)) → (∀ y : A₂, ∃ b s : B, IsUnit (f s) ∧ y * f s = f b) →
    (∀ b : B, f b = 0 → ∃ s : B, IsUnit (f s) ∧ s * b = 0) →
    ∀ (V' : Type) [CommRing V'] [IsLocalRing V'] (e₁ : A →+* V') (β : B →+* V'),
      IsLocalHom e₁ → β.comp (algebraMap A B) = e₁ →
      ∃ ev₂ : A₂ →+* V', IsLocalHom ev₂ ∧ ev₂.comp (f.comp (algebraMap A B)) = e₁ := by
  intro hfl hsurj hker V' _ _ e₁ β he₁ hβ
  set q : Ideal B := (maximalIdeal A₂).comap f with hq
  set c : Ideal B := (maximalIdeal V').comap β with hc
  haveI : q.IsPrime := Ideal.comap_isPrime f (maximalIdeal A₂)
  haveI : c.IsPrime := Ideal.comap_isPrime β (maximalIdeal V')
  have hqA : Ideal.under A q = maximalIdeal A := by
    ext a
    simp only [Ideal.under, Ideal.mem_comap, hq, mem_maximalIdeal, mem_nonunits_iff]
    rw [← RingHom.comp_apply, isUnit_map_iff (f.comp (algebraMap A B))]
  have hcA : Ideal.under A c = maximalIdeal A := by
    ext a
    simp only [Ideal.under, Ideal.mem_comap, hc, mem_maximalIdeal, mem_nonunits_iff]
    rw [← RingHom.comp_apply, hβ, isUnit_map_iff e₁]
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G c q (hcA.trans hqA.symm)
  set β' : B →+* V' := β.comp (MulSemiringAction.toRingHom G B σ⁻¹) with hβ'
  have hβ'q : ∀ b : B, b ∈ q ↔ ¬ IsUnit (β' b) := by
    intro b
    rw [hσ, Ideal.mem_pointwise_smul_iff_inv_smul_mem, hc, Ideal.mem_comap, mem_maximalIdeal,
      mem_nonunits_iff]
    rfl
  have hfq : ∀ b : B, b ∈ q ↔ ¬ IsUnit (f b) := by
    intro b
    rw [hq, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  have hβ'A : β'.comp (algebraMap A B) = e₁ := by
    rw [← hβ]
    ext a
    simp only [hβ', RingHom.comp_apply, MulSemiringAction.toRingHom_apply, smul_algebraMap]
  letI : Algebra B A₂ := f.toAlgebra
  haveI hloc : IsLocalization q.primeCompl A₂ := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, hs⟩
      have : s ∉ q := hs
      rw [hfq, not_not] at this
      exact this
    · intro z
      obtain ⟨b, s, hs, h⟩ := hsurj z
      have hs' : s ∈ q.primeCompl := by
        show s ∉ q
        rw [hfq, not_not]; exact hs
      exact ⟨(b, ⟨s, hs'⟩), h⟩
    · intro x y hxy
      have h0 : f (x - y) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr hxy
      obtain ⟨s, hs, h⟩ := hker _ h0
      have hs' : s ∈ q.primeCompl := by
        show s ∉ q
        rw [hfq, not_not]; exact hs
      refine ⟨⟨s, hs'⟩, ?_⟩
      show s * x = s * y
      rw [mul_sub] at h
      exact sub_eq_zero.mp h
  have hunits : ∀ y : q.primeCompl, IsUnit (β' y) := by
    rintro ⟨s, hs⟩
    have : s ∉ q := hs
    rw [hβ'q, not_not] at this
    exact this
  have hcomp : (IsLocalization.lift hunits).comp f = β' :=
    IsLocalization.lift_comp (M := q.primeCompl) (S := A₂) hunits
  refine ⟨IsLocalization.lift hunits, ?_, ?_⟩
  · refine ⟨fun x hx => ?_⟩
    obtain ⟨b, s, hs, h⟩ := hsurj x
    have hsq : IsUnit (β' s) := by
      have : s ∉ q := by rw [hfq, not_not]; exact hs
      rw [hβ'q, not_not] at this
      exact this
    have hb : IsUnit (β' b) := by
      have h2 := congrArg (IsLocalization.lift hunits) h
      rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, hcomp] at h2
      rw [← h2]
      exact hx.mul hsq
    have hfb : IsUnit (f b) := by
      have : b ∉ q := by rw [hβ'q, not_not]; exact hb
      rw [hfq, not_not] at this
      exact this
    rw [← h] at hfb
    exact isUnit_of_mul_isUnit_left hfb
  · rw [← RingHom.comp_assoc, hcomp, hβ'A]

end GlobalTheory
