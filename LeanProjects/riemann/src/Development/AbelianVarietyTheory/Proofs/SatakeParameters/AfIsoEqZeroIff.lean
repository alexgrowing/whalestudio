import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne

open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AfeLocTr

open HeightOneSpectrum

def IsIntAd {E : Type} [Field E] [NumberField E] (z : FiniteAdeleRing (𝓞 E) E) : Prop :=
  ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (z Q) ≤ 1

theorem eq_zero_of_le_exp {x : WithZero (Multiplicative ℤ)} (h : ∀ n : ℕ, x ≤ WithZero.exp (-(n : ℤ))) : x = 0 := by
  by_contra hx
  have e := WithZero.exp_log hx
  set n : ℕ := (-WithZero.log x + 1).toNat
  have h1 := h n
  rw [← e, WithZero.exp_le_exp] at h1
  have h2 := Int.self_le_toNat (-WithZero.log x + 1)
  omega

theorem exists_gen {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    ∃ h : ℕ, 0 < h ∧ ∃ α : 𝓞 E, Ideal.span {α} = P.asIdeal ^ h := by
  have hP : P.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 E))
  have hPh : P.asIdeal ^ h ∈ nonZeroDivisors (Ideal (𝓞 E)) := pow_mem hP h
  have h1 : ClassGroup.mk0 ⟨P.asIdeal ^ h, hPh⟩ = 1 := by
    have e : (⟨P.asIdeal ^ h, hPh⟩ : nonZeroDivisors (Ideal (𝓞 E))) = ⟨P.asIdeal, hP⟩ ^ h := Subtype.ext (by simp)
    rw [e, map_pow, pow_card_eq_one]
  haveI := (ClassGroup.mk0_eq_one_iff hPh).1 h1
  exact ⟨h, Fintype.card_pos, _, Ideal.span_singleton_generator _⟩

theorem comp_eq_zero_iff {E : Type} [Field E] [NumberField E] (z : FiniteAdeleRing (𝓞 E) E) (hz : IsIntAd z)
    (P : HeightOneSpectrum (𝓞 E)) :
    z P = 0 ↔ ∀ n : ℕ, ∃ π : 𝓞 E, π ≠ 0 ∧ π ∈ P.asIdeal ^ n ∧
      IsIntAd (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E π)⁻¹ * z) := by
  constructor
  · intro h0 n
    obtain ⟨h, hh, α, hα⟩ := exists_gen P
    have hα0 : α ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at hα
      exact pow_ne_zero _ P.ne_bot hα.symm
    have hαP : α ∈ P.asIdeal := Ideal.pow_le_self hh.ne' (hα ▸ Ideal.mem_span_singleton_self α)
    refine ⟨α ^ n, pow_ne_zero _ hα0, Ideal.pow_mem_pow hαP n, fun Q => ?_⟩
    show Valued.v (((algebraMap (𝓞 E) E (α ^ n))⁻¹ : E) * z Q) ≤ 1
    by_cases hQ : Q = P
    · subst hQ
      rw [h0, mul_zero, map_zero]
      exact zero_le'
    · have hαQ : α ∉ Q.asIdeal := by
        intro hm
        have h2 : P.asIdeal ^ h ≤ Q.asIdeal := by rw [← hα, Ideal.span_singleton_le_iff_mem]; exact hm
        exact hQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top (Q.isPrime.le_of_pow_le h2)).symm)
      have hv : Q.valuation E (algebraMap (𝓞 E) E (α ^ n)) = 1 :=
        (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) Q).2 fun hm => hαQ (Q.isPrime.mem_of_pow_mem n hm)
      rw [map_mul, valuedAdicCompletion_eq_valuation', map_inv₀, hv, inv_one, one_mul]
      exact hz Q
  · intro h
    refine (Valued.v.zero_iff).1 (eq_zero_of_le_exp fun n => ?_)
    obtain ⟨π, hπ0, hπn, hint⟩ := h n
    have h1 : Valued.v (((algebraMap (𝓞 E) E π)⁻¹ : E) * z P) ≤ 1 := hint P
    rw [map_mul, valuedAdicCompletion_eq_valuation', map_inv₀, valuation_of_algebraMap] at h1
    have hv0 : P.intValuation π ≠ 0 := P.intValuation_ne_zero π hπ0
    have h2 : Valued.v (z P) ≤ P.intValuation π := by
      calc Valued.v (z P) = P.intValuation π * ((P.intValuation π)⁻¹ * Valued.v (z P)) := by
            rw [← mul_assoc, mul_inv_cancel₀ hv0, one_mul]
        _ ≤ P.intValuation π * 1 := by gcongr
        _ = P.intValuation π := mul_one _
    exact h2.trans ((P.intValuation_le_pow_iff_mem π n).2 hπn)

end GlobalTheory.AfeLocTr

namespace GlobalTheory.AfeLocTr

open HeightOneSpectrum

theorem transport_zero {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (s : E ≃+* E')
    (Φ : FiniteAdeleRing (𝓞 E) E ≃+* FiniteAdeleRing (𝓞 E') E')
    (hΦ : ∀ x : E, Φ (algebraMap E _ x) = algebraMap E' _ (s x)) (hI : ∀ z, IsIntAd (Φ z) ↔ IsIntAd z)
    (P : HeightOneSpectrum (𝓞 E)) (Q : HeightOneSpectrum (𝓞 E'))
    (hPQ : ∀ a ∈ P.asIdeal, RingOfIntegers.mapRingEquiv s a ∈ Q.asIdeal)
    (z : FiniteAdeleRing (𝓞 E) E) (hz : IsIntAd z) (h0 : z P = 0) : Φ z Q = 0 := by
  rw [comp_eq_zero_iff z hz] at h0
  rw [comp_eq_zero_iff (Φ z) ((hI z).2 hz)]
  intro n
  obtain ⟨π, hπ0, hπn, hint⟩ := h0 n
  set f := RingOfIntegers.mapRingEquiv s
  refine ⟨f π, (map_ne_zero_iff _ f.injective).2 hπ0, ?_, ?_⟩
  · have h1 : Ideal.map f P.asIdeal ≤ Q.asIdeal := Ideal.map_le_iff_le_comap.2 hPQ
    have h2 : f π ∈ Ideal.map f (P.asIdeal ^ n) := Ideal.mem_map_of_mem _ hπn
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 n h2
  · have e : algebraMap (𝓞 E') E' (f π) = s (algebraMap (𝓞 E) E π) := RingOfIntegers.mapRingEquiv_apply s π
    have e2 : algebraMap E' (FiniteAdeleRing (𝓞 E') E') (algebraMap (𝓞 E') E' (f π))⁻¹ * Φ z =
        Φ (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E π)⁻¹ * z) := by
      rw [map_mul, hΦ, map_inv₀ s, e]
    rw [e2]
    exact (hI _).2 hint

theorem afIso_eq_zero_iff : ∀ (F E F' E' : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (s : E ≃+* E') (φ : AfE F E ≃+* AfE F' E'), (∀ x : E, φ (x ⊗ₜ[F] 1) = s x ⊗ₜ[F'] 1) → (∀ y, φ y ∈ RInt F' E' ↔ y ∈ RInt F E) → ∀ y ∈ RInt F E, ∀ P : HeightOneSpectrum (𝓞 E), (GlobalTheory.Mem.Col2.afIso F' E' (φ y) (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s) P) = 0 ↔ GlobalTheory.Mem.Col2.afIso F E y P = 0) := by
  intro F E F' E' _ _ _ _ _ _ _ _ _ _ s φ hφ hR y hy P
  set ι := GlobalTheory.Mem.Col2.afIso F E
  set ι' := GlobalTheory.Mem.Col2.afIso F' E'
  set Φ : FiniteAdeleRing (𝓞 E) E ≃+* FiniteAdeleRing (𝓞 E') E' := ι.symm.trans (φ.trans ι')
  have hΦa : ∀ w, Φ w = ι' (φ (ι.symm w)) := fun _ => rfl
  have hΦ : ∀ x : E, Φ (algebraMap E _ x) = algebraMap E' _ (s x) := fun x => by
    rw [hΦa, ← GlobalTheory.Mem.Col2.afIso_tmul_one F E x, RingEquiv.symm_apply_apply, hφ, GlobalTheory.Mem.Col2.afIso_tmul_one]
  have hI : ∀ w, IsIntAd (Φ w) ↔ IsIntAd w := fun w => by
    unfold IsIntAd
    rw [hΦa, ← GlobalTheory.Mem.Col2.mem_rInt_iff, hR, GlobalTheory.Mem.Col2.mem_rInt_iff, RingEquiv.apply_symm_apply]
  have hΦy : Φ (ι y) = ι' (φ y) := by rw [hΦa, RingEquiv.symm_apply_apply]
  have hz : IsIntAd (ι y) := (GlobalTheory.Mem.Col2.mem_rInt_iff F E y).1 hy
  set Q := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s) P
  have hQ : ∀ b : 𝓞 E', b ∈ Q.asIdeal ↔ (RingOfIntegers.mapRingEquiv s).symm b ∈ P.asIdeal := fun b => Iff.rfl
  rw [← hΦy]
  constructor
  · intro h0
    have hΦ' : ∀ x : E', Φ.symm (algebraMap E' _ x) = algebraMap E _ (s.symm x) := fun x => by
      rw [RingEquiv.symm_apply_eq, hΦ, RingEquiv.apply_symm_apply]
    have hI' : ∀ w, IsIntAd (Φ.symm w) ↔ IsIntAd w := fun w => by
      rw [← hI, RingEquiv.apply_symm_apply]
    have hQP : ∀ a ∈ Q.asIdeal, RingOfIntegers.mapRingEquiv s.symm a ∈ P.asIdeal := fun a ha => by
      have e : RingOfIntegers.mapRingEquiv s.symm a = (RingOfIntegers.mapRingEquiv s).symm a := rfl
      rw [e]
      exact (hQ a).1 ha
    have := transport_zero s.symm Φ.symm hΦ' hI' Q P hQP (Φ (ι y)) ((hI _).2 hz) h0
    rwa [RingEquiv.symm_apply_apply] at this
  · intro h0
    refine transport_zero s Φ hΦ hI P Q (fun a ha => ?_) (ι y) hz h0
    rw [hQ, RingEquiv.symm_apply_apply]
    exact ha

end GlobalTheory.AfeLocTr
