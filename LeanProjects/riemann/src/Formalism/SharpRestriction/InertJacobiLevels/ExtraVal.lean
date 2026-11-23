import Formalism.SharpRestriction.InertJacobiLevels.ExtraNch

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField IsDedekindDomain IsLocalRing

theorem val_le_one_iff {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (w : HeightOneSpectrum R) {B FB : Type*} [CommRing B] [IsLocalRing B] [Field FB] [Algebra B FB]
    (hinj : Function.Injective (algebraMap B FB)) (f : K →+* FB)
    (h1 : ∀ x : R, x ∈ w.asIdeal → ∃ y ∈ maximalIdeal B, algebraMap B FB y = f (algebraMap R K x))
    (h3 : ∀ x : R, x ∉ w.asIdeal → ∃ y : Bˣ, algebraMap B FB y = f (algebraMap R K x)) (x : K) :
    w.valuation K x ≤ 1 ↔ f x ∈ (algebraMap B FB).range := by
  have key : ∀ y : K, w.valuation K y ≤ 1 →
      ∃ a s : R, s ∉ w.asIdeal ∧ y * algebraMap R K s = algebraMap R K a := by
    intro y hy
    have hmem : y ∈ Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors := by
      have h1 : y ∈ (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w).toSubring := by
        show y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w
        rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
        exact (Valuation.mem_valuationSubring_iff _ _).2 hy
      rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_toSubring] at h1
      exact h1
    haveI := Localization.subalgebra.isLocalization_ofField K w.asIdeal.primeCompl
      w.asIdeal.primeCompl_le_nonZeroDivisors
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl
      (⟨y, hmem⟩ : Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors)
    refine ⟨a, s, s.2, ?_⟩
    have h2 := congrArg (fun z : Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors => (z : K))
      (IsLocalization.mk'_spec (Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors) a s)
    have hs' : IsLocalization.mk' (Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors) a s = ⟨y, hmem⟩ := hs
    rw [hs'] at h2
    simpa using h2
  have hone : ∀ s : R, s ∉ w.asIdeal → w.intValuation s = 1 := fun s hs =>
    le_antisymm (w.intValuation_le_one s)
      (not_lt.1 fun h => hs ((IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem w s).1 h))
  constructor
  · intro hx
    obtain ⟨a, s, hs, has⟩ := key x hx
    obtain ⟨u, hu⟩ := h3 s hs
    have hfa : f (algebraMap R K a) ∈ (algebraMap B FB).range := by
      by_cases ha : a ∈ w.asIdeal
      · obtain ⟨y, _, hy⟩ := h1 a ha
        exact ⟨y, hy⟩
      · obtain ⟨y, hy⟩ := h3 a ha
        exact ⟨y, hy⟩
    obtain ⟨b, hb⟩ := hfa
    refine ⟨b * ↑u⁻¹, ?_⟩
    have hfx : f x * f (algebraMap R K s) = f (algebraMap R K a) := by rw [← map_mul, has]
    rw [map_mul, hb, ← hfx, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  · rintro ⟨b, hb⟩
    by_contra hx
    push_neg at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hinv : w.valuation K x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hx
    obtain ⟨a, s, hs, has⟩ := key x⁻¹ hinv.le
    have hva : w.intValuation a < 1 := by
      have es : w.valuation K (algebraMap R K s) = 1 := by
        have e0 : w.valuation K (algebraMap R K s) = w.intValuation s :=
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap w s
        rw [e0, hone s hs]
      have ev : w.valuation K (algebraMap R K a) = w.valuation K x⁻¹ := by
        rw [← has, map_mul, es, mul_one]
      have ea : w.valuation K (algebraMap R K a) = w.intValuation a :=
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap w a
      rw [← ea, ev]
      exact hinv
    have ha : a ∈ w.asIdeal := (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem w a).1 hva
    obtain ⟨y, hy, hya⟩ := h1 a ha
    obtain ⟨u, hu⟩ := h3 s hs
    have e1 : f x⁻¹ * algebraMap B FB u = algebraMap B FB y := by
      rw [hu, hya, ← map_mul, has]
    have e2 : algebraMap B FB (b * y) = algebraMap B FB u := by
      rw [map_mul, ← e1, hb, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0, map_one, one_mul]
    have e3 := hinj e2
    have hmax : (u : B) ∈ maximalIdeal B := e3 ▸ Ideal.mul_mem_left _ b hy
    exact ((IsLocalRing.mem_maximalIdeal _).1 hmax) u.isUnit

theorem map_mem_maximalIdeal {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B]
    [IsLocalRing B] (g : A →+* B) (l : ℕ) (hl0 : (l : A) ≠ 0) (hl : (l : B) ∈ maximalIdeal B) (y : A)
    (hy : y ∈ maximalIdeal A) : g y ∈ maximalIdeal B := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hne : Ideal.span {(l : A)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hyn : y ^ n ∈ Ideal.span {(l : A)} := by
    rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
    exact Ideal.pow_mem_pow hy n
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hyn
  have hpow : g y ^ n ∈ maximalIdeal B := by
    rw [← map_pow, ← hc, map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ hl
  exact (maximalIdeal.isMaximal B).isPrime.mem_of_pow_mem n hpow

section Rec

variable (D : D7)

theorem val_nonneg_iff (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    0 ≤ D.what₂.places.val w x ↔ (D.plEq w).valuation D.what₂.LL x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [D.val_eq w x hx, Formalism.BasicNotions.vAdd]
    have hv0 : (D.plEq w).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (D.plEq w).valuation D.what₂.LL x = WithZero.exp n :=
      ⟨_, (WithZero.exp_log hv0).symm⟩
    rw [hn, WithZero.log_exp, ← WithZero.exp_zero, WithZero.exp_le_exp]
    rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
    omega

theorem resChar_mem (w : D.what₂.places.Pl) : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have h1 := D.what₂.places.val_resChar w
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  rw [D.val_eq w _ hne, Formalism.BasicNotions.vAdd] at h1
  have h2 := WithTop.coe_injective h1
  have hv0 : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hne
  obtain ⟨n, hn⟩ : ∃ n : ℤ,
      (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = WithZero.exp n :=
    ⟨_, (WithZero.exp_log hv0).symm⟩
  rw [hn, WithZero.log_exp] at h2
  have hpos := D.what₂.places.ramIdx_pos w
  have hlt : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) < 1 := by
    rw [hn, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
  have e : (D.plEq w).valuation D.what₂.LL
      (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) =
      (D.plEq w).intValuation ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) :=
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _
  rw [← e, map_natCast]
  exact hlt

end Rec

end Formalism.MainNotions.Inhab

end
