import Mathlib

open NumberField

theorem UpperTheory.unramified_anti_invariant_local :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      Module.finrank F E = 2 →
      Algebra.Unramified (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers E) →
      ∀ (ξ : E), ξ ≠ 0 → σ ξ = -ξ →
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
        ∃ (a b : NumberField.RingOfIntegers E) (n : NumberField.RingOfIntegers F),
          n ∉ v.asIdeal ∧ σ (a : E) = -(a : E) ∧ (a : E) * (b : E) = algebraMap F E (n : F) := by
  intro F E _ _ _ _ _ σ hr hU ξ hξ hσ v
  have hne : σ ξ ≠ ξ := by
    intro h
    rw [hσ] at h
    exact hξ (by linear_combination (-1 / 2 : E) * h)
  have hfix : ∀ y : E, σ y = y → ∃ c : F, algebraMap F E c = y := by
    intro y hy
    have := Subalgebra.isSimpleOrder_of_finrank hr
    rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
    · have : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := hy
      rw [h] at this
      exact Algebra.mem_bot.mp this
    · have : ξ ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
      exact absurd this hne
  have hinv : ∀ y : E, σ (σ y) = y := by
    intro y
    have := Subalgebra.isSimpleOrder_of_finrank hr
    rcases eq_bot_or_eq_top (AlgHom.equalizer (σ.comp σ) (AlgHom.id F E)) with h | h
    · have : ξ ∈ AlgHom.equalizer (σ.comp σ) (AlgHom.id F E) := by
        show σ (σ ξ) = ξ
        rw [hσ, map_neg, hσ, neg_neg]
      rw [h] at this
      obtain ⟨c, hc⟩ := Algebra.mem_bot.mp this
      exact absurd (by rw [← hc, AlgHom.commutes]) hne
    · have : y ∈ AlgHom.equalizer (σ.comp σ) (AlgHom.id F E) := by rw [h]; trivial
      exact this
  let τ : 𝓞 E →ₐ[𝓞 F] 𝓞 E := RingOfIntegers.mapAlgHom σ
  have hτ : ∀ x : 𝓞 E, ((τ x : 𝓞 E) : E) = σ x := fun _ => rfl
  have := v.isMaximal
  obtain ⟨w, hw, hwv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hx : ∃ x : 𝓞 E, x - τ x ∉ w := by
    by_contra hcon
    push Not at hcon
    have heq : AlgHom.id (𝓞 F) (𝓞 E) = τ :=
      Algebra.FormallyUnramified.ext_of_iInf w (Ideal.iInf_pow_eq_bot_of_isDomain w hw.ne_top)
        (fun x => Ideal.Quotient.eq.mpr (hcon x))
    have hall : ∀ x : 𝓞 E, σ x = x := fun x => by rw [← hτ, ← heq]; rfl
    obtain ⟨p, q, -, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 E) ξ
    apply hne
    rw [← hpq, map_div₀]
    exact congrArg₂ (· / ·) (hall p) (hall q)
  obtain ⟨x, hx⟩ := hx
  set a : 𝓞 E := x - τ x with ha
  have hσa : σ (a : E) = -(a : E) := by
    have : (a : E) = x - σ x := by rw [← hτ]; rfl
    rw [this, map_sub, hinv, neg_sub]
  obtain ⟨c, hc⟩ := hfix ((a : E) * a) (by rw [map_mul, hσa, neg_mul_neg])
  have hci : IsIntegral ℤ c := by
    rw [← isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective, hc]
    exact a.isIntegral_coe.mul a.isIntegral_coe
  refine ⟨a, a, ⟨c, hci⟩, ?_, hσa, hc.symm⟩
  intro hn
  have h1 := (Ideal.mem_of_liesOver w v.asIdeal _).mp hn
  have h2 : algebraMap (𝓞 F) (𝓞 E) ⟨c, hci⟩ = a * a := by
    apply RingOfIntegers.ext
    exact hc
  rw [h2] at h1
  exact hx ((hw.isPrime.mem_or_mem h1).elim id id)
