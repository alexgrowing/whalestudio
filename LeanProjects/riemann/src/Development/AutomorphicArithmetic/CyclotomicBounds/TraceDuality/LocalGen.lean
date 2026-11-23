import Mathlib
open NumberField
open scoped TensorProduct NNReal

theorem UpperTheory.WildB.localGen :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ∃ (d : 𝓞 E) (m : ℕ), d ∈ differentIdeal ℤ (𝓞 E) ∧ d ≠ 0 ∧ ¬ p ∣ m ∧ ∀ a ∈ differentIdeal ℤ (𝓞 E), d ∣ (m : 𝓞 E) * a := by
  intro E _ _ p hp
  have hD : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  generalize differentIdeal ℤ (𝓞 E) = D at hD ⊢
  have hP : Ideal.span {(p : 𝓞 E)} ≠ ⊥ := by simpa using hp.ne_zero
  have hPtop : Ideal.span {(p : 𝓞 E)} ≠ ⊤ := by
    intro h
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at h1
    have h2 : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
    rcases Nat.pow_eq_one.mp h1 with h | h
    · exact hp.one_lt.ne' h
    · omega
  obtain ⟨d, hd⟩ := IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {(p : 𝓞 E)} * D) (J := D)
    Ideal.mul_le_right (mul_ne_zero hP hD)
  have hle : Ideal.span {d} ≤ D := hd ▸ le_sup_right
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hco : Ideal.span {(p : 𝓞 E)} ⊔ J = ⊤ := by
    apply mul_left_cancel₀ hD
    rw [Ideal.mul_sup, Ideal.mul_top, ← hJ, mul_comm]
    exact hd
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    exact hPtop (by simpa using hco)
  refine ⟨d, Ideal.absNorm J, hle (Ideal.mem_span_singleton_self d), ?_, ?_, ?_⟩
  · rintro rfl
    have : D * J = 0 := by rw [← hJ]; simp
    exact mul_ne_zero hD hJ0 this
  · intro h
    obtain ⟨P, hPm, hu, hdv⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp J h
    have hpP : (p : 𝓞 E) ∈ P := by
      have h1 : (p : ℤ) ∈ Ideal.under ℤ P := hu ▸ Ideal.mem_span_singleton_self _
      simpa [Ideal.under, Ideal.mem_comap] using h1
    apply hPm.ne_top
    rw [eq_top_iff, ← hco]
    exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hpP) (Ideal.dvd_iff_le.mp hdv)
  · intro a ha
    rw [← Ideal.mem_span_singleton, hJ, mul_comm (_ : 𝓞 E)]
    exact Ideal.mul_mem_mul ha (Ideal.absNorm_mem J)
