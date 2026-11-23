import Mathlib
open NumberField

namespace GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes

theorem exists_multiple_not_mem :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDedekindDomain R] (M : Type) [AddCommGroup M] [Module R M], (∀ (a : R) (m : M), a ≠ 0 → a • m = 0 → m = 0) → ∀ t : M, t ≠ 0 → ∀ d₀ : R, d₀ ≠ 0 → (∀ (x d : R) (u : M), d ≠ 0 → d • u = x • t → d ∣ d₀ * x) → ∀ (V : Set M) (P : Ideal R), P.IsMaximal → P ≠ ⊥ → (∀ u ∈ V, ∀ c e : R, e ≠ 0 → (∀ π ∈ P, e ∣ c * π) → ∃ u' : M, e • u' = c • u) → ∃ (x : R) (u : M), d₀ • u = x • t ∧ u ∉ V := by
  intro R _ _ _ M _ _ htf t _ d₀ hd₀ hb V P hP hP0 hV
  by_contra hcon
  push_neg at hcon
  let I : Ideal R :=
    { carrier := {x | ∃ u : M, d₀ • u = x • t}
      add_mem' := by
        rintro a b ⟨u, hu⟩ ⟨v, hv⟩
        exact ⟨u + v, by rw [smul_add, hu, hv, add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨u, hu⟩
        refine ⟨c • u, ?_⟩
        rw [smul_comm, hu, smul_eq_mul, mul_smul] }
  have hImem : ∀ x, x ∈ I ↔ ∃ u : M, d₀ • u = x • t := fun x => Iff.rfl
  have hI0 : I ≠ ⊥ := by
    intro h
    have : d₀ ∈ I := (hImem _).2 ⟨t, rfl⟩
    rw [h] at this
    exact hd₀ (by simpa using this)
  obtain ⟨e, heP, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hle : Ideal.span {e} ≤ P := (Ideal.span_singleton_le_iff_mem P).2 heP
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.2 hle
  have hcz : ∀ c ∈ C, ∀ z ∈ I, c * z ∈ Ideal.span {e} * I := by
    intro c hc z hz
    obtain ⟨u, hu⟩ := (hImem z).1 hz
    have huV : u ∈ V := hcon z u hu
    have hdiv : ∀ π ∈ P, e ∣ c * π := by
      intro π hπ
      have : π * c ∈ Ideal.span {e} := by
        rw [hC]
        exact Ideal.mul_mem_mul hπ hc
      rw [mul_comm]
      exact Ideal.mem_span_singleton.1 this
    obtain ⟨u', hu'⟩ := hV u huV c e he0 hdiv
    have h1 : (d₀ * e) • u' = (c * z) • t := by
      rw [mul_smul, hu', smul_comm, hu, mul_smul]
    have h2 : d₀ * e ∣ d₀ * (c * z) := hb (c * z) (d₀ * e) u' (mul_ne_zero hd₀ he0) h1
    obtain ⟨w, hw⟩ := (mul_dvd_mul_iff_left hd₀).1 h2
    have h3 : d₀ • u' = w • t := by
      have h4 : e • (d₀ • u' - w • t) = 0 := by
        rw [smul_sub, smul_comm, ← mul_smul e w, ← hw, ← h1, mul_smul, sub_self]
      exact sub_eq_zero.1 (htf e _ he0 h4)
    have hwI : w ∈ I := (hImem w).2 ⟨u', h3⟩
    rw [hw]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self e) hwI
  have hCI : C * I ≤ Ideal.span {e} * I := Ideal.mul_le.2 hcz
  have h5 : Ideal.span {e} * I ≤ Ideal.span {e} * (P * I) := by
    calc Ideal.span {e} * I = P * (C * I) := by rw [hC, mul_assoc]
      _ ≤ P * (Ideal.span {e} * I) := Ideal.mul_mono_right hCI
      _ = Ideal.span {e} * (P * I) := by ring
  have h6 : I ≤ P * I := (Ideal.span_singleton_mul_right_mono he0).1 h5
  have h8 : P * I = ⊤ * I := by
    rw [Ideal.top_mul]
    exact le_antisymm Ideal.mul_le_right h6
  exact hP.ne_top (mul_right_cancel₀ hI0 h8)

end GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes
