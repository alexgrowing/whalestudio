import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem wittVector_dvd_of_coeff_zero_eq_zero (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (a : WittVector p k) (ha : a.coeff 0 = 0) :
    (p : WittVector p k) ∣ a := by
  by_cases h0 : a = 0
  · exact h0 ▸ dvd_zero _
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul a h0
  cases m with
  | zero =>
    exfalso
    simp only [pow_zero, one_mul] at ha
    exact hb ha
  | succ n => exact ⟨(p : WittVector p k) ^ n * b, by ring⟩

theorem wittVector_natCast_ne_zero (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] : (p : WittVector p k) ≠ 0 := by
  intro h
  have := WittVector.coeff_p_pow p k 1
  rw [pow_one, h] at this
  simp at this

theorem exists_flat_lift_mod_p_sq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectField k], ∃ (Λ : Type) (_ : CommRing Λ) (π : Λ →+* k), Function.Surjective π ∧
      RingHom.ker π = Ideal.span {(p : Λ)} ∧ (p : Λ) ^ 2 = 0 ∧
      ∀ x : Λ, (p : Λ) * x = 0 → x ∈ Ideal.span {(p : Λ)} := by
  intro p _ k _ _ _
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  set I : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k) ^ 2} with hI
  have hlift : ∀ a ∈ I, WittVector.constantCoeff a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    simp [map_mul, map_pow, map_natCast, CharP.cast_eq_zero]
  let π : (WittVector p k ⧸ I) →+* k := Ideal.Quotient.lift I WittVector.constantCoeff hlift
  have hπ : ∀ a, π (Ideal.Quotient.mk I a) = a.coeff 0 := by
    intro a
    simp [π, Ideal.Quotient.lift_mk, WittVector.constantCoeff_apply]
  have hp0 : π (p : WittVector p k ⧸ I) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero k p
  refine ⟨WittVector p k ⧸ I, inferInstance, π, ?_, ?_, ?_, ?_⟩
  · intro r
    refine ⟨Ideal.Quotient.mk I (WittVector.teichmuller p r), ?_⟩
    rw [hπ, WittVector.teichmuller_coeff_zero]
  · ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, hπ, Ideal.mem_span_singleton]
    constructor
    · intro ha
      obtain ⟨c, rfl⟩ := wittVector_dvd_of_coeff_zero_eq_zero p k a ha
      exact ⟨Ideal.Quotient.mk I c, by rw [map_mul, map_natCast]⟩
    · rintro ⟨c, hc⟩
      rw [← hπ, hc, map_mul, hp0, zero_mul]
  · rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_natCast (Ideal.Quotient.mk I), ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    have hpne := wittVector_natCast_ne_zero p k
    have hac : a = (p : WittVector p k) * c := by
      apply mul_left_cancel₀ hpne
      rw [hc]; ring
    rw [Ideal.mem_span_singleton]
    exact ⟨Ideal.Quotient.mk I c, by rw [hac, map_mul, map_natCast]⟩

end GlobalTheory
