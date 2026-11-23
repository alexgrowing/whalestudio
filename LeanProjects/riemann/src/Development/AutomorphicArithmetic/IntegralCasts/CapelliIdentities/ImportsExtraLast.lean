import Mathlib

namespace DedekindLocalUniformizer
end DedekindLocalUniformizer

theorem UpperTheory.Reformulated.B.Yde5.main :
    ∀ {R : Type} [inst : CommRing R] [IsDedekindDomain R] (P : Ideal R),
      P.IsMaximal → P ≠ ⊥ → ∃ (π : R), π ≠ (0 : R) ∧ π ∈ P ∧ ∃ s ∉ P, ∀ y ∈ P, ∃ (c : R), s * y = π * c := by
  intro R _ _ P hmax hbot
  haveI : P.IsPrime := hmax.isPrime
  have hlt : P ^ (1 + 1) < P ^ 1 := Ideal.pow_succ_lt_pow hbot 1
  rw [pow_one] at hlt
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  have hπ0 : π ≠ 0 := by
    rintro rfl; exact hπ2 (Ideal.zero_mem _)
  refine ⟨π, hπ0, hπP, ?_⟩
  have hle : Ideal.span {π} ≤ P := (Ideal.span_singleton_le_iff_mem P).2 hπP
  obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).2 hle
  have hJP : ¬ J ≤ P := by
    intro h
    apply hπ2
    have : Ideal.span {π} ≤ P ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self π)
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hJP
  refine ⟨s, hsP, fun y hy => ?_⟩
  have hmem : s * y ∈ Ideal.span {π} := by
    rw [hJ, mul_comm s y]; exact Ideal.mul_mem_mul hy hsJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨c, by rw [← hc, mul_comm]⟩
