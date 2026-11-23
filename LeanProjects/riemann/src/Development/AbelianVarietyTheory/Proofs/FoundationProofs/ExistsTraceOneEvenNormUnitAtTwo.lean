import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem norm_eq_one_or_of_add_eq_one {L : Type*} [NormedField L] [IsUltrametricDist L] {b c : L}
    (h : b + c = 1) (hn : ‖b * c‖ < 1) : ‖b‖ = 1 ∨ ‖c‖ = 1 := by
  by_contra hne
  push_neg at hne
  obtain ⟨hb, hc⟩ := hne
  rw [norm_mul] at hn
  have h1 : ‖c‖ = max 1 ‖b‖ := by
    have : c = 1 + -b := by linear_combination h
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hb.symm)]
    simp
  have h2 : ‖b‖ = max 1 ‖c‖ := by
    have : b = 1 + -c := by linear_combination h
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hc.symm)]
    simp
  have h3 : 1 ≤ ‖c‖ := h1 ▸ le_max_left _ _
  have h4 : 1 ≤ ‖b‖ := h2 ▸ le_max_left _ _
  nlinarith

theorem norm_two_mul_natCast_lt_one (k : ℕ) : ‖((2 * k : ℕ) : ℂ_[2])‖ < 1 := by
  have h2 : ‖(2 : ℂ_[2])‖ < 1 := by
    have : (2 : ℂ_[2]) = algebraMap ℚ_[2] ℂ_[2] ((2 : ℕ) : ℚ_[2]) := by simp [map_ofNat]
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hk : ‖(k : ℂ_[2])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ k
  push_cast
  rw [norm_mul]
  nlinarith [norm_nonneg (k : ℂ_[2]), norm_nonneg (2 : ℂ_[2])]

theorem exists_int_trace_one_unit_at_two :
    ∀ (D : D7) (lam : Qbar →+* ℂ_[2]), ∃ (a : 𝓞 D.host.K) (β : ℂ) (k : ℕ), D.host.φ₀ (((a : D.host.K) : D.host.E)) = β ∧ β ∈ Qbar ∧ ‖lamC lam β‖ = 1 ∧ β + starRingEnd ℂ β = 1 ∧ β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) ∧ ∀ (Λ : AddSubgroup ℂ) (t₀ : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D Λ t₀ → β * t₀ ∉ Λ ∧ (1 - β) * t₀ ∉ Λ := by
  intro D lam
  have hm : ∀ x, D.host.φ₀ x ∈ Qbar := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 8 * k := ⟨(D.host.d + 1) / 8, by omega⟩
  have hk' : (D.host.d : ℂ) + 1 = 8 * (k : ℂ) := by exact_mod_cast hk
  have hs : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hw : StandardLatticesGL3.w0 D = (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 := rfl
  have hw' : 1 - StandardLatticesGL3.w0 D = (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 := by
    rw [hw]; ring
  have hc : starRingEnd ℂ (StandardLatticesGL3.w0 D) = 1 - StandardLatticesGL3.w0 D := by
    rw [hw', hw, map_div₀, map_add, map_mul, map_one, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hp : StandardLatticesGL3.w0 D * (1 - StandardLatticesGL3.w0 D) = ((2 * k : ℕ) : ℂ) := by
    rw [hw', hw]
    push_cast
    linear_combination (1 / 4 : ℂ) * hk' + (1 / 4 : ℂ) * hs
      - (1 / 4 : ℂ) * ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 * Complex.I_sq
  have hQ : StandardLatticesGL3.w0 D ∈ Qbar := ha ▸ hm _
  have hQ' : 1 - StandardLatticesGL3.w0 D ∈ Qbar := Qbar.sub_mem Qbar.one_mem hQ
  have hadd : lamC lam (StandardLatticesGL3.w0 D) + lamC lam (1 - StandardLatticesGL3.w0 D) = 1 := by
    simp only [lamC, dif_pos hQ, dif_pos hQ']
    rw [← map_add, ← map_one lam]
    congr 1
    apply Subtype.ext
    simp
  have hmul : lamC lam (StandardLatticesGL3.w0 D) * lamC lam (1 - StandardLatticesGL3.w0 D) = ((2 * k : ℕ) : ℂ_[2]) := by
    simp only [lamC, dif_pos hQ, dif_pos hQ']
    rw [← map_mul, ← map_natCast lam]
    congr 1
    apply Subtype.ext
    exact hp.trans (by simp; exact Or.inl rfl)
  rcases norm_eq_one_or_of_add_eq_one hadd (hmul ▸ norm_two_mul_natCast_lt_one k) with h | h
  · refine ⟨a, StandardLatticesGL3.w0 D, k, ha, hQ, h, by rw [hc]; ring, by rw [hc, hp], ?_⟩
    intro Λ t ht
    exact ⟨ht.2.1, hw' ▸ ht.2.2⟩
  · refine ⟨1 - a, 1 - StandardLatticesGL3.w0 D, k, ?_, hQ', h, ?_, ?_, ?_⟩
    · rw [← ha]
      simp
    · rw [map_sub, map_one, hc]; ring
    · rw [map_sub, map_one, hc, ← hp]; ring
    · intro Λ t ht
      rw [sub_sub_cancel]
      exact ⟨hw' ▸ ht.2.2, ht.2.1⟩

end GlobalTheory.EvenTheta
