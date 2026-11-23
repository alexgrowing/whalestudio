import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockComplementLattice

open GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual

namespace GlobalTheory.CoeffEmbedding

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem exists_norm_le : ∃ C : ℝ, ∀ b : N.O i, ‖iotaOQ N A i b‖ ≤ C := by

  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[N.l i] (N.O i)).FG)
  refine ⟨∑ a ∈ s, ‖iotaOQ N A i a‖, fun b => ?_⟩
  have hb : b ∈ Submodule.span ℤ_[N.l i] (s : Set (N.O i)) := hs ▸ Submodule.mem_top
  obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hb
  rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  have hz : iotaOQ N A i (algebraMap ℤ_[N.l i] (N.O i) (c a)) =
      algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i]) := A.iotaQ_alg i (c a)
  rw [Algebra.smul_def, map_mul, norm_mul, hz]
  have h1 : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i])‖ ≤ 1 := by
    have he : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i])‖ = ‖(c a : ℚ_[N.l i])‖ :=
      PadicAlgCl.norm_extends (p := N.l i) _
    rw [he, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one _
  exact mul_le_of_le_one_left (norm_nonneg _) h1

include A in

theorem exists_pow_le_span : ∃ e : ℕ, IsLocalRing.maximalIdeal (N.O i) ^ e ≤
    Ideal.span {((N.l i : ℕ) : N.O i)} := by

  have hl : ((N.l i : ℕ) : N.O i) ≠ 0 := by
    intro h
    have h' := congrArg (iotaOQ N A i) h
    rw [map_natCast, map_zero] at h'
    exact (Nat.cast_ne_zero.2 (Fact.out : (N.l i).Prime).ne_zero) h'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (N.O i)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {((N.l i : ℕ) : N.O i)}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
  refine ⟨n, ?_⟩
  rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

theorem continuous_iotaOQ : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N) (i : N.Loc), Continuous (iotaOQ N A i) := by
  intro R H what₂ N A i

  obtain ⟨C, hC⟩ := exists_norm_le N A i
  obtain ⟨e, he⟩ := exists_pow_le_span N A i
  refine continuous_of_continuousAt_zero (iotaOQ N A i) ?_
  rw [ContinuousAt, map_zero, Metric.nhds_basis_ball.tendsto_right_iff]
  intro ε hε
  set q : ℝ := ‖((N.l i : ℕ) : Qbar (N.l i))‖ with hq
  have hq1 : q < 1 := by
    have he : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) ((N.l i : ℕ) : ℚ_[N.l i])‖ =
        ‖((N.l i : ℕ) : ℚ_[N.l i])‖ := PadicAlgCl.norm_extends (p := N.l i) _
    rw [map_natCast] at he
    rw [hq, he]
    exact Padic.norm_p_lt_one
  have hq0 : 0 ≤ q := norm_nonneg _
  have hC1 : 0 < |C| + 1 := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hC1) hq1
  obtain ⟨hopen, -⟩ := isAdic_iff.mp (N.O_adic i)
  filter_upwards [(hopen (e * k)).mem_nhds (Ideal.zero_mem _)] with x hx
  have hx' : x ∈ Ideal.span {((N.l i : ℕ) : N.O i) ^ k} := by
    rw [← Ideal.span_singleton_pow, pow_mul] at *
    exact Ideal.pow_right_mono he k hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
  rw [Metric.mem_ball, dist_zero_right, map_mul, map_pow, map_natCast, norm_mul, norm_pow, ← hq]
  calc ‖iotaOQ N A i b‖ * q ^ k ≤ (|C| + 1) * q ^ k :=
        mul_le_mul_of_nonneg_right ((hC b).trans (by linarith [le_abs_self C])) (pow_nonneg hq0 k)
    _ < (|C| + 1) * (ε / (|C| + 1)) := mul_lt_mul_of_pos_left hk hC1
    _ = ε := by field_simp

end GlobalTheory.CoeffEmbedding
