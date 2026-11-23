import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CosetRepresentativeTraceFixedProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumMulCosetRepresentativeTraceEqStatement
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_integer_coset_trace_eq (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] (hv : ∀ (g : G) (x : L), v (g • x) = v x) (U : Subgroup G)
    [Fintype (G ⧸ U)] (hU : AlmostSep v U) (e : L) (he : ∀ g : G, g • e = e) (he1 : v e < 1) :
    ∃ y ∈ Fix L U, v y ≤ 1 ∧ cosetTrace U y = e := by
  obtain ⟨n, a, b, c, hs, hc⟩ := hU (v e) he1
  have hid := GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq L v G U n a b c hs 1 (one_mem _)
  simp only [mul_one] at hid

  obtain ⟨i, hi⟩ : ∃ i, v e < v (cosetTrace U (b i)) := by
    by_contra h
    push_neg at h
    have : v (∑ i, a i * cosetTrace U (b i)) ≤ v e := by
      apply v.map_sum_le
      intro i _
      rw [v.map_mul]
      calc v (a i) * v (cosetTrace U (b i)) ≤ 1 * v (cosetTrace U (b i)) :=
            mul_le_mul_of_nonneg_right (hs.a_le i) zero_le
        _ = v (cosetTrace U (b i)) := one_mul _
        _ ≤ v e := h i
    rw [hid] at this
    exact absurd hc (not_lt.mpr this)
  set t := cosetTrace U (b i) with ht
  have hfix := GlobalTheory.AlmostEt.cosetTrace_fixed_props L v G hv U (b i) (hs.b_mem i)
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, v.map_zero] at hi; exact absurd hi (not_lt.mpr zero_le)
  have hvt0 : v t ≠ 0 := by rwa [Ne, Valuation.zero_iff]
  have hq : ∀ g : G, g • (e / t) = e / t := by
    intro g
    rw [smul_div₀', he g, hfix.1 g]
  refine ⟨e / t * b i, ?_, ?_, ?_⟩
  · have hb := hs.b_mem i
    intro m
    rw [smul_mul', hb m]
    congr 1
    exact hq (m : G)
  · rw [v.map_mul, map_div₀]
    calc v e / v t * v (b i) ≤ 1 * 1 := by
          apply mul_le_mul' _ (hs.b_le i)
          rw [div_le_one₀ (pos_iff_ne_zero.mpr hvt0)]
          exact hi.le
      _ = 1 := one_mul 1
  · rw [hfix.2.2 (e / t) hq, div_mul_cancel₀ e ht0]

theorem exists_integer_coset_trace_eq' : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (U : Subgroup G) [Fintype (G ⧸ U)], AlmostSep v U → ∀ e : L, (∀ g : G, g • e = e) → v e < 1 → ∃ y ∈ Fix L U, v y ≤ 1 ∧ cosetTrace U y = e :=
  fun L _ v G _ _ hv U _ hU e he he1 => exists_integer_coset_trace_eq L v G hv U hU e he he1

end GlobalTheory.AlmostEt
