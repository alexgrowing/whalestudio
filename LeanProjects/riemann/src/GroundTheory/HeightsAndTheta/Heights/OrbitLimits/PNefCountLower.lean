import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountLower
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountAlongMultiples
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefSmallSectionEventually
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBoundedMul
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsCoordNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

section Shift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem smallSectionCount_le_shift {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m d : ℕ} {t : Ω}
    (ht : t ∈ chartLat y A.a d) (ht0 : t ≠ 0) (hts : IsSmallH (mCoordIdeal y) y A d t)
    (hfin : {s : chartLat y A.a (m + d) | IsSmallH (mCoordIdeal y) y A (m + d) (s : Ω)}.Finite) :
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) m ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (m + d) := by
  unfold smallSectionCount
  have : Finite {s : chartLat y A.a (m + d) // IsSmallH (mCoordIdeal y) y A (m + d) (s : Ω)} :=
    hfin.to_subtype
  have hmap : ∀ s : {s : chartLat y A.a m // IsSmallH (mCoordIdeal y) y A m (s : Ω)},
      (s.1 : Ω) * t ∈ chartLat y A.a (m + d) ∧ IsSmallH (mCoordIdeal y) y A (m + d) ((s.1 : Ω) * t) := by
    intro s
    refine ⟨chartLat_mul s.1.2 ht, fun dg dh g h z hg hh hdeg he hz => ?_⟩
    have := SectionBoundedMul.proof K ι Ω y A m d 1 1 _ t s.1.2 ht (isBoundedH_one_of_isSmallH s.2)
      (isBoundedH_one_of_isSmallH hts) dg dh g h z hg hh hdeg he hz
    simpa only [one_mul] using this
  have hcard : Nat.card {s : chartLat y A.a m // IsSmallH (mCoordIdeal y) y A m (s : Ω)} ≤
      Nat.card {s : chartLat y A.a (m + d) // IsSmallH (mCoordIdeal y) y A (m + d) (s : Ω)} :=
    Nat.card_le_card_of_injective (fun s => ⟨⟨(s.1 : Ω) * t, (hmap s).1⟩, (hmap s).2⟩) fun s s' h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext (mul_right_cancel₀ ht0 h))
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLat y A.a m // IsSmallH (mCoordIdeal y) y A m (s : Ω)})
    with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

end Shift

theorem eventually_mul_pow_le_shift (D L : ℕ) {b c : ℝ} (hc : 0 < c) (hbc : b < c) :
    ∀ᶠ n : ℕ in atTop, b * (n : ℝ) ^ (D + 1) ≤ c * ((n : ℝ) - L) ^ (D + 1) := by
  have h1 : Tendsto (fun n : ℕ => (1 - (L : ℝ) / n) ^ (D + 1)) atTop (𝓝 1) := by
    simpa using ((tendsto_const_div_atTop_nhds_zero_nat (L : ℝ)).const_sub 1).pow (D + 1)
  filter_upwards [h1.eventually (lt_mem_nhds ((div_lt_one hc).2 hbc)), eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have e : (n : ℝ) - L = n * (1 - L / n) := by field_simp
  have hp : 0 < (n : ℝ) ^ (D + 1) := by positivity
  rw [e, mul_pow]
  have := (div_lt_iff₀ hc).1 hn
  nlinarith

theorem NefCountLower.proof (hM : NefCountAlongMultiples.Statement) (hS : NefSmallSectionEventually.Statement)
    (hPk : PackingStatement) : NefCountLower.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen hht ε hε
  set T := II K ι (mCoordIdeal y) (D + 1) (fun _ => A)
  have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  by_cases hT : T - ε ≤ 0
  · exact Eventually.of_forall fun n =>
      (mul_nonpos_of_nonpos_of_nonneg hT (by positivity)).trans (Real.log_natCast_nonneg _)
  rw [not_le] at hT
  obtain ⟨a, ha, hak⟩ := hM K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht (ε / 2) (by linarith)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hak
  obtain ⟨n₀, hn₀⟩ :=
    eventually_atTop.1 (hS K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht (by linarith))
  have hfin := (hPk K ι Ω y D A (chartLat y A.a) har hb hs.1
    (fun τ _ hs' c hc' => isIntegral_algebraMap (x := (⟨_, hs' c hc'⟩ : chartRingZ y c)))).1
  filter_upwards [eventually_mul_pow_le_shift D (n₀ + a) (b := T - ε) (c := T - ε / 2) (by linarith)
    (by linarith), eventually_ge_atTop (n₀ + a + a * k₀)] with n hn hge
  obtain ⟨k, r, hr, hnk⟩ : ∃ k r, r < a ∧ n = a * k + (n₀ + r) :=
    ⟨(n - n₀) / a, (n - n₀) % a, Nat.mod_lt _ ha, by have := Nat.div_add_mod (n - n₀) a; omega⟩
  have hkk : k₀ ≤ k := by
    by_contra hlt
    have : a * k + a ≤ a * k₀ := by nlinarith
    omega
  obtain ⟨t, ht, ht0, hts⟩ := hn₀ (n₀ + r) (by omega)
  have hL : (n : ℝ) - ((n₀ + a : ℕ) : ℝ) ≤ ((a * k : ℕ) : ℝ) := by
    have : (n : ℝ) ≤ ((a * k : ℕ) : ℝ) + ((n₀ + a : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ a * k + (n₀ + a))
    linarith
  have hL0 : (0 : ℝ) ≤ (n : ℝ) - ((n₀ + a : ℕ) : ℝ) := by
    have : ((n₀ + a : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n₀ + a ≤ n)
    linarith
  have hpow := pow_le_pow_left₀ hL0 hL (D + 1)
  calc (T - ε) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
      = ((T - ε) * (n : ℝ) ^ (D + 1)) / ((D + 1).factorial : ℝ) := by ring
    _ ≤ ((T - ε / 2) * ((n : ℝ) - ((n₀ + a : ℕ) : ℝ)) ^ (D + 1)) / ((D + 1).factorial : ℝ) :=
        div_le_div_of_nonneg_right hn hfac.le
    _ ≤ ((T - ε / 2) * ((a * k : ℕ) : ℝ) ^ (D + 1)) / ((D + 1).factorial : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by linarith)) hfac.le
    _ = (T - ε / 2) * (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by ring
    _ ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (a * k) := hk₀ k hkk
    _ ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (a * k + (n₀ + r)) :=
        smallSectionCount_le_shift ht ht0 hts (hfin _)
    _ = smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n := by rw [← hnk]

end

end GroundTheory.Heights₂.Heights.Targets
