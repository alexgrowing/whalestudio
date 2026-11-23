import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter

noncomputable section

theorem chartLat_le_chartLatNm {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) :
    chartLat y a τ ≤ chartLatNm y a τ := by
  intro s hs c hc
  have h := hs c hc
  rw [mem_integralClosure_iff]
  exact isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, h⟩)

theorem smallSectionCount_mono_lattice {Ω : Type*} [CommRing Ω] (P : ℕ → Ω → Prop) {La La' : ℕ → AddSubgroup Ω}
    (τ : ℕ) (hle : La τ ≤ La' τ) (hfin : {s : La' τ | P τ (s : Ω)}.Finite) :
    smallSectionCount P La τ ≤ smallSectionCount P La' τ := by
  unfold smallSectionCount
  have : Finite {s : La' τ // P τ (s : Ω)} := hfin.to_subtype
  have hc : Nat.card {s : La τ // P τ (s : Ω)} ≤ Nat.card {s : La' τ // P τ (s : Ω)} := by
    refine Nat.card_le_card_of_injective
      (fun s => (⟨⟨(s.1 : Ω), hle s.1.2⟩, s.2⟩ : {s : La' τ // P τ (s : Ω)})) ?_
    intro s t hst
    exact Subtype.ext (Subtype.ext (congrArg (fun u : {s : La' τ // P τ (s : Ω)} => ((u.1 : La' τ) : Ω)) hst))
  rcases Nat.eq_zero_or_pos (Nat.card {s : La τ // P τ (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hc)

theorem ArithmeticVolumeBigRefined.proof (hG6p : ArithmeticVolumeBig.Statement) (hPk : PackingStatement) :
    ArithmeticVolumeBigRefined.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hD hII har hb hP0 hs hnef hc
  refine (hG6p K ι Ω y D A P0 II hD hII har hb hP0 hs hnef hc).trans ?_
  obtain ⟨hfin, C, hC⟩ := hPk K ι Ω y D A (chartLatNm y A.a) har hb hs.1 (fun _ => le_rfl)
  unfold arVolP
  simp only [one_mul]
  have hden : ∀ k : ℕ, 0 ≤ ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := fun k => by positivity
  refine limsup_le_limsup (Eventually.of_forall fun k => div_le_div_of_nonneg_right
      (smallSectionCount_mono_lattice _ k (chartLat_le_chartLatNm y A.a k) (hfin k)) (hden k)) ?_ ?_
  · exact isCoboundedUnder_le_of_le atTop (fun k => div_nonneg (Real.log_natCast_nonneg _) (hden k))
  · refine isBoundedUnder_of_eventually_le (a := |C| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ))
      (eventually_atTop.2 ⟨1, fun k hk => ?_⟩)
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hF : (0 : ℝ) < (D + 1).factorial := by positivity
    have hkp : (0 : ℝ) < (k : ℝ) ^ (D + 1) := by positivity
    rw [div_le_iff₀ (by positivity)]
    have h2 : C * ((k : ℝ) + 1) ^ (D + 1) ≤ |C| * (2 * (k : ℝ)) ^ (D + 1) :=
      calc C * ((k : ℝ) + 1) ^ (D + 1) ≤ |C| * ((k : ℝ) + 1) ^ (D + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * (2 * (k : ℝ)) ^ (D + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (abs_nonneg C)
    calc smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) k
        ≤ |C| * (2 * (k : ℝ)) ^ (D + 1) := (hC k).trans h2
      _ = |C| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) * ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
          rw [mul_pow]; field_simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
