import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountMonoLattice
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.StNmSmallIntoFS
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.StFSSmallFinite
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.StFSSmallCountBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter

noncomputable section

theorem G6ppB.proof (hBig : MoriwakiBigStatement) (hInj : NmSmallIntoFS.Statement)
    (hFin : FSSmallFinite.Statement) (hCnt : FSSmallCountBound.Statement) : BirationalPullbackPushforwardFormula := by
  intro K _ ι _ Ω _ y D A P0 II hD hII har hb hP0 hs hnef hc
  refine (ArithmeticVolumeBig.of_moriwakiBig_only hBig K ι Ω y D A P0 II hD hII har hb hP0 hs hnef hc).trans ?_
  obtain ⟨M, k, C₀, hM, hC₀, hf⟩ := hInj K ι Ω y D A har hb hs.1
  obtain ⟨R, hR⟩ := hCnt K ι Ω y D II hII har hb C₀ hC₀
  have hg : Tendsto (fun τ : ℕ => M * (τ + k)) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun τ hτ => le_trans hτ (by nlinarith)⟩

  have hev : ∀ᶠ τ : ℕ in atTop,
      {s : chartLatNm y A.a τ | IsSmallH (mCoordIdeal y) y A τ (s : Ω)}.Finite ∧
      smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ ≤
        R * ((M * (τ + k) : ℕ) : ℝ) ^ (D + 1) := by
    filter_upwards [hg.eventually hR] with τ hτ
    obtain ⟨f, hfi⟩ := hf C₀ le_rfl τ
    have : Finite {σ : chartLat y (fsScaled ι C₀).a (M * (τ + k)) //
        IsSmallH (mCoordIdeal y) y (fsScaled ι C₀) (M * (τ + k)) (σ : Ω)} :=
      (hFin K ι Ω y D har hb C₀ (M * (τ + k))).to_subtype
    have : Finite {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} :=
      Finite.of_injective f hfi
    refine ⟨Set.finite_coe_iff.mp this, le_trans ?_ hτ⟩
    unfold smallSectionCount
    have hcard := Nat.card_le_card_of_injective f hfi
    rcases Nat.eq_zero_or_pos
        (Nat.card {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)}) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)
  unfold arVolP
  simp only [one_mul]
  have hden : ∀ τ : ℕ, 0 ≤ ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := fun τ => by positivity
  refine limsup_le_limsup ?_ ?_ ?_
  · filter_upwards [hev] with τ hτ
    exact div_le_div_of_nonneg_right
      (smallSectionCount_mono_lattice _ τ (chartLat_le_chartLatNm y A.a τ) hτ.1) (hden τ)
  · exact isCoboundedUnder_le_of_le atTop fun τ => div_nonneg (Real.log_natCast_nonneg _) (hden τ)
  · refine isBoundedUnder_of_eventually_le
      (a := |R| * ((M : ℝ) * (1 + k)) ^ (D + 1) * ((D + 1).factorial : ℝ)) ?_
    filter_upwards [hev, eventually_ge_atTop 1] with τ hτ hτ1
    have hτ1' : (1 : ℝ) ≤ τ := by exact_mod_cast hτ1
    have hF : (0 : ℝ) < (D + 1).factorial := by positivity
    have hkp : (0 : ℝ) < (τ : ℝ) ^ (D + 1) := by positivity
    rw [div_le_iff₀ (by positivity)]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hMk : ((M * (τ + k) : ℕ) : ℝ) ≤ (M : ℝ) * (1 + k) * τ := by
      push_cast
      nlinarith [mul_nonneg hM0 hk0, mul_le_mul_of_nonneg_left hτ1' (mul_nonneg hM0 hk0)]
    calc smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ
        ≤ R * ((M * (τ + k) : ℕ) : ℝ) ^ (D + 1) := hτ.2
      _ ≤ |R| * ((M * (τ + k) : ℕ) : ℝ) ^ (D + 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self R) (by positivity)
      _ ≤ |R| * ((M : ℝ) * (1 + k) * τ) ^ (D + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hMk _) (abs_nonneg R)
      _ = |R| * ((M : ℝ) * (1 + k)) ^ (D + 1) * ((D + 1).factorial : ℝ) *
            ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
          rw [mul_pow]
          field_simp

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
