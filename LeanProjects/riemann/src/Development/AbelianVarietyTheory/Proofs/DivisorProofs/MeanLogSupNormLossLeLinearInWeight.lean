import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConstantCmEvaluationFitsRoom
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LamSize

theorem one_le_fdeg_of_cm (E : Type) [Field E] [NumberField E] [IsCMField E] : 1 ≤ fdeg E := by
  have h : Module.finrank ℚ E = 2 * fdeg E := by rw [fdeg, IsTotallyComplex.finrank E]; omega
  have := Module.finrank_pos (R := ℚ) (M := E)
  omega

theorem one_le_dE_field (E : Type) [Field E] [NumberField E] : 1 ≤ dE E := by
  unfold dE
  have h := Int.one_le_abs (NumberField.discr_ne_zero E)
  rw [← Int.cast_abs]
  exact_mod_cast h

theorem neg_log_epStar_le (f M d w : ℝ) (hf : 1 ≤ f) (hM : 1 ≤ M) (hd : 1 ≤ d) (hw : 1 ≤ w) :
    0 < epStar (2 * M * Real.sqrt d) f w 1 ∧ epStar (2 * M * Real.sqrt d) f w 1 ≤ 1 ∧
      -Real.log (epStar (2 * M * Real.sqrt d) f w 1) ≤
        Real.log 2 + Real.log M + 1 / 2 * Real.log d + Real.log f + Real.log w := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hpi := Real.pi_gt_three
  have hsd : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd
  have hfw : 1 ≤ f * w := one_le_mul_of_one_le_of_one_le hf hw
  set A := 2 * M * Real.sqrt d * f * w with hA
  have hA1 : 1 ≤ A := by
    have h1 : 1 ≤ M * Real.sqrt d := one_le_mul_of_one_le_of_one_le hM hsd
    have : A = 2 * (M * Real.sqrt d) * (f * w) := by rw [hA]; ring
    rw [this]; nlinarith
  have hA0 : 0 < A := by linarith
  have hB : 0 < 2 * M * Real.sqrt d * (f * w + 2) * 1 * Real.log 2 := by positivity
  have hlow : 1 / A ≤ epStar (2 * M * Real.sqrt d) f w 1 := by
    unfold epStar
    refine le_min ((div_le_one hA0).2 hA1) ?_
    rw [div_le_div_iff₀ hA0 hB]
    have hMd : 0 < 2 * M * Real.sqrt d := by positivity
    have key : (f * w + 2) * Real.log 2 ≤ Real.pi * (f * w) := by nlinarith
    have : 1 * (2 * M * Real.sqrt d * (f * w + 2) * 1 * Real.log 2) = (2 * M * Real.sqrt d) * ((f * w + 2) * Real.log 2) := by ring
    rw [this]
    have : Real.pi * A = (2 * M * Real.sqrt d) * (Real.pi * (f * w)) := by rw [hA]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left key hMd.le
  have he0 : 0 < epStar (2 * M * Real.sqrt d) f w 1 := lt_of_lt_of_le (by positivity) hlow
  refine ⟨he0, min_le_left _ _, ?_⟩
  have h1 : Real.log (1 / A) ≤ Real.log (epStar (2 * M * Real.sqrt d) f w 1) :=
    Real.log_le_log (by positivity) hlow
  rw [one_div, Real.log_inv] at h1
  have hlA : Real.log A = Real.log 2 + Real.log M + 1 / 2 * Real.log d + Real.log f + Real.log w := by
    rw [hA, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_sqrt (by linarith)]
    ring
  linarith

theorem log_radius_le (E : Type) [Field E] [NumberField E] [IsCMField E] (r d M : ℕ) (w L : ℝ)
    (hr : 1 ≤ r) (hd : 1 ≤ d) (hM : 1 ≤ M) (hL : 1 ≤ L) (hw : 1 ≤ w)
    (hfr : Real.log (fdeg E * r) ≤ L) (hlM : Real.log M ≤ 30 * L) (hdE : Real.log (dE E) ≤ 4 * fdeg E * L)
    (hld : Real.log d ≤ 4 * L) (hlw : Real.log w ≤ 2 * L) :
    1 ≤ 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
      (3 * frameRadius w r / 5) ∧
    Real.log (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
      (3 * frameRadius w r / 5)) ≤ (4 * fdeg E + 32) * L := by
  have hf1 := one_le_fdeg_of_cm E
  have hf' : (1 : ℝ) ≤ fdeg E := by exact_mod_cast hf1
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hdE1 := one_le_dE_field E
  obtain ⟨he0, he1, hne⟩ := neg_log_epStar_le (fdeg E) M d w hf' hM' hd' hw
  have hepsdef : epsLev E d M w = epStar (2 * M * Real.sqrt d) (fdeg E) w 1 := rfl
  rw [← hepsdef] at he0 he1 hne
  obtain ⟨hX0, hX⟩ := GlobalTheory.room_log_radius (fdeg E) r (dE E) (epsLev E d M w) w hf1 hr hdE1 he0 hw
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
    (3 * frameRadius w r / 5) with hXdef
  clear_value X
  have hle : Real.log (epsLev E d M w) ≤ 0 := Real.log_nonpos he0.le he1
  have hn : (1 : ℝ) ≤ (fdeg E : ℝ) * r := one_le_mul_of_one_le_of_one_le hf' hr'
  have a1 : 0 ≤ Real.log (dE E) := Real.log_nonneg hdE1
  have a2 : 0 ≤ Real.log w := Real.log_nonneg hw
  have a3 : 0 ≤ Real.log (fdeg E : ℝ) := Real.log_nonneg hf'
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have a5 : 0 ≤ Real.log ((fdeg E : ℝ) * r) := Real.log_nonneg hn
  have a6 : 0 ≤ Real.log (1600 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have a7 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM'
  have a8 : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd'
  have hmul : Real.log ((fdeg E : ℝ) * r) = Real.log (fdeg E : ℝ) + Real.log r :=
    Real.log_mul (by positivity) (by positivity)
  have hc : Real.log (1600 / 3 : ℝ) ≤ 7 := by
    have h1 : Real.log (1600 / 3 : ℝ) ≤ Real.log ((2 : ℝ) ^ 10) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h1
    have := Real.log_two_lt_d9
    push_cast at h1
    linarith
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hfdL : 0 ≤ (fdeg E : ℝ) * L := by positivity
  have hX1 : 0 ≤ Real.log X := by rw [hX]; linarith
  refine ⟨?_, ?_⟩
  · by_contra hc'
    have := Real.log_neg hX0 (not_le.1 hc')
    linarith
  · rw [hX]
    have : (4 * (fdeg E : ℝ) + 32) * L = 4 * ((fdeg E : ℝ) * L) + 32 * L := by ring
    rw [this]
    linarith

theorem lamSup_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q d M : ℕ) (Om s t L : ℝ), 1 ≤ r → 1 ≤ d → 1 ≤ M → 1 ≤ L → 0 ≤ s → 0 ≤ t → Real.log (fdeg E * r) ≤ L → Real.log M ≤ 30 * L → Real.log (dE E) ≤ 4 * fdeg E * L → Real.log d ≤ 4 * L → Real.log (s + t + 1) ≤ 2 * L → lamSup E r q d M Om s t ≤ ((1 + |Om|) / 2 + L + (2 * q + 1) * (6 * fdeg E + 48) * L) * (s + t) := by
  intro E _ _ _ r q d M Om s t L hr hd hM hL hs ht hfr hlM hdE hld hlw
  have hw : (1 : ℝ) ≤ s + t + 1 := by linarith
  obtain ⟨hX1, hXle⟩ := log_radius_le E r d M (s + t + 1) L hr hd hM hL hw hfr hlM hdE hld hlw
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hcm : cmLen E r q d M (s + t + 1) = (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E)
      (Real.sqrt (epsLev E d M (s + t + 1)) / Real.sqrt (fdeg E))) (3 * frameRadius (s + t + 1) r / 5)) ^ (2 * q + 1) := rfl
  unfold lamSup
  rw [hcm]
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E)
      (Real.sqrt (epsLev E d M (s + t + 1)) / Real.sqrt (fdeg E))) (3 * frameRadius (s + t + 1) r / 5) with hXdef
  clear_value X
  have hX0 : 0 < X := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  unfold Formalism.L2.LamCM.pDeg
  push_cast
  set K : ℝ := 2 * (q : ℝ) + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  set Y := K * Real.log X with hY
  have hY0 : 0 ≤ Y := mul_nonneg hK0 hlX
  have hYle : Y ≤ K * ((4 * fdeg E + 32) * L) := mul_le_mul_of_nonneg_left hXle hK0
  have hlr : Real.log r ≤ L := by
    have hf' : (1 : ℝ) ≤ fdeg E := by exact_mod_cast one_le_fdeg_of_cm E
    have : Real.log (r : ℝ) ≤ Real.log ((fdeg E : ℝ) * r) :=
      Real.log_le_log (by positivity) (le_mul_of_one_le_left (by positivity) hf')
    linarith
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have hst : 0 ≤ s + t := by linarith
  have c1 : s * (Real.log r + Y) ≤ (s + t) * (L + Y) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) hst
  have c2 : (3 / 2 * Y) * (s + t) ≤ (K * (6 * fdeg E + 48) * L) * (s + t) := by
    refine mul_le_mul_of_nonneg_right ?_ hst
    have : K * (6 * (fdeg E : ℝ) + 48) * L = 3 / 2 * (K * ((4 * fdeg E + 32) * L)) := by ring
    rw [this]; linarith
  nlinarith

end GlobalTheory.LamSize
