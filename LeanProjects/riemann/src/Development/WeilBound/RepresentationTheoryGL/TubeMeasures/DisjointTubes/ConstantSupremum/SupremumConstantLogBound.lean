import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFundamentalDomainVolumeLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainVolumeLowerStatement

noncomputable section

namespace MainStatements.Tam.Plug

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

def supConst2 (E : Type) [Field E] [NumberField E] (r d M : ℕ) (w : ℝ) : ℝ :=
  locConst E r w (epsLev E d M w) * MainStatements.Tam.massLev2 E r M

theorem supConst_nonneg2 (E : Type) [Field E] [NumberField E] (r d M : ℕ) (w : ℝ) : 0 ≤ supConst2 E r d M w := by
  unfold supConst2 locConst multBd
  have h2 : Even (2 * fdeg E * r ^ 2) := by rw [mul_assoc]; exact even_two_mul _
  refine mul_nonneg (mul_nonneg (div_nonneg (by positivity) (pow_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) _))
    (h2.pow_nonneg _)) ?_
  unfold MainStatements.Tam.massLev2 MainStatements.Tam.massB
  positivity

section
open ReciprocityTheory.L2DbarEstimates GlobalTheory.SupConstSize Real

theorem supremum_constant_log_bound_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r d M : ℕ) (w L : ℝ), 2 ≤ r → 1 ≤ d → 1 ≤ M → 1 ≤ L → 1 ≤ w → Real.log (fdeg E * r) ≤ L → Real.log M ≤ 30 * L → Real.log (dE E) ≤ 4 * fdeg E * L → Real.log d ≤ 4 * L → Real.log w ≤ 2 * L → 1 ≤ supConst2 E r d M w ∧ Real.log (supConst2 E r d M w) ≤ 250 * (fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * L := by
  intro E _ _ _ r d M w L hr hd hM hL hw hfr hlM hdE hld hlw
  have hn := finrank_eq_two_fdeg E
  have hf1 : 1 ≤ fdeg E := by
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have hfR : (1 : ℝ) ≤ fdeg E := by exact_mod_cast hf1
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hfr' : Real.log (fdeg E) + Real.log r ≤ L := by
    rw [← Real.log_mul (by positivity) (by positivity)]; exact hfr
  have hf0 : 0 ≤ Real.log (fdeg E) := Real.log_nonneg hfR
  have hr0 : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  obtain ⟨hε0, hε1, hεB⟩ := epsLev_bounds E d M w hfR hd hM hw
  set B : ℝ := 3 * fdeg E * w * M * Real.sqrt d with hB
  have sd : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hdR
  have hB1 : 1 ≤ B := by
    have a : 1 ≤ (fdeg E : ℝ) * w := one_le_mul_of_one_le_of_one_le hfR hw
    have b : 1 ≤ (fdeg E : ℝ) * w * M := one_le_mul_of_one_le_of_one_le a hMR
    have c : 1 ≤ (fdeg E : ℝ) * w * M * Real.sqrt d := one_le_mul_of_one_le_of_one_le b sd
    rw [hB]; nlinarith
  have l2b := Real.log_two_lt_d9
  have l2a := Real.log_two_gt_d9
  have l3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]; exact Real.log_le_log (by norm_num) (by norm_num)
  have l16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hlB : Real.log B ≤ 2 * Real.log 2 + 35 * L := by
    rw [hB, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_sqrt (by linarith)]
    linarith
  obtain ⟨hm1, hml⟩ := multBd_size E r (epsLev E d M w) B hfR (by linarith) hε0 hB1 hεB
  obtain ⟨hc1, hcl⟩ := chart_factor_size E r w L hfR hr hw hL hfr' hlw
  obtain ⟨hM1, hMl⟩ := size E r M L hr hM hL hfr hlM hdE
  have hs : supConst2 E r d M w = (8 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r) *
      multBd E r (epsLev E d M w) * MainStatements.Tam.massLev2 E r M := by
    unfold supConst2 locConst; ring
  rw [hs]
  refine ⟨one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hc1 hm1) hM1, ?_⟩
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have hX0 : 0 ≤ (fdeg E : ℝ) * (r : ℝ) ^ 2 := by positivity
  have b1 : (fdeg E : ℝ) * (r : ℝ) ^ 2 / 2 * (12 * L + 16 * Real.log 2) ≤ (fdeg E : ℝ) * (r : ℝ) ^ 2 / 2 * (28 * L) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have b2 : 2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 *
      (Real.log 16 + 2 * (Real.log (fdeg E) + Real.log r) + Real.log (dE E) + Real.log B) ≤
      2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 * (43 * L + 4 * fdeg E * L) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hXY : (fdeg E : ℝ) * (r : ℝ) ^ 2 * L ≤ (fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * L := by
    have : 0 ≤ (r : ℝ) ^ 2 * L := by positivity
    have h := mul_le_mul_of_nonneg_right hfR (by positivity : (0:ℝ) ≤ (fdeg E : ℝ) * ((r : ℝ) ^ 2 * L))
    have e1 : (fdeg E : ℝ) * (r : ℝ) ^ 2 * L = 1 * ((fdeg E : ℝ) * ((r : ℝ) ^ 2 * L)) := by ring
    have e2 : (fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * L = (fdeg E : ℝ) * ((fdeg E : ℝ) * ((r : ℝ) ^ 2 * L)) := by ring
    rw [e1, e2]; exact h
  have hLY : L ≤ (fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * L := by
    have h1 : 1 ≤ (fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 := by
      have a : 1 ≤ (fdeg E : ℝ) ^ 2 := one_le_pow₀ hfR
      have b : 1 ≤ (r : ℝ) ^ 2 := one_le_pow₀ (by linarith)
      exact one_le_mul_of_one_le_of_one_le a b
    have := mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ L)
    linarith
  have c1 : (fdeg E : ℝ) * (r : ℝ) ^ 2 / 2 * (28 * L) = 14 * ((fdeg E : ℝ) * (r : ℝ) ^ 2 * L) := by ring
  have c2 : 2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 * (43 * L + 4 * fdeg E * L) =
      86 * ((fdeg E : ℝ) * (r : ℝ) ^ 2 * L) + 8 * ((fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * L) := by ring
  have c3 : 130 * (fdeg E : ℝ) * (r : ℝ) ^ 2 * L = 130 * ((fdeg E : ℝ) * (r : ℝ) ^ 2 * L) := by ring
  have c4 : 250 * (fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * L = 250 * ((fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * L) := by ring
  rw [c4]
  linarith

end

end MainStatements.Tam.Plug

end
