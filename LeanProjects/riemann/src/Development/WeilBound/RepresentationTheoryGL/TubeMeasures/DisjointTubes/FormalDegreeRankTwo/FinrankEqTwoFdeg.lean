import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.TubeSt

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open GlobalTheory.CovTop.VolUp
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam.Z

theorem finrank_eq_two_fdeg (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Module.finrank ℚ E = 2 * fdeg E := by
  have h := NumberField.IsTotallyComplex.finrank (K := E)
  rw [fdeg, h]
  omega

theorem one_le_dE (E : Type) [Field E] [NumberField E] : 1 ≤ dE E := by
  rw [dE]
  have h0 := NumberField.discr_ne_zero E
  have h : (1 : ℤ) ≤ |NumberField.discr E| := Int.one_le_abs h0
  exact_mod_cast h

theorem massLev2_eq (E : Type) [Field E] [NumberField E] (r M : ℕ) :
    massLev2 E r M = (M : ℝ) ^ (Module.finrank ℚ E * r ^ 2) * 15 ^ (Module.finrank ℚ E * r ^ 2) *
      (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (r : ℝ) ^ 4 *
        (dE E ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^ (3 * Module.finrank ℚ E * r ^ 2) := rfl

theorem log_consts : 2 * Real.log 15 + 6 * (Real.log 3 + 2 * Real.log 2) ≤ 21 := by
  have hx : (0 : ℝ) < 15 ^ 2 * (3 * 2 ^ 2) ^ 6 := by norm_num
  have heq : 2 * Real.log 15 + 6 * (Real.log 3 + 2 * Real.log 2) =
      Real.log (15 ^ 2 * (3 * 2 ^ 2) ^ 6) := by
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  rw [heq, Real.log_le_iff_le_exp hx]
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h21 : Real.exp 1 ^ 21 = Real.exp 21 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [← h21]
  calc (15 : ℝ) ^ 2 * (3 * 2 ^ 2) ^ 6 ≤ 2.7 ^ 21 := by norm_num
    _ ≤ Real.exp 1 ^ 21 := pow_le_pow_left₀ (by norm_num) he 21

end MainStatements.Tam.Z

namespace MainStatements.Tam

end MainStatements.Tam

theorem MainStatements.Tam.size : SizeSt := by
  unfold MainStatements.Tam.SizeSt
  intro E _ _ _ r M L hr hM hL hfr hMl hd
  have hn := MainStatements.Tam.Z.finrank_eq_two_fdeg E
  have hd1 := MainStatements.Tam.Z.one_le_dE E
  have hc := MainStatements.Tam.Z.log_consts
  rw [MainStatements.Tam.Z.massLev2_eq]
  set n := Module.finrank ℚ E with hn_def
  set f := fdeg E with hf_def
  have hnpos' : 0 < n := Module.finrank_pos
  have hf1 : 1 ≤ f := by omega
  have hnR : (n : ℝ) = 2 * f := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf1
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hnpos : (0 : ℝ) < n := by rw [hnR]; linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hfpos : (0 : ℝ) < f := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hdpos : 0 < dE E := by linarith
  set X := dE E ^ ((1 : ℝ) / (n : ℝ)) with hX_def
  have hX1 : 1 ≤ X := Real.one_le_rpow hd1 (by positivity)
  have hXpos : 0 < X := by linarith
  have hlogX : Real.log X = (1 / (n : ℝ)) * Real.log (dE E) := Real.log_rpow hdpos _
  have hnX : (n : ℝ) * Real.log X = Real.log (dE E) := by
    rw [hlogX]
    field_simp
  set B : ℝ := 3 * ((n : ℝ) ^ 2 * (r : ℝ) ^ 4 * X ^ 2) with hB_def
  have hn1 : (1 : ℝ) ≤ n := by rw [hnR]; linarith
  have hB1 : 1 ≤ B := by
    have h1 : 1 ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
    have h2 : 1 ≤ (r : ℝ) ^ 4 := one_le_pow₀ (by linarith)
    have h3 : 1 ≤ X ^ 2 := one_le_pow₀ hX1
    have h4 : 1 ≤ (n : ℝ) ^ 2 * (r : ℝ) ^ 4 * X ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3
    rw [hB_def]
    linarith
  have hBpos : 0 < B := by linarith
  have h15 : (1 : ℝ) ≤ 15 := by norm_num
  constructor
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hMR) (one_le_pow₀ h15)) (one_le_pow₀ hB1)
  · have ha : (n : ℝ) ^ 2 ≠ 0 := (pow_pos hnpos 2).ne'
    have hb : (r : ℝ) ^ 4 ≠ 0 := (pow_pos hrpos 4).ne'
    have hx : X ^ 2 ≠ 0 := (pow_pos hXpos 2).ne'
    have hab : (n : ℝ) ^ 2 * (r : ℝ) ^ 4 ≠ 0 := mul_ne_zero ha hb
    have habx : (n : ℝ) ^ 2 * (r : ℝ) ^ 4 * X ^ 2 ≠ 0 := mul_ne_zero hab hx
    have hlogB : Real.log B = Real.log 3 + 2 * Real.log n + 4 * Real.log r + 2 * Real.log X := by
      rw [hB_def, Real.log_mul (by norm_num) habx, Real.log_mul hab hx, Real.log_mul ha hb,
        Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      ring
    have hm1 : (M : ℝ) ^ (n * r ^ 2) ≠ 0 := (pow_pos hMpos _).ne'
    have hm2 : (15 : ℝ) ^ (n * r ^ 2) ≠ 0 := (pow_pos (by norm_num) _).ne'
    have hm3 : B ^ (3 * n * r ^ 2) ≠ 0 := (pow_pos hBpos _).ne'
    rw [Real.log_mul (mul_ne_zero hm1 hm2) hm3, Real.log_mul hm1 hm2, Real.log_pow, Real.log_pow,
      Real.log_pow, hlogB]
    have hlogn : Real.log n = Real.log 2 + Real.log f := by
      rw [hnR, Real.log_mul (by norm_num) hfpos.ne']
    have hlfr : Real.log ((f : ℝ) * r) = Real.log f + Real.log r :=
      Real.log_mul hfpos.ne' hrpos.ne'
    rw [hlfr] at hfr
    rw [hlogn]
    push_cast
    rw [hnR] at hnX ⊢
    have hlf : 0 ≤ Real.log f := Real.log_nonneg hfR
    have hK : 0 ≤ (f : ℝ) * r ^ 2 := by positivity
    have pa := mul_le_mul_of_nonneg_left hMl hK
    have pb := mul_le_mul_of_nonneg_left hc hK
    have pc := mul_le_mul_of_nonneg_left hfr hK
    have pd := mul_nonneg hK hlf
    have pe := mul_nonneg hK (by linarith : (0 : ℝ) ≤ L - 1)
    have pf := mul_nonneg hK (by linarith : (0 : ℝ) ≤ L)
    have ph : (r : ℝ) ^ 2 * (2 * f * Real.log X) ≤ (r : ℝ) ^ 2 * (4 * f * L) := by
      rw [hnX]
      exact mul_le_mul_of_nonneg_left hd (by positivity)
    nlinarith [pa, pb, pc, pd, pe, pf, ph]

end
