import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CurveHasDerivAt

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.FL

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw.LVs.II (cE cE_hasDerivAt0 cE_add cE_zero cE_continuous mulL mulL_apply)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem fz_curve {X x : M2 n} (hX : IsLie X) (hx : InG x) (m : ℕ) (e : ℤ) (w : ℂ) (s : ℝ) :
    fz m e w (x * cE X s) = (x * cE X s).det ^ e * (u1 (x * cE X s)).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 (x * cE X s)).det) : ℝ) : ℂ) * (-w)) := by
  have hg : InG (x * cE X s) := inG_mul hx (inG_cE hX s)
  have hd := det_first_cayley_block_ne_zero hg
  have hmul : (u1 (x * cE X s)).det * (ub1 (x * cE X s)).det =
      ((Complex.normSq (u1 (x * cE X s)).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_adjoint hg, Matrix.det_conjTranspose]
    exact Complex.mul_conj _
  have hpos : (0 : ℝ) < Complex.normSq (u1 (x * cE X s)).det := Complex.normSq_pos.mpr hd
  unfold fz
  rw [hmul, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), Complex.ofReal_log hpos.le]

theorem fz_deriv {X x : M2 n} (hX : IsLie X) (hx : InG x) (m : ℕ) (e : ℤ) (w : ℂ) :
    ∃ R : ℂ, HasDerivAt (fun s : ℝ => fz m e w (x * cE X s)) R 0 ∧
      ‖R‖ ≤ ‖fz m e w x‖ * (|(e : ℝ)| * ‖rD X x‖ + ((m : ℝ) + 2 * ‖w‖) * ‖rA X x‖) := by
  have hd0 : det x ≠ 0 := (isUnit_det_of_InG hx).ne_zero
  have ha0 : (u1 x).det ≠ 0 := det_first_cayley_block_ne_zero hx
  have hfun : (fun s : ℝ => fz m e w (x * cE X s)) = fun s : ℝ =>
      (x * cE X s).det ^ e * (u1 (x * cE X s)).det ^ (-(m : ℤ)) *
        Complex.exp (((Real.log (Complex.normSq (u1 (x * cE X s)).det) : ℝ) : ℂ) * (-w)) :=
    funext fun s => fz_curve hX hx m e w s
  have hf0 : fz m e w x = (det x) ^ e * (u1 x).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 x).det) : ℝ) : ℂ) * (-w)) := by
    have h := fz_curve hX hx m e w 0
    rw [cE_zero, mul_one] at h
    exact h
  have hD : HasDerivAt (fun s : ℝ => det (x * cE X s))
      ((fderiv ℂ (fun y : M2 n => det y) x) (x * X)) 0 :=
    curve_deriv (fun y : M2 n => det y) cd_det X x
  have hA : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)) 0 :=
    curve_deriv (fun y : M2 n => (u1 y).det) cd_detu1 X x
  have hD0 : det (x * cE X 0) = det x := by rw [cE_zero, mul_one]
  have hA0 : (u1 (x * cE X 0)).det = (u1 x).det := by rw [cE_zero, mul_one]
  have hzD : HasDerivAt (fun z : ℂ => z ^ e) (↑e * det x ^ (e - 1)) (det (x * cE X 0)) := by
    rw [hD0]
    exact hasDerivAt_zpow e (det x) (Or.inl hd0)
  have hzA : HasDerivAt (fun z : ℂ => z ^ (-(m : ℤ)))
      (↑(-(m : ℤ)) * (u1 x).det ^ (-(m : ℤ) - 1)) ((u1 (x * cE X 0)).det) := by
    rw [hA0]
    exact hasDerivAt_zpow _ _ (Or.inl ha0)
  have hDz := hzD.comp (0 : ℝ) hD
  have hAz := hzA.comp (0 : ℝ) hA
  have hre : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det.re)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)).re 0 := by
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
    exact h2
  have him : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det.im)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)).im 0 := by
    have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
    exact h2
  have hN := ((hre.mul hre).add (him.mul him)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => Complex.normSq_apply (u1 (x * cE X s)).det)
  have hNne : Complex.normSq (u1 (x * cE X 0)).det ≠ 0 := by
    rw [hA0]
    exact (Complex.normSq_pos.mpr ha0).ne'
  have hL := hN.log hNne
  have hE := (hL.ofReal_comp.mul_const (-w)).cexp
  have hfin := (hDz.mul hAz).mul hE
  rw [hfun]
  refine ⟨_, hfin, ?_⟩
  simp only [hA0, hD0, Function.comp_apply]
  have hd' : (fderiv ℂ (fun y : M2 n => det y) x) (x * X) = rD X x * det x := by
    unfold rD
    field_simp
  have ha' : (fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X) = rA X x * (u1 x).det := by
    unfold rA
    field_simp
  have bound : ‖(det x ^ e * (u1 x).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 x).det) : ℝ) : ℂ) * (-w))) *
      ((e : ℂ) * rD X x + (-(m : ℂ)) * rA X x + ((2 * (rA X x).re : ℝ) : ℂ) * (-w))‖ ≤
      ‖fz m e w x‖ * (|(e : ℝ)| * ‖rD X x‖ + ((m : ℝ) + 2 * ‖w‖) * ‖rA X x‖) := by
    rw [norm_mul, hf0]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    refine norm_add₃_le.trans ?_
    have h1 : |(rA X x).re| ≤ ‖rA X x‖ := Complex.abs_re_le_norm _
    have h2 : 0 ≤ ‖w‖ := norm_nonneg _
    simp only [norm_mul, norm_neg, Complex.norm_intCast, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_two]
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  convert bound using 2
  rw [hd', ha']
  have hq : ((rA X x * (u1 x).det).re * (u1 x).det.re + (u1 x).det.re * (rA X x * (u1 x).det).re +
      ((rA X x * (u1 x).det).im * (u1 x).det.im + (u1 x).det.im * (rA X x * (u1 x).det).im)) /
      Complex.normSq (u1 x).det = 2 * (rA X x).re := by
    have hn : Complex.normSq (u1 x).det ≠ 0 := (Complex.normSq_pos.mpr ha0).ne'
    rw [div_eq_iff hn, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im]
    ring
  rw [hq]
  simp only [Pi.mul_apply, Function.comp_apply, cE_zero, mul_one]
  rw [zpow_sub_one₀ hd0, zpow_sub_one₀ ha0]
  push_cast
  field_simp

end PositivityTheory.Rg.Sw.HSt.FL
