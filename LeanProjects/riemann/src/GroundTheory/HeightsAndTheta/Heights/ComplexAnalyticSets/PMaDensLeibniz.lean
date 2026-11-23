import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsPiola
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffBoundaryParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

namespace MaDensLeibniz

variable {D : ℕ}

theorem exists_open_contDiffOn (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) :
    ∃ U : Set (Fin D → ℂ), IsOpen U ∧ z ∈ U ∧ ContDiffOn ℝ 2 f U ∧ ContDiffOn ℝ 2 g U := by
  obtain ⟨U, hP, hU, hzU⟩ :=
    eventually_nhds_iff.mp ((hf.eventually (by simp)).and (hg.eventually (by simp)))
  exact ⟨U, hU, hzU, fun y hy => (hP y hy).1.contDiffWithinAt,
    fun y hy => (hP y hy).2.contDiffWithinAt⟩

theorem contDiffAt_cplx {f : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 f z) :
    ContDiffAt ℝ 2 (cplx f) z := by
  have h : cplx f = fun y => Complex.ofRealCLM (f y) := by funext y; simp [cplx]
  rw [h]
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hf

theorem dzb_cplx_mul (k : Fin D) (f g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    dzb k (cplx fun x => f x * g x) y = cplx f y * dzb k (cplx g) y + cplx g y * dzb k (cplx f) y := by
  rw [dzb_cplx_eq_star, dz_cplx_mul k f g y hf hg, dzb_cplx_eq_star, dzb_cplx_eq_star]
  simp [cplx, star_add]

theorem dzb_cplx_sq_half (k : Fin D) (f : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hf : DifferentiableAt ℝ f y) :
    dzb k (cplx fun x => f x ^ 2 / 2) y = cplx f y * dzb k (cplx f) y := by
  rw [dzb_cplx, dzb_cplx, fderiv_sq_half f y hf]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, cplx]
  push_cast
  ring

theorem hessC_mul (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) :
    hessC (fun y => f y * g y) z =
      (f z : ℂ) • hessC g z + (g z : ℂ) • hessC f z + gradMat f g z + gradMat g f z := by
  obtain ⟨U, hU, hzU, hfU, hgU⟩ := exists_open_contDiffOn f g z hf hg
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU (hfU.mul hgU) z hzU j k, hessCDz_thm D f U hU hfU z hzU j k,
    hessCDz_thm D g U hU hgU z hzU j k]
  have hev : dzb k (cplx fun y => f y * g y) =ᶠ[𝓝 z]
      fun y => cplx f y * dzb k (cplx g) y + cplx g y * dzb k (cplx f) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_mul k f g y ((hfU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      ((hgU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hF := (contDiffAt_cplx hf).differentiableAt (n := 2) (by norm_num)
  have hG := (contDiffAt_cplx hg).differentiableAt (n := 2) (by norm_num)
  have hF' := differentiableAt_dzb (j := k) (contDiffAt_cplx hf)
  have hG' := differentiableAt_dzb (j := k) (contDiffAt_cplx hg)
  rw [dz_congr hev, dz_add (hF.fun_mul hG') (hG.fun_mul hF'), dz_mul hF hG', dz_mul hG hF']
  simp only [gradMat, cplx]
  ring

theorem hessC_sq_half (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z) :
    hessC (fun y => f y ^ 2 / 2) z = (f z : ℂ) • hessC f z + gradMat f f z := by
  obtain ⟨U, hU, hzU, hfU, -⟩ := exists_open_contDiffOn f f z hf hf
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU ((hfU.pow 2).div_const 2) z hzU j k, hessCDz_thm D f U hU hfU z hzU j k]
  have hev : dzb k (cplx fun y => f y ^ 2 / 2) =ᶠ[𝓝 z] fun y => cplx f y * dzb k (cplx f) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_sq_half k f y ((hfU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hF := (contDiffAt_cplx hf).differentiableAt (n := 2) (by norm_num)
  have hF' := differentiableAt_dzb (j := k) (contDiffAt_cplx hf)
  rw [dz_congr hev, dz_mul hF hF']
  simp only [gradMat, cplx]
  ring

theorem mdisc_cons_add {n : ℕ} (A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (A + A') B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      mdisc (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
        mdisc (Fin.cons A' B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  simpa using mdisc_cons_smul_add 1 1 A A' B

theorem proof : MaDensLeibniz.Statement := by
  intro D φ f g z hf hg
  constructor
  · rw [maDens_cons_eq, maDens_cons_eq, maDens_cons_eq, hessC_mul f g z hf hg]
    unfold gradDens
    rw [mdisc_cons_add, mdisc_cons_add, mdisc_cons_smul_add]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
  · rw [maDens_cons_eq, maDens_cons_eq, hessC_sq_half f z hf]
    unfold gradDens
    rw [mdisc_cons_add, mdisc_cons_smul_fst]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring

end MaDensLeibniz

end

end GroundTheory.Heights₂.Heights
