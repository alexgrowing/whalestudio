import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PshCore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCPsh

open Matrix Metric Real
open scoped MatrixOrder ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

abbrev cx (Y : Matrix ι ι ℝ) : Matrix ι ι ℂ := Y.map (fun x : ℝ => (x : ℂ))

theorem cx_mul (Y Z : Matrix ι ι ℝ) : cx (Y * Z) = cx Y * cx Z :=
  Matrix.map_mul (f := Complex.ofRealHom)

theorem cx_one : cx (1 : Matrix ι ι ℝ) = 1 := Matrix.map_one _ (by simp) (by simp)

theorem cx_inv {Y : Matrix ι ι ℝ} (hY : IsUnit Y.det) : (cx Y)⁻¹ = cx Y⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← cx_mul, Matrix.nonsing_inv_mul _ hY, cx_one]

theorem cx_posDef {Y : Matrix ι ι ℝ} (hY : Y.PosDef) : (cx Y).PosDef := by
  have hsymm : ∀ i j, Y j i = Y i j := fun i j => by
    have := congrFun (congrFun hY.isHermitian i) j
    simpa [conjTranspose_apply] using this
  refine PosDef.of_dotProduct_mulVec_pos (hY.isHermitian.map _ fun x => by simp) fun x hx => ?_
  set a : ι → ℝ := fun i => (x i).re
  set b : ι → ℝ := fun i => (x i).im
  have hre : ∀ (u v : ℂ) (y : ℝ), (star u * ((y : ℂ) * v)).re = y * (u.re * v.re + u.im * v.im) :=
    fun u v y => by simp [Complex.mul_re, Complex.mul_im]; ring
  have him : ∀ (u v : ℂ) (y : ℝ), (star u * ((y : ℂ) * v)).im = y * (u.re * v.im - u.im * v.re) :=
    fun u v y => by simp [Complex.mul_re, Complex.mul_im]; ring
  have e1 : star x ⬝ᵥ (cx Y *ᵥ x) = ∑ i, ∑ j, star (x i) * ((Y i j : ℂ) * x j) := by
    simp [dotProduct, mulVec, Finset.mul_sum]
  have e2 : a ⬝ᵥ (Y *ᵥ a) + b ⬝ᵥ (Y *ᵥ b) =
      ∑ i, ∑ j, Y i j * ((x i).re * (x j).re + (x i).im * (x j).im) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib, a, b]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have e3 : ∑ i, ∑ j, Y i j * ((x i).re * (x j).im - (x i).im * (x j).re) = 0 := by
    have hswap : ∑ i, ∑ j, Y i j * ((x i).im * (x j).re) =
        ∑ i, ∑ j, Y i j * ((x i).re * (x j).im) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsymm]; ring
    simp only [mul_sub, Finset.sum_sub_distrib, hswap, sub_self]
  have key : star x ⬝ᵥ (cx Y *ᵥ x) = ((a ⬝ᵥ (Y *ᵥ a) + b ⬝ᵥ (Y *ᵥ b) : ℝ) : ℂ) := by
    rw [e1]
    apply Complex.ext
    · simp only [Complex.re_sum, hre, Complex.ofReal_re, e2]
    · simp only [Complex.im_sum, him, Complex.ofReal_im, e3]
  rw [key]
  have ha := hY.posSemidef.dotProduct_mulVec_nonneg a
  have hb := hY.posSemidef.dotProduct_mulVec_nonneg b
  simp only [star_trivial] at ha hb
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push Not at h; exact hx (funext h)
  have hpos : 0 < a ⬝ᵥ (Y *ᵥ a) + b ⬝ᵥ (Y *ᵥ b) := by
    by_cases hai : a = 0
    · have hbi : b ≠ 0 := by
        intro hbi
        apply hi
        apply Complex.ext
        · simpa using congrFun hai i
        · simpa using congrFun hbi i
      have := hY.dotProduct_mulVec_pos hbi
      simp only [star_trivial] at this
      linarith
    · have := hY.dotProduct_mulVec_pos hai
      simp only [star_trivial] at this
      linarith
  exact_mod_cast hpos

theorem exists_factor {A : Matrix κ κ ℂ} (hA : A.PosDef) :
    ∃ B : Matrix κ κ ℂ, IsUnit B.det ∧ A = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  refine ⟨B, ?_, hB⟩
  have hdet : A.det ≠ 0 := (hA.det_pos).ne'
  rw [hB, det_mul, star_eq_conjTranspose, det_conjTranspose] at hdet
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)

theorem mulVec_injective_of_rank {F : Matrix ι κ ℂ} (h : F.rank = Fintype.card κ) :
    Function.Injective F.mulVec := by
  have hrn := LinearMap.finrank_range_add_finrank_ker F.mulVecLin
  rw [← Matrix.rank, h, Module.finrank_fintype_fun_eq_card] at hrn
  have hk : LinearMap.ker F.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  exact LinearMap.ker_eq_bot.mp hk

theorem analyticOnNhd_det {s : Set ℂ} {M : ℂ → Matrix κ κ ℂ}
    (hM : ∀ i j, AnalyticOnNhd ℂ (fun ζ => M ζ i j) s) :
    AnalyticOnNhd ℂ (fun ζ => (M ζ).det) s := by
  have : (fun ζ => (M ζ).det) =
      fun ζ => ∑ σ : Equiv.Perm κ, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M ζ (σ i) i := by
    funext ζ
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [this]
  intro z hz
  refine Finset.univ.analyticAt_fun_sum fun σ _ => ?_
  exact analyticAt_const.mul (Finset.univ.analyticAt_fun_prod fun i _ => hM _ _ z hz)

theorem re_trace_eq (W : Matrix ι κ ℂ) (Y : Matrix ι ι ℝ) :
    RCLike.re (Wᴴ * cx Y * W).trace =
      ∑ j, ∑ k, (∑ a, (star (W j a) * W k a).re) * Y j k := by
  calc RCLike.re (Wᴴ * cx Y * W).trace
      = ∑ a, ∑ k, ∑ j, (star (W j a) * W k a).re * Y j k := by
        simp only [trace, diag, mul_apply, conjTranspose_apply, map_apply, RCLike.re_to_complex,
          Complex.re_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
    _ = ∑ j, ∑ k, ∑ a, (star (W j a) * W k a).re * Y j k := by
        rw [Finset.sum_comm]
        rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
        rw [Finset.sum_comm]
    _ = _ := by simp only [Finset.sum_mul]

end

end GroundTheory.Heights₂.Heights.MCPsh
