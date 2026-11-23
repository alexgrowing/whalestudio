import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
import Development.WeilBound.CoreStatements.PluriharmonicCharts.TripleDeriv
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace PositivityTheory.Xgp.ProjectiveLineNormal

theorem holo_part {E M : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup M] [Module ℂ M]
    (H : E →ₗ[ℝ] M) : ∃ L : E →ₗ[ℂ] M, ∀ v, L v = (1 / 2 : ℂ) • (H v - Complex.I • H (Complex.I • v)) := by
  refine ⟨⟨⟨fun v => (1 / 2 : ℂ) • (H v - Complex.I • H (Complex.I • v)), ?_⟩, ?_⟩, fun v => rfl⟩
  · intro v w
    simp only [smul_add, map_add]
    module
  · intro c v
    have e1 : c • v = c.re • v + c.im • (Complex.I • v) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
    have e2 : Complex.I • c • v = c.re • (Complex.I • v) - c.im • v := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul, ← sub_smul]
      congr 1
      apply Complex.ext <;> simp
    simp only [RingHom.id_apply]
    rw [e2, e1, map_add, map_sub, H.map_smul, H.map_smul, H.map_smul, H.map_smul]
    generalize H v = A
    generalize H (Complex.I • v) = B
    simp only [← Complex.coe_smul]
    match_scalars
    · apply Complex.ext <;> simp [mul_comm]
    · apply Complex.ext <;> simp [mul_comm]

end PositivityTheory.Xgp.ProjectiveLineNormal

theorem PositivityTheory.Xgp.projective_line_normal_frame : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y₀ : Fin d → ℂ), (G y₀).PosDef → (∀ y, (G y).IsHermitian) → (∀ p q, ContDiffAt ℝ 2 (fun y => G y p q) y₀) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y => g y p q) ∧ IsUnit (g y₀).det ∧ (g y₀)ᴴ * G y₀ * g y₀ = 1 ∧ ∀ p q, fderiv ℝ (fun y => ((g y)ᴴ * G y * g y) p q) y₀ = 0 := by
  intro d G y₀ hpos hherm hC
  have hG : ∀ p q, DifferentiableAt ℝ (fun y => G y p q) y₀ := fun p q =>
    (hC p q).differentiableAt (by norm_num)
  obtain ⟨g0, hg0u, hg0⟩ : ∃ g0 : Matrix (Fin 2) (Fin 2) ℂ, IsUnit g0.det ∧ g0ᴴ * G y₀ * g0 = 1 := by
    open scoped MatrixOrder in
    obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos.posSemidef.nonneg
    have hdet := hpos.det_pos.ne'
    have hyu : IsUnit y.det := by
      rw [hy, det_mul] at hdet
      exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
    refine ⟨y⁻¹, isUnit_nonsing_inv_det y hyu, ?_⟩
    rw [hy, star_eq_conjTranspose, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_assoc,
      mul_nonsing_inv y hyu]
    simp
  let Dm : (Fin d → ℂ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    { toFun := fun v => Matrix.of fun p q => fderiv ℝ (fun y => G y p q) y₀ v
      map_add' := fun v w => by ext p q; simp
      map_smul' := fun c v => by ext p q; simp }
  have hDm : ∀ v, (Dm v)ᴴ = Dm v := by
    intro v
    ext p q
    have h1 := (PositivityTheory.Xgp.gram_grad.line_deriv _ y₀ (hG q p) v).star
    have h2 := PositivityTheory.Xgp.gram_grad.line_deriv _ y₀ (hG p q) v
    have e : (fun s : ℝ => star (G (y₀ + s • v) q p)) = fun s : ℝ => G (y₀ + s • v) p q := by
      funext s
      exact (hherm _).apply p q
    rw [e] at h1
    exact h1.unique h2
  let H : (Fin d → ℂ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    { toFun := fun v => g0ᴴ * Dm v * g0
      map_add' := fun v w => by rw [map_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c v => by rw [map_smul, Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hH : ∀ v, (H v)ᴴ = H v := by
    intro v
    show (g0ᴴ * Dm v * g0)ᴴ = g0ᴴ * Dm v * g0
    rw [conjTranspose_mul, conjTranspose_mul, hDm, conjTranspose_conjTranspose, Matrix.mul_assoc]
  obtain ⟨L, hL⟩ := PositivityTheory.Xgp.ProjectiveLineNormal.holo_part H
  have hLL : ∀ v, (L v)ᴴ + L v = H v := by
    intro v
    rw [hL, conjTranspose_smul, conjTranspose_sub, conjTranspose_smul, hH, hH]
    simp only [Complex.star_def, Complex.conj_I, map_div₀, map_one, map_ofNat]
    module
  let Λ : Fin 2 → Fin 2 → (Fin d → ℂ) →L[ℂ] ℂ := fun p q => LinearMap.toContinuousLinearMap
    { toFun := fun v => (g0 * L v) p q
      map_add' := fun v w => by rw [map_add, Matrix.mul_add]; rfl
      map_smul' := fun c v => by rw [map_smul, Matrix.mul_smul]; rfl }
  refine ⟨fun y => g0 - g0 * L (y - y₀), fun p q => ?_, by simpa using hg0u, by simpa using hg0, fun p q => ?_⟩
  · show Differentiable ℂ fun y => g0 p q - Λ p q (y - y₀)
    fun_prop
  · by_cases hd : DifferentiableAt ℝ
        (fun y => ((g0 - g0 * L (y - y₀))ᴴ * G y * (g0 - g0 * L (y - y₀))) p q) y₀
    swap
    · exact fderiv_zero_of_not_differentiableAt hd
    ext1 v
    have hV : ∀ p q, HasDerivAt (fun s : ℝ => (g0 - g0 * L (y₀ + s • v - y₀)) p q) ((-(g0 * L v)) p q) 0 := by
      intro p q
      have e : (fun s : ℝ => (g0 - g0 * L (y₀ + s • v - y₀)) p q) =
          fun s : ℝ => g0 p q - s • (g0 * L v) p q := by
        funext s
        rw [add_sub_cancel_left, L.map_smul_of_tower, Matrix.mul_smul]
        rfl
      rw [e]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ((g0 * L v) p q)).const_sub (g0 p q)
    have h1 := PositivityTheory.Xgp.gram_grad.triple_deriv (fun s : ℝ => G (y₀ + s • v))
      (fun s : ℝ => g0 - g0 * L (y₀ + s • v - y₀)) (Dm v) (-(g0 * L v)) 0
      (fun p q => PositivityTheory.Xgp.gram_grad.line_deriv _ y₀ (hG p q) v) hV p q
    have h3 := (PositivityTheory.Xgp.gram_grad.line_deriv _ y₀ hd v).unique h1
    rw [h3]
    simp only [zero_smul, add_zero, sub_self, map_zero, Matrix.mul_zero, sub_zero]
    have e1 : (-(g0 * L v))ᴴ * G y₀ * g0 = -(L v)ᴴ := by
      rw [conjTranspose_neg, conjTranspose_mul, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc (L v)ᴴ,
        Matrix.mul_assoc (L v)ᴴ, hg0, Matrix.mul_one]
    have e2 : g0ᴴ * G y₀ * -(g0 * L v) = -L v := by
      rw [Matrix.mul_neg, ← Matrix.mul_assoc, hg0, Matrix.one_mul]
    have e3 : g0ᴴ * Dm v * g0 = (L v)ᴴ + L v := (hLL v).symm
    rw [e1, e2, e3]
    simp
