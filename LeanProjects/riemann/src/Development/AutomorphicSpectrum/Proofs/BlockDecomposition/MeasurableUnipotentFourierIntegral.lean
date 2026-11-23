import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth
open MeasureTheory

namespace GlobalTheory.CompanionTheory.GodementInt

lemma continuous_mul_blk :
    Continuous (fun p : Ad3.LR.M22 × (Fin 2 → ℝ) =>
      (Matrix.of.symm (Matrix.of p.1 * Ad3.LR.blk p.2) : Ad3.LR.M23)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  fin_cases j <;> simp [Ad3.LR.blk] <;> fun_prop

theorem measurable_integral_mul_blk (Ψ : Ad3.LR.M23 → ℂ) (β : ℝ) (hΨ : Continuous Ψ) :
    Measurable (fun h : Ad3.LR.M22 =>
      ∫ x : Fin 2 → ℝ, Ψ (Matrix.of.symm (Matrix.of h * Ad3.LR.blk x)) * Ad3.psiR (-(β * x 1))) := by
  have hψ : Continuous (fun p : Ad3.LR.M22 × (Fin 2 → ℝ) => Ad3.psiR (-(β * p.2 1))) := by
    unfold Ad3.psiR
    fun_prop
  have hf : Continuous (fun p : Ad3.LR.M22 × (Fin 2 → ℝ) =>
      Ψ (Matrix.of.symm (Matrix.of p.1 * Ad3.LR.blk p.2)) * Ad3.psiR (-(β * p.2 1))) :=
    (hΨ.comp continuous_mul_blk).mul hψ
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

end GlobalTheory.CompanionTheory.GodementInt
