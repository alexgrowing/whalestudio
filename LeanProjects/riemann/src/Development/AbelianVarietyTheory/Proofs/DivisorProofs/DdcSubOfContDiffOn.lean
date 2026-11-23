import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory

theorem ddc_sub_of_contDiffOn : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set (Pt E g)} (u₁ u₂ : Pt E g → ℝ), IsOpen U → ContDiffOn ℝ 2 u₁ U →
    ContDiffOn ℝ 2 u₂ U → ∀ P ∈ U, ∀ v w : Pt E g,
      ddc (fun Q => u₁ Q - u₂ Q) P v w = ddc u₁ P v w - ddc u₂ P v w := by
  intro g E _ _ U u₁ u₂ hU h1 h2 P hP v w
  have hd : ∀ Q ∈ U, DifferentiableAt ℝ u₁ Q ∧ DifferentiableAt ℝ u₂ Q := fun Q hQ =>
    ⟨(h1.contDiffAt (hU.mem_nhds hQ)).differentiableAt (by norm_num),
      (h2.contDiffAt (hU.mem_nhds hQ)).differentiableAt (by norm_num)⟩
  have key : ∀ x : Pt E g,
      (fun Q => fderiv ℝ (fun Q => u₁ Q - u₂ Q) Q (Complex.I • x)) =ᶠ[nhds P]
        (fun Q => fderiv ℝ u₁ Q (Complex.I • x) - fderiv ℝ u₂ Q (Complex.I • x)) := by
    intro x
    filter_upwards [hU.mem_nhds hP] with Q hQ
    rw [fderiv_fun_sub (hd Q hQ).1 (hd Q hQ).2]
    rfl
  have hdd : ∀ (u : Pt E g → ℝ), ContDiffOn ℝ 2 u U → ∀ y : Pt E g,
      DifferentiableAt ℝ (fun Q => fderiv ℝ u Q y) P := by
    intro u hu y
    have h3 : ContDiffAt ℝ 1 (fderiv ℝ u) P :=
      (hu.contDiffAt (hU.mem_nhds hP)).fderiv_right (by norm_num)
    exact (h3.differentiableAt (by norm_num)).clm_apply (differentiableAt_const y)
  unfold ddc
  rw [(key w).fderiv_eq, (key v).fderiv_eq,
    fderiv_fun_sub (hdd u₁ h1 _) (hdd u₂ h2 _), fderiv_fun_sub (hdd u₁ h1 _) (hdd u₂ h2 _)]
  simp only [ContinuousLinearMap.sub_apply]
  ring

end GlobalTheory
