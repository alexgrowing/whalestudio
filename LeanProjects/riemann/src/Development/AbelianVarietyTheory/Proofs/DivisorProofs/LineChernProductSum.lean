import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff

namespace GlobalTheory.ChernProd

theorem lineChern_eq_neg_ddc_log {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {f : E → ℝ} {y : E} (hf : ContDiffAt ℝ 2 f y)
    (hf0 : 0 < f y) (ξ η : E) :
    lineChern f y ξ η = -ddc (fun x => Real.log (f x)) y ξ η :=
  chernOne_line (n := Unit) hf hf0.ne' (Filter.Eventually.of_forall fun _ => rfl) ξ η

theorem lineChern_prod : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E]
    (T : Type) [Fintype T] (f : T → E → ℝ) (y : E),
    (∀ τ, ContDiffAt ℝ 2 (f τ) y) → (∀ τ, 0 < f τ y) → ∀ ξ η,
      lineChern (fun x => ∏ τ, f τ x) y ξ η = ∑ τ, lineChern (f τ) y ξ η := by
  intro E _ _ _ _ T _ f y hf hpos ξ η
  have hP : ContDiffAt ℝ 2 (fun x => ∏ τ, f τ x) y :=
    contDiffAt_prod fun τ _ => hf τ
  have hP0 : 0 < ∏ τ, f τ y := Finset.prod_pos fun τ _ => hpos τ
  rw [lineChern_eq_neg_ddc_log hP hP0]
  simp only [fun τ => lineChern_eq_neg_ddc_log (hf τ) (hpos τ) ξ η]
  have hev : ∀ᶠ x in nhds y, ∀ τ, 0 < f τ x :=
    Filter.eventually_all.2 fun τ => (hf τ).continuousAt.eventually (lt_mem_nhds (hpos τ))
  have hcongr : (fun x => Real.log (∏ τ, f τ x)) =ᶠ[nhds y] fun x => ∑ τ, Real.log (f τ x) :=
    hev.mono fun x hx => Real.log_prod fun τ _ => (hx τ).ne'
  have hl : ∀ τ ∈ (Finset.univ : Finset T), ContDiffAt ℝ 2 (fun x => Real.log (f τ x)) y :=
    fun τ _ => (hf τ).log (hpos τ).ne'
  simp only [ddc, leviForm_congr hcongr, leviForm_sum hl]
  simp [Finset.mul_sum, ContinuousLinearMap.sum_apply]

end GlobalTheory.ChernProd
