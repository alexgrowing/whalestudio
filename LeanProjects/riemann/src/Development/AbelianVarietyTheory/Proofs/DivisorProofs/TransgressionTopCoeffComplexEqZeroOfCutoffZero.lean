import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem mixTop_position_zero {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n) :
    mixTop (intersection_update_fsHerm_neg_one K₁ 0 K₀ j) = 0 := by
  unfold mixTop
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun π _ =>
    Finset.sum_eq_zero fun u _ => mul_eq_zero_of_right _ ?_)
  refine Matrix.det_eq_zero_of_row_eq_zero j fun b => ?_
  simp [intersection_update_fsHerm_neg_one]

theorem cutForm_eq_zero {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ}
    (G₀ G₁ : V n → Matrix r r ℂ) {v : V n} (hρ : ρ =ᶠ[𝓝 v] (fun _ => 0)) :
    cutForm ρ G₀ G₁ v = 0 := by
  have h : dbar (fun x => (ρ x : ℂ)) v = dbar (fun _ : V n => (0 : ℂ)) v :=
    dbar_congr (hρ.mono fun x hx => by simp [hx])
  funext a b
  simp [cutForm, h]

theorem corrC_eq_zero_of_eventuallyEq_zero {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ}
    (G₀ G₁ : V n → Matrix r r ℂ) {v : V n} (hρ : ρ =ᶠ[𝓝 v] (fun _ => 0)) : corrC ρ G₀ G₁ v = 0 := by
  unfold corrC
  rw [cutForm_eq_zero G₀ G₁ hρ]
  exact Finset.sum_eq_zero fun j _ => mixTop_position_zero _ _ j

example : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} (G₀ G₁ : V n → Matrix r r ℂ) {v : V n}, ρ =ᶠ[𝓝 v] (fun _ => 0) → corrC ρ G₀ G₁ v = 0 :=
  by
  intro n r _ _ ρ G₀ G₁ v h
  exact corrC_eq_zero_of_eventuallyEq_zero G₀ G₁ h

end GlobalTheory.GoodTop
