import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem curvAt_germ_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G G' : V n → Matrix r r ℂ} {v : V n}
    (h : G =ᶠ[𝓝 v] G') : curvAt G v = curvAt G' v := by
  funext a b
  exact curv_congr h _ _

theorem cutForm_germ_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ ρ' : V n → ℝ}
    {G₀ G₁ G₀' G₁' : V n → Matrix r r ℂ} {v : V n} (hρ : ρ =ᶠ[𝓝 v] ρ') (h₀ : G₀ =ᶠ[𝓝 v] G₀')
    (h₁ : G₁ =ᶠ[𝓝 v] G₁') : cutForm ρ G₀ G₁ v = cutForm ρ' G₀' G₁' v := by
  funext a b
  have hc : (fun x => (ρ x : ℂ)) =ᶠ[𝓝 v] fun x => (ρ' x : ℂ) := hρ.mono fun x hx => by simp only [hx]
  simp only [cutForm]
  rw [dbar_congr hc, conn_congr h₀, conn_congr h₁]

theorem corrC_germ_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ ρ' : V n → ℝ}
    {G₀ G₁ G₀' G₁' : V n → Matrix r r ℂ} {v : V n} (hρ : ρ =ᶠ[𝓝 v] ρ') (h₀ : G₀ =ᶠ[𝓝 v] G₀')
    (h₁ : G₁ =ᶠ[𝓝 v] G₁') : corrC ρ G₀ G₁ v = corrC ρ' G₀' G₁' v := by
  simp only [corrC]
  rw [curvAt_germ_congr h₀, curvAt_germ_congr h₁, cutForm_germ_congr hρ h₀ h₁]

end GlobalTheory.GoodTop
