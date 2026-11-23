import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem upperHalfPlane_eq_zero_of_vanish_high :
    ∀ (f : ℍ → ℂ) (C : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
      (∀ τ : ℍ, C < τ.im → f τ = 0) → f = 0 := by
  intro f C hf hC
  have hd : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have han := hd.analyticOnNhd hopen
  have hpc : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  set z₀ : ℂ := ((|C| + 1 : ℝ) : ℂ) * Complex.I with hz₀
  have hz₀im : z₀.im = |C| + 1 := by simp [hz₀]
  have hmem : z₀ ∈ {z : ℂ | 0 < z.im} := by
    show 0 < z₀.im
    rw [hz₀im]; positivity
  have hev : (f ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds z₀] 0 := by
    have hopen2 : IsOpen {z : ℂ | max C 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have hin : z₀ ∈ {z : ℂ | max C 0 < z.im} := by
      show max C 0 < z₀.im
      rw [hz₀im]
      have := le_abs_self C
      have := abs_nonneg C
      exact max_lt (by linarith) (by linarith)
    filter_upwards [hopen2.mem_nhds hin] with z hz
    have hz' : max C 0 < z.im := hz
    have h0 : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz'
    have h1 : C < z.im := lt_of_le_of_lt (le_max_left _ _) hz'
    simp only [Function.comp_apply, Pi.zero_apply, UpperHalfPlane.ofComplex_apply_of_im_pos h0]
    exact hC _ h1
  have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc hmem hev
  funext τ
  have := heq (show (τ : ℂ) ∈ {z : ℂ | 0 < z.im} from τ.im_pos)
  simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this

end GlobalTheory
