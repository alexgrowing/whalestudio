import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAt

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ComplexOrder

namespace GlobalTheory.GoodTop

theorem gram_smooth_isUnit_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → MContDiffAt ∞ (fun v => H A (e.symm v) ()) (e y) ∧ IsUnit (H A (e.symm (e y)) ()).det := by
  intro F _ σ X m E O H hH e he y hyO hye A hA
  refine ⟨fun a b => ?_, ?_⟩
  · obtain ⟨hre, him⟩ := hH.smooth y hyO A hA () a b
    have h1 : ContDiffAt ℝ ∞ (fun v => (H A (e.symm v) () a b).re) (e y) := contDiffAt_holoChart he hye hre
    have h2 : ContDiffAt ℝ ∞ (fun v => (H A (e.symm v) () a b).im) (e y) := contDiffAt_holoChart he hye him
    have h3 : ContDiffAt ℝ ∞ (fun v => ((H A (e.symm v) () a b).re : ℂ) + ((H A (e.symm v) () a b).im : ℂ) * Complex.I)
        (e y) :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp (e y) h1).add
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp (e y) h2).mul contDiffAt_const)
    exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => (Complex.re_add_im _).symm)
  · rw [e.left_inv hye]
    exact isUnit_iff_ne_zero.mpr (hH.posDef y hyO A hA ()).det_pos.ne'

end GlobalTheory.GoodTop
