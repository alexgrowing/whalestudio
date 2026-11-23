import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedFDerivApply
open MeasureTheory

namespace GlobalTheory.SchwInt

theorem iteratedFDeriv_integral_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {P : Type} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]
    (μ : Measure P) [IsFiniteMeasureOnCompacts μ]
    (G : P → SchwartzMap V ℂ) (hG : Continuous G) (C : Set P) (hC : IsCompact C)
    (h0 : ∀ p ∉ C, G p = 0) :
    ∀ (n : ℕ) (x : V), iteratedFDeriv ℝ n (fun y => ∫ p, G p y ∂μ) x
      = ∫ p, iteratedFDeriv ℝ n (G p) x ∂μ := by
  have hzero : ∀ p ∉ C, ∀ (m : ℕ) (y : V), iteratedFDeriv ℝ m (G p) y = 0 := by
    intro p hp m y
    rw [h0 p hp]
    simp
  have hint : ∀ (m : ℕ) (y : V), Integrable (fun p => iteratedFDeriv ℝ m (G p) y) μ :=
    fun m y => integrable_of_zero_outside μ (continuous_iteratedFDeriv_apply hG m y) hC
      (fun p hp => hzero p hp m y)
  intro n
  induction n with
  | zero =>
    intro x
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ V ℂ).symm.toContinuousLinearEquiv.integral_comp_comm
      (fun p => G p x)).symm
  | succ n ih =>
    have ih' : iteratedFDeriv ℝ n (fun y => ∫ p, G p y ∂μ)
        = fun y => ∫ p, iteratedFDeriv ℝ n (G p) y ∂μ := funext ih
    intro x
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ
    have hF' : ∀ p y, fderiv ℝ (iteratedFDeriv ℝ n (G p)) y
        = L (iteratedFDeriv ℝ (n + 1) (G p) y) := fun p y => rfl
    have hderiv : HasFDerivAt (fun y => ∫ p, iteratedFDeriv ℝ n (G p) y ∂μ)
        (∫ p, fderiv ℝ (iteratedFDeriv ℝ n (G p)) x ∂μ) x := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
        (F' := fun y p => fderiv ℝ (iteratedFDeriv ℝ n (G p)) y)
        (bound := fun p => SchwartzMap.seminorm ℂ 0 (n + 1) (G p)) Filter.univ_mem
        (Filter.Eventually.of_forall fun y => (hint n y).aestronglyMeasurable) (hint n x)
        ?_ ?_ ?_ ?_
      · simp only [hF']
        exact (L.continuous.comp (continuous_iteratedFDeriv_apply hG (n + 1) x)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun p y _ => ?_
        rw [norm_fderiv_iteratedFDeriv]
        exact SchwartzMap.norm_iteratedFDeriv_le_seminorm (𝕜 := ℂ) (G p) (n + 1) y
      · refine integrable_of_zero_outside μ
          (((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (0, n + 1)).comp hG) hC ?_
        intro p hp
        simp only [Function.comp_apply, h0 p hp, map_zero]
      · refine Filter.Eventually.of_forall fun p y _ => ?_
        exact (((G p).smooth ⊤).differentiable_iteratedFDeriv
          (by exact_mod_cast ENat.coe_lt_top n) y).hasFDerivAt
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih', hderiv.fderiv]
    calc L.symm (∫ p, fderiv ℝ (iteratedFDeriv ℝ n (G p)) x ∂μ)
        = ∫ p, L.symm (fderiv ℝ (iteratedFDeriv ℝ n (G p)) x) ∂μ :=
          (L.symm.toContinuousLinearEquiv.integral_comp_comm _).symm
      _ = ∫ p, iteratedFDeriv ℝ (n + 1) (G p) x ∂μ := by
          congr 1

end GlobalTheory.SchwInt
