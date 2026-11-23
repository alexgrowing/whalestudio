import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RestrictedProductMeasureSet

theorem UpperTheory.Reformulated.B.Gla1.haar_const_of_haar_exists :
    UpperTheory.ConvolutionTheory.T4.HaarEx → UpperTheory.ConvolutionTheory.T4.HaarConst := by
  intro H V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K hRP μ μi m hμ hμi hm
  have hm1 := fun v => (hm v).1
  choose a ha0 ha using H V G Gi Gv q p K hRP μ μi m hμ hμi hm1
  obtain ⟨hq, hp, hK, -⟩ := hRP
  obtain ⟨A⟩ : Nonempty (TopologicalSpace.PositiveCompacts Gi) := inferInstance
  refine ⟨a ∅, ha0 ∅, fun S => ?_⟩
  have h : a ∅ = a S :=
    UpperTheory.restricted_product_measure V G Gi Gv q (fun v => p v) (fun v => K v) μ μi m hq.measurable
      (fun v => (hp v).measurable) (fun v => (hK v).measurableSet) (fun v => (hm v).2)
      ⟨A, A.isCompact.measurableSet,
        (MeasureTheory.Measure.measure_pos_of_nonempty_interior μi A.interior_nonempty).ne',
        A.isCompact.measure_lt_top.ne⟩ ∅ S (a ∅) (a S) (ha ∅) (ha S)
  exact h ▸ ha S
