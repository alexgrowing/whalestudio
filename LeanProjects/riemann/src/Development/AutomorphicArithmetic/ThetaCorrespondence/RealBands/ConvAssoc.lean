import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_assoc :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (e f h : G → ℂ) (C : ℝ),
      Continuous e → Integrable e μ → Continuous f → Integrable f μ → Continuous h → (∀ g, ‖h g‖ ≤ C) →
      (∀ x, conv μ e f x = f x) → ∀ x, conv μ f h x = conv μ e (conv μ f h) x := by
  intro G _ _ _ _ _ _ _ _ μ _ e f h C _ hei _ hfi hh hC hef x
  have h1 : Integrable (fun z : G × G => e z.1 * f z.2) (μ.prod μ) := hei.mul_prod hfi
  have h2 : Integrable (fun z : G × G => e z.1 * f (z.1⁻¹ * z.2)) (μ.prod μ) :=
    (measurePreserving_prod_inv_mul μ μ).integrable_comp_of_integrable h1
  have h3 : Integrable (fun z : G × G => e z.1 * f (z.1⁻¹ * z.2) * h (z.2⁻¹ * x)) (μ.prod μ) := by
    refine h2.mul_bdd (c := C) ?_ (Eventually.of_forall fun z => hC _)
    exact (hh.comp (continuous_snd.inv.mul continuous_const)).aestronglyMeasurable
  have h4 : ∀ g : G, conv μ f h (g⁻¹ * x) = ∫ y, f (g⁻¹ * y) * h (y⁻¹ * x) ∂μ := by
    intro g
    rw [← integral_mul_left_eq_self (fun y => f (g⁻¹ * y) * h (y⁻¹ * x)) g]
    simp only [conv, inv_mul_cancel_left, mul_inv_rev, mul_assoc]
  calc conv μ f h x = ∫ y, ∫ g, e g * f (g⁻¹ * y) * h (y⁻¹ * x) ∂μ ∂μ := by
        unfold conv
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        beta_reduce
        rw [integral_mul_const, ← hef y]
        rfl
    _ = ∫ g, ∫ y, e g * f (g⁻¹ * y) * h (y⁻¹ * x) ∂μ ∂μ :=
        (integral_integral_swap (f := fun g y => e g * f (g⁻¹ * y) * h (y⁻¹ * x)) h3).symm
    _ = conv μ e (conv μ f h) x := by
        show _ = ∫ g, e g * conv μ f h (g⁻¹ * x) ∂μ
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        beta_reduce
        rw [h4, ← integral_const_mul]
        simp only [mul_assoc]
