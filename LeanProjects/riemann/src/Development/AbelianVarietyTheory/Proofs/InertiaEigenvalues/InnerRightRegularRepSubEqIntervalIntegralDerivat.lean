import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.AutomorphicL2Unitary

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

theorem coeFn_right_translate {φ : G → ℂ} (h : MemL2Quotient Γ μ φ) (g : G) :
    R Γ μ g h.toL2 =ᵐ[quotMeasure Γ μ] fun q => φ (sec Γ q * g) := by
  rw [right_translate_toL2]
  refine (h.mul_right g).coeFn_toL2.trans (Filter.Eventually.of_forall fun q => ?_)
  have := (h.1.mul_right g).descend_mk (sec Γ q)
  rwa [mk_sec] at this

theorem inner_right_translate_integral {φ : G → ℂ} (h : MemL2Quotient Γ μ φ) (g : G) (H : L2 Γ μ) :
    inner ℂ H (R Γ μ g h.toL2) = ∫ q, starRingEnd ℂ (H q) * φ (sec Γ q * g) ∂quotMeasure Γ μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_right_translate h g] with q e
  simp [e, mul_comm]

theorem inner_R_sub_eq_intervalIntegral :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ (H : L2 Γ μ) (t : ℝ), Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s)) ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) → inner ℂ H (R Γ μ (c t) hf.toL2) - inner ℂ H hf.toL2 = ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
  intro G _ _ _ _ _ _ _ Γ _ μ _ _ _ c hc h0 f f' hf hf' hcf hd H t hint
  have ftc : ∀ x, ∫ s in (0 : ℝ)..t, f' (x * c s) = f (x * c t) - f (x * 1) := fun x => by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd x s)
      ((hcf.comp (continuous_const.mul hc)).intervalIntegrable _ _), h0]
  simp only [inner_right_translate_integral hf']
  rw [MeasureTheory.intervalIntegral_integral_swap hint, ← inner_sub_right, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have e1 := coeFn_right_translate hf 1
  rw [map_one, ContinuousLinearMap.one_apply] at e1
  filter_upwards [coeFn_right_translate hf (c t), e1, Lp.coeFn_sub (R Γ μ (c t) hf.toL2) hf.toL2] with q a b e
  rw [intervalIntegral.integral_const_mul, ftc, e, Pi.sub_apply, a, b]
  simp [mul_comm]

end GlobalTheory.AutomorphicL2Unitary
