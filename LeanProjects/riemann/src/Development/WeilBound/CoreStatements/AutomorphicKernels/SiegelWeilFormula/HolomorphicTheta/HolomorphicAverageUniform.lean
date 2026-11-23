import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolomorphicTranslationLevi
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HolomorphicTheta.IntHol
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HolomorphicTheta.ContinuousWeightFactor

noncomputable section

open Matrix Metric Set Filter Topology MeasureTheory
open scoped ComplexOrder

namespace PositivityTheory.SiegelWeilFormula.Holtb

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.HSt.HolTPf

theorem holomorphic_average_uniform : ∀ (n p q : ℕ) (e : ℤ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (ι : GR n →* G),
    Continuous ι →
    ∀ A : G → ℂ, Continuous A → (∀ g, IsHolW p q e fun y => A (g * ι y)) →
    ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (c : X → G) (u : X → ℂ) (C : Set G), IsCompact C →
      (∀ x, c x ∈ C) → (∀ x, ‖u x‖ ≤ 1) → (∀ y, AEStronglyMeasurable (fun x => A (c x * ι y) * u x) ν) →
      IsHolW p q e fun y => ∫ x, A (c x * ι y) * u x ∂ν := by
  intro n p q e G _ _ _ ι hι A hA hhol X _ ν _ c u C hC hcC hu hmeas
  choose H hHd hHe using hhol
  have hHe' : ∀ g y, A (g * ι y) = F0 p q e y * H g (bmap q y) := hHe
  have hval : ∀ g y, H g (bmap q y) = A (g * ι y) / F0 p q e y := by
    intro g y
    rw [hHe' g y]
    exact (mul_div_cancel_left₀ _ (spherical_section_ne_zero_group p q e y)).symm
  set f : X → (Fin n → Fin n → ℂ) → ℂ := fun x W => H (c x) W * u x with hf
  refine ⟨fun W => ∫ x, f x W ∂ν, ?_, ?_⟩
  · refine differentiableOn_integral_of_bdd (U := Dom n) isOpen_dom' f (fun x => (hHd (c x)).mul_const _) ?_ ?_
    · intro W hW
      obtain ⟨y, hy⟩ := bmap_surj q hW
      have h : (fun x => f x W) = fun x => (A (c x * ι y) * u x) * (F0 p q e y)⁻¹ := by
        funext x
        simp only [hf]
        rw [← hy, hval, div_eq_mul_inv]
        ring
      rw [h]
      exact (hmeas y).mul_const _
    · intro W₀ hW₀
      obtain ⟨r, hr, hsub, S, hS, hSW⟩ := bmap_local q W₀ hW₀
      obtain ⟨K, hK⟩ := (hC.prod hS).exists_bound_of_continuousOn
        ((hA.comp (continuous_fst.mul (hι.comp continuous_snd))).continuousOn)
      obtain ⟨y₀, hy₀S, -⟩ := hSW W₀ (mem_closedBall_self hr.le)
      obtain ⟨ym, hymS, hymin⟩ := hS.exists_isMinOn ⟨y₀, hy₀S⟩ (continuous_weight_factor p q e).norm.continuousOn
      have hm : 0 < ‖F0 p q e ym‖ := norm_pos_iff.2 (spherical_section_ne_zero_group p q e ym)
      refine ⟨r, hr, K / ‖F0 p q e ym‖, ball_subset_closedBall.trans hsub, fun x W hW => ?_⟩
      obtain ⟨y, hyS, hy⟩ := hSW W (ball_subset_closedBall hW)
      have hAy : ‖A (c x * ι y)‖ ≤ K := hK (c x, y) ⟨hcC x, hyS⟩
      have hmy : ‖F0 p q e ym‖ ≤ ‖F0 p q e y‖ := hymin hyS
      have hK0 : 0 ≤ K := (norm_nonneg _).trans hAy
      have hfx : ‖f x W‖ = ‖A (c x * ι y)‖ / ‖F0 p q e y‖ * ‖u x‖ := by
        simp only [hf]
        rw [← hy, hval, norm_mul, norm_div]
      rw [hfx]
      calc ‖A (c x * ι y)‖ / ‖F0 p q e y‖ * ‖u x‖ ≤ K / ‖F0 p q e ym‖ * 1 := by
            apply mul_le_mul _ (hu x) (norm_nonneg _) (by positivity)
            exact div_le_div₀ hK0 hAy hm hmy
        _ = K / ‖F0 p q e ym‖ := mul_one _
  · intro y
    show _ = F0 p q e y * ∫ x, f x (bmap q y) ∂ν
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hf]
    rw [hHe' (c x) y]
    ring

theorem holT : HolT := ⟨holomorphic_translation_levi, holomorphic_average_uniform⟩

end PositivityTheory.SiegelWeilFormula.Holtb
