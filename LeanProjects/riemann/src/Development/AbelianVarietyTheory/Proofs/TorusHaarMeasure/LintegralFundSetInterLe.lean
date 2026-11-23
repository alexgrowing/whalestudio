import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Unfold

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem lintegral_fundSet_inter_le : MeasInvStatement (E := E) → ∀ (r : ℕ) (X : Data E r) (x0 x1 : Frame X.Ψ r), IsOrth X x0 → IsOrth X x1 →
    ∀ FF, IsFundSet X x0 FF → ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ →
    (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (lact γ (rmul x b)) = φ x) →
    ∀ N : Set (V (nd X)), MeasurableSet N → N ⊆ OmF X x1 →
    ∫⁻ z in FF ∩ {z | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (cpt X x1 y) b)},
      φ (cpt X x0 z) ∂muF X x0 ≤ ∫⁻ y in N, φ (cpt X x1 y) ∂muF X x1 := by
  intro hM r X x0 x1 ho0 ho1 FF hF φ hφ hinv N hN hNO
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x := fun x hx b hb => by
    have h := hinv 1 X.Γ.one_mem x hx b hb
    rwa [FundSetPf.lact_one] at h
  let ψ : Frame X.Ψ r → ℝ≥0∞ := (satFrames X x1 N).indicator φ
  have hψ : Measurable ψ := hφ.indicator (measurableSet_satFrames X ho1 hN hNO)
  have hψB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    simp only [ψ, Set.indicator, rmul_mem_satFrames_iff X x1 N _ hb, hφB x hx b hb]
  have h1 : ∫⁻ y in N, φ (cpt X x1 y) ∂muF X x1 = ∫⁻ y, ψ (cpt X x1 y) ∂muF X x1 := by
    rw [← lintegral_indicator hN]
    refine lintegral_congr fun z => ?_
    simp only [ψ, Set.indicator, cpt_mem_satFrames_iff X ho1]
  rw [h1, ← hM r X x0 x1 ho0 ho1 ψ hψ hψB, lintegral_unfold hM r X x0 ho0 FF hF ψ hψ hψB]
  refine le_trans (setLIntegral_mono (g := fun z => ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z))) ?_ ?_)
    (lintegral_mono_set Set.inter_subset_left)
  · exact Measurable.tsum fun γ => (hψ.comp (continuous_lact X γ.1).measurable).comp hc
  · rintro z ⟨-, y, hy, γ, hγ, b, hb, h⟩
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨γ⁻¹, X.Γ.inv_mem hγ⟩ : X.Γ))
    have hm : rmul (cpt X x1 y) b ∈ satFrames X x1 N := ⟨y, hy, b, hb, rfl⟩
    show φ (cpt X x0 z) = ψ (lact γ⁻¹ (cpt X x0 z))
    rw [h, FundSetPf.lact_inv, hinv γ hγ _ (hNO hy) b hb]
    show _ = (satFrames X x1 N).indicator φ _
    rw [Set.indicator_of_mem hm, hφB _ (hNO hy) b hb]

end GlobalTheory.Unfold
