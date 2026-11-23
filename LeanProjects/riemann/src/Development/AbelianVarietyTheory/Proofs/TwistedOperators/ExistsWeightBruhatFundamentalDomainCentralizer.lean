import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

namespace GlobalTheory.WeightUnfold

theorem exists_weight (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H) (hcomm : IsMulCommutative (cent γ)) (μ : Measure H) [μ.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure] (𝓣 : Set (cent γ)) (hfd : IsFundamentalDomain (Γ.subgroupOf (cent γ)) 𝓣 dt) :
    ∃ α : H → ℝ≥0∞, Measurable α ∧ (∀ y, ∑' h : Γ.subgroupOf (cent γ), α (((h : cent γ) : H) * y) = 1) ∧ ∀ ψ : H → ℝ≥0∞, Measurable ψ → LeftInv (cent γ) ψ → ∫⁻ y, α y * ψ y ∂μ = dt 𝓣 * ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
  have hTcl : IsClosed ((cent γ : Subgroup H) : Set H) := Set.isClosed_centralizer _
  have hc : ∀ a b : cent γ, a * b = b * a := fun a b => hcomm.is_comm.comm a b
  haveI : LocallyCompactSpace (cent γ) := hTcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : dt.IsMulRightInvariant := ⟨fun g => by
    have : (fun x : cent γ => x * g) = (fun x => g * x) := funext fun x => hc x g
    rw [this]; exact map_mul_left_eq_self dt g⟩
  obtain ⟨β, hβm, hβ⟩ := exists_bruhat (T := cent γ) hTcl dt
  have hprod : Measurable fun p : H × cent γ => β (((p.2 : cent γ) : H) * p.1) :=
    hβm.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst)
  have hsec : ∀ x : H, Measurable fun t : cent γ => β ((t : H) * x) := fun x =>
    hβm.comp (measurable_subtype_coe.mul_const x)
  refine ⟨fun y => ∫⁻ t in 𝓣, β ((t : H) * y) ∂dt, ?_, ?_, ?_⟩
  · exact hprod.lintegral_prod_right'
  · intro y
    haveI : Countable Γ := by
      haveI : TopologicalSpace.SeparableSpace Γ := inferInstance
      exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance
    haveI : Countable (Γ.subgroupOf (cent γ)) := by
      refine Function.Injective.countable (f := fun h : Γ.subgroupOf (cent γ) => (⟨((h : cent γ) : H), h.2⟩ : Γ)) ?_
      intro a b hab
      apply Subtype.ext; apply Subtype.ext
      simpa using congrArg Subtype.val hab
    rw [← hβ y, hfd.lintegral_eq_tsum'' (fun t : cent γ => β ((t : H) * y))]
    refine tsum_congr fun h => lintegral_congr fun t => ?_
    congr 1
    have e : ((h • t : cent γ) : H) = ((h : cent γ) : H) * (t : H) := rfl
    rw [e, ← mul_assoc, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hc]
  · intro ψ hψm hψ
    haveI : dt.IsMulLeftInvariant := inferInstance
    have hq := isQuotMeasure_quotMeas (T := cent γ) dt μ hTcl

    have hinner : ∀ t : cent γ, ∫⁻ y, β ((t : H) * y) * ψ y ∂μ = ∫⁻ y, β y * ψ y ∂μ := by
      intro t
      have : (fun y => β ((t : H) * y) * ψ y) = fun y => (fun z => β z * ψ z) ((t : H) * y) := by
        funext y; show _ = β _ * ψ _; rw [hψ (t : H) t.2 y]
      rw [this]; exact lintegral_mul_left_eq_self (fun z => β z * ψ z) (t : H)
    have hC : ∫⁻ y, β y * ψ y ∂μ = ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
      rw [hq (fun y => β y * ψ y) (hβm.mul hψm)]
      refine lintegral_congr fun q => ?_
      have : (fun t : cent γ => β ((t : H) * Quotient.out q) * ψ ((t : H) * Quotient.out q)) = fun t : cent γ => β ((t : H) * Quotient.out q) * ψ (Quotient.out q) := by
        funext t; rw [hψ (t : H) t.2]
      rw [this, lintegral_mul_const _ (hsec _), hβ, one_mul]
      rfl
    calc ∫⁻ y, (∫⁻ t in 𝓣, β ((t : H) * y) ∂dt) * ψ y ∂μ
        = ∫⁻ y, ∫⁻ t in 𝓣, β ((t : H) * y) * ψ y ∂dt ∂μ := by
          refine lintegral_congr fun y => ?_
          rw [lintegral_mul_const _ (hsec y)]
      _ = ∫⁻ t in 𝓣, ∫⁻ y, β ((t : H) * y) * ψ y ∂μ ∂dt := by
          refine lintegral_lintegral_swap ?_
          exact (hprod.mul (hψm.comp measurable_fst)).aemeasurable
      _ = ∫⁻ t in 𝓣, ∫⁻ y, β y * ψ y ∂μ ∂dt := by
          refine lintegral_congr fun t => hinner t
      _ = dt 𝓣 * ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
          rw [lintegral_const, Measure.restrict_apply_univ, hC, mul_comm]

end GlobalTheory.WeightUnfold
