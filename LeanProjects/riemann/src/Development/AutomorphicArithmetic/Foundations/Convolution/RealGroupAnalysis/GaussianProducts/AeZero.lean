import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem kappa_ne_zero {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F)
    {U : Set (G1 F)} (hU : IsOpen U) {k : G1 F} (hk : k ∈ KK F) (hkU : k ∈ U) : M.κ U ≠ 0 := by
  intro h0
  obtain ⟨hKs, hC⟩ := UpperTheory.ConvolutionTheory.R2.M.kkCpt F
  have hmem : ∀ x ∈ KK F, ∀ y ∈ KK F, x * y⁻¹ ∈ KK F := by
    intro x hx y hy
    rw [hKs] at hx hy ⊢
    exact (UpperTheory.ConvolutionTheory.R2.M.Ks F).mul_mem hx ((UpperTheory.ConvolutionTheory.R2.M.Ks F).inv_mem hy)
  have hnull : ∀ c ∈ KK F, M.κ ((fun x => c * x) ⁻¹' U) = 0 := by
    intro c hc
    have hm : Measurable (fun x : G1 F => c * x) := (continuous_const.mul continuous_id).measurable
    rw [← Measure.map_apply hm hU.measurableSet, M.κ_left c hc]
    exact h0
  obtain ⟨t, ht, hcov⟩ := hC.elim_nhds_subcover (fun x => (fun y => (k * x⁻¹) * y) ⁻¹' U) (by
    intro x hx
    refine ((continuous_const.mul continuous_id).isOpen_preimage _ hU).mem_nhds ?_
    simpa using hkU)
  have hK0 : M.κ (KK F) = 0 := by
    refine measure_mono_null hcov ?_
    exact (measure_biUnion_null_iff t.countable_toSet).2 fun x hx => hnull _ (hmem k hk x (ht x hx))
  haveI := M.prob
  have hle : M.κ Set.univ ≤ M.κ (KK F) + M.κ (KK F)ᶜ := by
    rw [← Set.union_compl_self (KK F)]
    exact measure_union_le _ _
  rw [hK0, M.supp, measure_univ] at hle
  simp at hle

theorem UpperTheory.ConvolutionTheory.R2.G.aeZero :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (u : IdeleGroup F × G1 F → ℂ), ContinuousOn u (Set.univ ×ˢ KK F) → (∀ᵐ p ∂M.ν, u p = 0) →
    ∀ a, ∀ k ∈ KK F, u (a, k) = 0 := by
  intro F _ _ _ M u hu h a k hk
  by_contra hne
  haveI := M.prob
  have hc : ContinuousWithinAt u (Set.univ ×ˢ KK F) (a, k) := hu (a, k) ⟨Set.mem_univ _, hk⟩
  have h1 : {p | u p ≠ 0} ∈ 𝓝[Set.univ ×ˢ KK F] (a, k) := hc.eventually_ne hne
  rw [nhdsWithin_prod_eq, Filter.mem_prod_iff] at h1
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := h1
  rw [nhdsWithin_univ, mem_nhds_iff] at ht₁
  obtain ⟨V, hVt, hVo, haV⟩ := ht₁
  obtain ⟨U, hUo, hkU, hUt⟩ := mem_nhdsWithin.1 ht₂
  have hnull : M.ν (V ×ˢ (U ∩ KK F)) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 h)
    intro p hp
    exact hsub ⟨hVt hp.1, hUt hp.2⟩
  have hprod : ideleMeasure F V * M.κ (U ∩ KK F) = 0 := by
    rw [← Measure.prod_prod]
    exact hnull
  have hV : ideleMeasure F V ≠ 0 := hVo.measure_ne_zero _ ⟨a, haV⟩
  have hU : M.κ (U ∩ KK F) ≠ 0 := by
    intro h0
    refine kappa_ne_zero M hUo hk hkU (measure_mono_null (t := (U ∩ KK F) ∪ (KK F)ᶜ) ?_ ?_)
    · intro x hx
      by_cases hxK : x ∈ KK F
      · exact Or.inl ⟨hx, hxK⟩
      · exact Or.inr hxK
    · exact measure_union_null h0 M.supp
  exact (mul_ne_zero hV hU) hprod
