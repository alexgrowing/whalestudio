import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitScalarMul

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

namespace GlobalTheory.ExtChar

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special

theorem integrableOn_translate {n : ℕ} (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure]
    (Θ' : SUJ ε → ℂ) (h : LocallyIntegrable Θ' μ') (c : SUJ ε) {K : Set (SUJ ε)} (hK : IsCompact K) :
    IntegrableOn (fun g => Θ' (c * g)) K μ' := by
  have h1 : IntegrableOn Θ' ((fun g => c * g) '' K) μ' :=
    h.integrableOn_isCompact (hK.image (continuous_const.mul continuous_id))
  have h2 := ((measurePreserving_mul_left μ' c).integrableOn_comp_preimage
    (MeasurableEquiv.mulLeft c).measurableEmbedding).2 h1
  exact h2.mono_set (Set.subset_preimage_image _ _)

theorem integrableOn_avgChar {n : ℕ} [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure]
    (m : ℤ) (Θ' : SUJ ε → ℂ) (h : LocallyIntegrable Θ' μ') {K : Set (SUJ ε)} (hK : IsCompact K) :
    IntegrableOn (avgChar ε m Θ') K μ' := by
  unfold avgChar
  exact (integrable_finset_sum _ fun j _ => (integrableOn_translate ε μ' Θ' h _ hK).const_mul _).const_mul _

theorem locallyIntegrable_extChar : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (m : ℤ) (Θ' : SUJ ε → ℂ), LocallyIntegrable Θ' μ' → AEStronglyMeasurable (GlobalTheory.ExtChar.extChar ε m Θ') (letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) → LocallyIntegrable (GlobalTheory.ExtChar.extChar ε m Θ') (letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) := by
  intro n _ ε μ' _ m Θ' h hm
  have hsc : Continuous (scalarMul ε) := GlobalTheory.SqIntSU.continuous_scalarMul ε
  rw [locallyIntegrable_iff]
  intro K hK
  have hP : IsCompact (scalarMul ε ⁻¹' K) := by
    have := (isProperMap_iff_tendsto_cocompact.2 ⟨hsc, GlobalTheory.SqIntSU.scalarMul_proper ε⟩)
    exact this.isCompact_preimage hK
  have hK' : IsCompact (Prod.snd '' (scalarMul ε ⁻¹' K)) := hP.image continuous_snd
  have hmr := hm.restrict (s := K)
  rw [IntegrableOn]
  rw [Measure.restrict_map hsc.measurable hK.measurableSet] at hmr ⊢
  rw [integrable_map_measure hmr hsc.measurable.aemeasurable]
  have hz : Integrable (fun z : Circle => (z : ℂ) ^ m) circleHaar := by
    have hc : Continuous (fun z : Circle => (z : ℂ) ^ m) :=
      (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ))).zpow₀ m fun z => Or.inl (Circle.coe_ne_zero z)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 := hz.mul_prod (integrableOn_avgChar ε μ' m Θ' h hK')
  have h2 : IntegrableOn (fun p : Circle × SUJ ε => (p.1 : ℂ) ^ m * avgChar ε m Θ' p.2)
      (Set.univ ×ˢ (Prod.snd '' (scalarMul ε ⁻¹' K))) (circleHaar.prod μ') := by
    rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ]
    exact h1
  have h3 := h2.mono_set (t := _) (s := scalarMul ε ⁻¹' K) fun p hp => ⟨trivial, p, hp, rfl⟩
  have e : extChar ε m Θ' ∘ scalarMul ε = fun p : Circle × SUJ ε => (p.1 : ℂ) ^ m * avgChar ε m Θ' p.2 := by
    funext p
    exact extChar_scalarMul ε m Θ' p.1 p.2
  rw [e]
  exact h3

end GlobalTheory.ExtChar
