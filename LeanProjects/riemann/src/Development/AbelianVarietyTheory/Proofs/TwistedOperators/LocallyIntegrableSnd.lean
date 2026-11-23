import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitScalarMul
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.ExtCharInt

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special GlobalTheory.DSSU.borelSpace_SUJ

theorem scalarMul_cen {n : ℕ} [NeZero n] (ε : Fin n → Bool) (j : ZMod n) (z : Circle) (g : SUJ ε) :
    scalarMul ε (z * ZMod.toCircle j, GlobalTheory.ExtChar.cen ε j * g) = scalarMul ε (z, g) := by
  rw [GlobalTheory.SqIntSU.scalarMul_apply, GlobalTheory.SqIntSU.scalarMul_apply]
  show GlobalTheory.SqIntSU.unitScalar ε (z * ZMod.toCircle j) *
      (GlobalTheory.SqIntSU.unitScalar ε (ZMod.toCircle j)⁻¹ * (g : UJ ε)) = _
  rw [← mul_assoc, ← GlobalTheory.SqIntSU.unitScalar_mul, mul_inv_cancel_right]

theorem locallyIntegrable_snd {n : ℕ} (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [SFinite μ'] (Θ' : SUJ ε → ℂ)
    (h : LocallyIntegrable Θ' μ') :
    LocallyIntegrable (fun p : Circle × SUJ ε => Θ' p.2) (circleHaar.prod μ') := by
  intro x
  obtain ⟨U, hU, hi⟩ := h x.2
  refine ⟨Set.univ ×ˢ U, prod_mem_nhds Filter.univ_mem hU, ?_⟩
  rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ]
  exact hi.comp_snd circleHaar

theorem integral_extChar : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (m : ℤ) (Θ' : SUJ ε → ℂ), LocallyIntegrable Θ' μ' → LocallyIntegrable (GlobalTheory.ExtChar.extChar ε m Θ') (letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) → ∀ f : UJ ε → ℂ, Continuous f → HasCompactSupport f → ∫ x, f x * GlobalTheory.ExtChar.extChar ε m Θ' x ∂(letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) = ∫ g, (∫ z, f (scalarMul ε (z, g)) * (z : ℂ) ^ m ∂circleHaar) * Θ' g ∂μ' := by
  intro n _ ε μ' _ m Θ' hΘ hE f hf hfc
  haveI : SFinite μ' := inferInstance
  have hsc : Continuous (scalarMul ε) := GlobalTheory.SqIntSU.continuous_scalarMul ε
  have hI : Integrable (fun x => f x * GlobalTheory.ExtChar.extChar ε m Θ' x)
      (Measure.map (scalarMul ε) (circleHaar.prod μ')) := by
    simpa only [smul_eq_mul] using hE.integrable_smul_left_of_hasCompactSupport hf hfc
  rw [integral_map hsc.aemeasurable hI.aestronglyMeasurable]

  set G : Circle × SUJ ε → ℂ := fun p => f (scalarMul ε p) * (p.1 : ℂ) ^ m * Θ' p.2 with hGdef
  have hzc : Continuous fun z : Circle => (z : ℂ) ^ m :=
    Continuous.zpow₀ continuous_subtype_val m (fun z => Or.inl (Circle.coe_ne_zero z))
  have hc : Continuous fun p : Circle × SUJ ε => f (scalarMul ε p) * (p.1 : ℂ) ^ m :=
    (hf.comp hsc).mul (hzc.comp continuous_fst)
  have hprop : IsProperMap (scalarMul ε) :=
    isProperMap_iff_tendsto_cocompact.2 ⟨hsc, GlobalTheory.SqIntSU.scalarMul_proper ε⟩
  have hcs : HasCompactSupport fun p : Circle × SUJ ε => f (scalarMul ε p) * (p.1 : ℂ) ^ m := by
    refine HasCompactSupport.intro (hprop.isCompact_preimage hfc) fun p hp => ?_
    have : f (scalarMul ε p) = 0 := image_eq_zero_of_notMem_tsupport hp
    simp [this]
  have hG : Integrable G (circleHaar.prod μ') := by
    simpa only [smul_eq_mul, hGdef] using
      (locallyIntegrable_snd ε μ' Θ' hΘ).integrable_smul_left_of_hasCompactSupport hc hcs

  have hT : ∀ j : ZMod n, MeasurePreserving (Prod.map (fun z : Circle => z * ZMod.toCircle j)
      (fun g : SUJ ε => GlobalTheory.ExtChar.cen ε j * g)) (circleHaar.prod μ') (circleHaar.prod μ') := fun j =>
    (measurePreserving_mul_right circleHaar _).prod (measurePreserving_mul_left μ' _)
  have hEmb : ∀ j : ZMod n, MeasurableEmbedding (Prod.map (fun z : Circle => z * ZMod.toCircle j)
      (fun g : SUJ ε => GlobalTheory.ExtChar.cen ε j * g)) := fun j =>
    ((MeasurableEquiv.mulRight (ZMod.toCircle j)).prodCongr
      (MeasurableEquiv.mulLeft (GlobalTheory.ExtChar.cen ε j))).measurableEmbedding
  have hpt : ∀ p : Circle × SUJ ε, f (scalarMul ε p) * GlobalTheory.ExtChar.extChar ε m Θ' (scalarMul ε p) =
      (n : ℂ)⁻¹ * ∑ j : ZMod n, G (Prod.map (fun z : Circle => z * ZMod.toCircle j)
        (fun g : SUJ ε => GlobalTheory.ExtChar.cen ε j * g) p) := by
    rintro ⟨z, g⟩
    rw [GlobalTheory.ExtChar.extChar_scalarMul, GlobalTheory.ExtChar.avgChar, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hGdef, Prod.map, scalarMul_cen, Circle.coe_mul, mul_zpow]
    ring
  simp only [hpt]
  rw [integral_const_mul, integral_finset_sum (f := fun j p => G (Prod.map (fun z : Circle => z * ZMod.toCircle j)
      (fun g : SUJ ε => GlobalTheory.ExtChar.cen ε j * g) p)) _ (fun j _ => ((hT j).integrable_comp_emb (hEmb j)).2 hG)]
  simp only [fun j => (hT j).integral_comp (hEmb j) G]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (NeZero.ne n)), one_mul, integral_prod_symm G hG]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [hGdef]
  exact integral_mul_const _ _

end GlobalTheory.ExtCharInt
