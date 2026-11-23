import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.integral_unipFundamentalDomain_comp_lattice_preserving :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (α : (UPos n r → AdeleRing (𝓞 K) K) ≃ₜ+ (UPos n r → AdeleRing (𝓞 K) K)), (∀ X, α X ∈ unipLattice K n r ↔ X ∈ unipLattice K n r) → ∀ F : (UPos n r → AdeleRing (𝓞 K) K) → ℂ, (∀ ξ ∈ unipLattice K n r, ∀ X, F (ξ + X) = F X) → ∫ X in unipFundamentalDomain K n r, F (α X) ∂unipMeasure K n r = ∫ X in unipFundamentalDomain K n r, F X ∂unipMeasure K n r := by
  intro K _ _ n r α hα F hF
  haveI : TopologicalSpace.MetrizableSpace (UPos n r → AdeleRing (𝓞 K) K) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  haveI : (unipMeasure K n r).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hfd : IsAddFundamentalDomain (unipLattice K n r) (unipFundamentalDomain K n r) (unipMeasure K n r) :=
    isAddFundamentalDomain_unipFundamentalDomain
  have hsm := addEquivAddHaarChar_smul_map (unipMeasure K n r) α.symm
  have hpos := addEquivAddHaarChar_pos α.symm
  have hmap : (unipMeasure K n r).map α.symm = (addEquivAddHaarChar α.symm)⁻¹ • unipMeasure K n r := by
    conv_rhs => rw [← hsm]
    rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  have hqmp : Measure.QuasiMeasurePreserving α.symm (unipMeasure K n r) (unipMeasure K n r) :=
    ⟨α.symm.continuous.measurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
  let e : unipLattice K n r → unipLattice K n r := fun g => ⟨α g, (hα g).2 g.2⟩
  have he : Function.Bijective e := by
    refine ⟨fun g h hgh => ?_, fun g => ⟨⟨α.symm g, (hα (α.symm g)).1 (by simpa using g.2)⟩, ?_⟩⟩
    · apply Subtype.ext
      apply α.injective
      exact congrArg Subtype.val hgh
    · apply Subtype.ext
      simp [e]
  have hfd' : IsAddFundamentalDomain (unipLattice K n r) (α.symm ⁻¹' unipFundamentalDomain K n r)
      (unipMeasure K n r) :=
    hfd.preimage_of_equiv hqmp he (fun g x => by
      show α.symm (α g + x) = g + α.symm x
      simp [map_add])
  have hmeas := hfd'.measure_eq hfd
  have hpre := addEquivAddHaarChar_smul_preimage (unipMeasure K n r) (X := unipFundamentalDomain K n r) α.symm
  rw [hmeas, unipMeasure_unipFundamentalDomain, ENNReal.smul_def, smul_eq_mul, mul_one,
    ENNReal.coe_eq_one] at hpre
  have hmp : MeasurePreserving α.symm (unipMeasure K n r) (unipMeasure K n r) :=
    ⟨α.symm.continuous.measurable, by rw [hmap, hpre, inv_one, one_smul]⟩
  have key := hmp.setIntegral_preimage_emb α.symm.toHomeomorph.measurableEmbedding
    (fun y => F (α y)) (unipFundamentalDomain K n r)
  simp only [ContinuousAddEquiv.apply_symm_apply] at key
  rw [← key]
  exact hfd'.setIntegral_eq hfd (fun g x => hF g g.2 x)
