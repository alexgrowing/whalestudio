import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.MeasurableSetUS
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal

theorem UpperTheory.exists_haar_restrict_range_eq_smul_map_of_invariant :
    ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (e : X → G) (ν : Measure X) [IsFiniteMeasureOnCompacts ν], IsOpenEmbedding e → (1 : G) ∈ Set.range e → (∀ a ∈ Set.range e, ∀ b ∈ Set.range e, a * b ∈ Set.range e) → (∀ a ∈ Set.range e, a⁻¹ ∈ Set.range e) → ν ≠ 0 → (∀ x, ∃ T : X → X, MeasurePreserving T ν ν ∧ ∀ y, e x * e y = e (T y)) → ∃ c : ℝ≥0, μ.restrict (Set.range e) = c • ν.map e := by
  intro G X _ _ _ _ _ _ _ _ μ _ _ _ _ e ν _ he h1 hmul hinv hν hT
  let H : Subgroup G :=
    { carrier := Set.range e
      mul_mem' := fun ha hb => hmul _ ha _ hb
      one_mem' := h1
      inv_mem' := fun ha => hinv _ ha }
  have hHo : IsOpen (H : Set G) := he.isOpen_range
  have hemb : IsOpenEmbedding (H.subtype) := hHo.isOpenEmbedding_subtypeVal
  haveI : LocallyCompactSpace H := hemb.locallyCompactSpace
  haveI hHaar : (μ.comap H.subtype).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) μ hemb
  have hme : MeasurableEmbedding (H.subtype) := hemb.measurableEmbedding
  let e' : X → H := fun x => ⟨e x, x, rfl⟩
  have he'c : Continuous e' := he.continuous.subtype_mk _
  have he'i : IsInducing e' :=
    (IsInducing.of_comp_iff (g := H.subtype) IsInducing.subtypeVal).mp he.isInducing
  have he'sur : Function.Surjective e' := by
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  have hval : H.subtype ∘ e' = e := rfl
  have hlamval : (ν.map e').map H.subtype = ν.map e := by
    rw [Measure.map_map hme.measurable he'c.measurable, hval]
  have hlam0 : ν.map e' ≠ 0 := by
    intro h0
    apply hν
    rw [← Measure.measure_univ_eq_zero]
    have := congrArg (fun m : Measure H => m Set.univ) h0
    simpa [Measure.map_apply he'c.measurable MeasurableSet.univ] using this
  haveI : IsFiniteMeasureOnCompacts (ν.map e') := ⟨fun K hK => by
    rw [Measure.map_apply he'c.measurable hK.measurableSet]
    exact (he'i.isCompact_preimage (by simp [he'sur.range_eq]) hK).measure_lt_top⟩
  haveI : (ν.map e').IsMulLeftInvariant := ⟨fun h => by
    obtain ⟨_, x, rfl⟩ := h
    obtain ⟨T, hTm, hTe⟩ := hT x
    rw [Measure.map_map (measurable_const_mul _) he'c.measurable]
    have hcomp : (fun y : H => (⟨e x, x, rfl⟩ : H) * y) ∘ e' = e' ∘ T :=
      funext fun y => Subtype.ext (hTe y)
    rw [hcomp, ← Measure.map_map he'c.measurable hTm.measurable, hTm.map_eq]⟩
  have key := Measure.isMulLeftInvariant_eq_smul (ν.map e') (μ.comap H.subtype)
  set c := Measure.haarScalarFactor (ν.map e') (μ.comap H.subtype) with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply hlam0
    rw [key, h0, zero_smul]
  have hμH : μ.comap H.subtype = c⁻¹ • ν.map e' := by
    rw [key, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨c⁻¹, ?_⟩
  have hres : μ.restrict (Set.range e) = (μ.comap H.subtype).map H.subtype := by
    rw [hme.map_comap]
    congr 1
    simp [H]
    rfl
  rw [hres, hμH, Measure.map_smul, hlamval]
