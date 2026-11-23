import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilModulusHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormImageNeighbourhoodEventually
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.NormFib

section Abstract

variable {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [MeasurableSpace A]
  [BorelSpace A] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B]
  [BorelSpace B] [LocallyCompactSpace B] [SecondCountableTopology B]

theorem isHaarMeasure_comap_subtype {R : Subgroup B} (ho : IsOpen (R : Set B)) (ν : Measure B)
    [ν.IsHaarMeasure] : (Measure.comap (Subtype.val : R → B) ν).IsHaarMeasure := by
  have hemb : MeasurableEmbedding (Subtype.val : R → B) :=
    MeasurableEmbedding.subtype_coe ho.measurableSet
  have hop : IsOpenMap (Subtype.val : R → B) := ho.isOpenMap_subtype_val
  exact
    { lt_top_of_isCompact := fun {K} hK => by
        rw [hemb.comap_apply]
        exact (hK.image continuous_subtype_val).measure_lt_top
      map_mul_left_eq_self := fun g => by
        refine Measure.ext fun s hs => ?_
        rw [Measure.map_apply (measurable_const_mul g) hs, hemb.comap_apply, hemb.comap_apply]
        have e : (Subtype.val : R → B) '' ((fun x => g * x) ⁻¹' s) =
            (fun x => (g : B) * x) ⁻¹' ((Subtype.val : R → B) '' s) := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact ⟨g * y, hy, rfl⟩
          · rintro ⟨z, hz, hzx⟩
            refine ⟨g⁻¹ * z, ?_, ?_⟩
            · simpa using hz
            · simp [hzx]
        rw [e]
        exact measure_preimage_mul ν (g : B) _
      open_pos := fun U hU hne => by
        rw [hemb.comap_apply]
        exact (hop U hU).measure_ne_zero ν (hne.image _) }

theorem exists_map_eq_smul_restrict (N : A →* B) (hp : IsProperMap N)
    (ho : IsOpen (N.range : Set B)) (μ : Measure A) [μ.IsHaarMeasure] (ν : Measure B)
    [ν.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ Measure.map N μ = c • ν.restrict (N.range : Set B) := by
  have hemb : MeasurableEmbedding (Subtype.val : N.range → B) :=
    MeasurableEmbedding.subtype_coe ho.measurableSet
  haveI : LocallyCompactSpace N.range := ho.locallyCompactSpace
  haveI : SecondCountableTopology N.range :=
    TopologicalSpace.Subtype.secondCountableTopology (N.range : Set B)
  have hc : Continuous N.rangeRestrict := hp.continuous.subtype_mk _
  have ht : Filter.Tendsto N.rangeRestrict (Filter.cocompact A) (Filter.cocompact N.range) := by
    refine (Filter.hasBasis_cocompact.tendsto_iff Filter.hasBasis_cocompact).2 fun K hK => ?_
    refine ⟨N ⁻¹' (Subtype.val '' K), hp.isCompact_preimage (hK.image continuous_subtype_val), ?_⟩
    intro x hx hxK
    exact hx ⟨_, hxK, rfl⟩
  haveI : (Measure.map N.rangeRestrict μ).IsHaarMeasure :=
    Measure.isHaarMeasure_map μ N.rangeRestrict hc N.rangeRestrict_surjective ht
  haveI : (Measure.comap (Subtype.val : N.range → B) ν).IsHaarMeasure :=
    isHaarMeasure_comap_subtype ho ν
  refine ⟨Measure.haarScalarFactor (Measure.map N.rangeRestrict μ)
    (Measure.comap (Subtype.val : N.range → B) ν),
    Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, ?_⟩
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map N.rangeRestrict μ)
    (Measure.comap (Subtype.val : N.range → B) ν)
  have e : Measure.map N μ = Measure.map Subtype.val (Measure.map N.rangeRestrict μ) := by
    rw [Measure.map_map measurable_subtype_coe hc.measurable]
    rfl
  rw [e]
  conv_lhs => rw [h]
  rw [Measure.map_smul, hemb.map_comap, Subtype.range_coe]

end Abstract

section Fib

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] in

theorem nfib_normUnits {f : E → ℂ}
    (hinv : ∀ (x : E) (u : Eˣ), Algebra.norm F (u : E) = 1 → f (x * u) = f x) (x : Eˣ) :
    nfib E f (normUnits F E x) = f x := by
  have h : ∃ t : Eˣ, Algebra.norm F (t : E) = (normUnits F E x : Fˣ) := ⟨x, rfl⟩
  rw [nfib, dif_pos h]
  have hs : normUnits F E h.choose = normUnits F E x := Units.ext h.choose_spec
  have hu : Algebra.norm F (((h.choose⁻¹ * x : Eˣ)) : E) = 1 := by
    have h1 : normUnits F E (h.choose⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, hs, inv_mul_cancel]
    exact congrArg Units.val h1
  have := hinv (h.choose : E) (h.choose⁻¹ * x) hu
  rw [← this, Units.val_mul, Units.mul_inv_cancel_left]

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] in

theorem nfib_eq_zero {f : E → ℂ} {a : Fˣ} (ha : a ∉ (normUnits F E).range) : nfib E f a = 0 := by
  refine dif_neg ?_
  rintro ⟨t, ht⟩
  exact ha ⟨t, Units.ext ht⟩

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E] in

theorem continuous_nfib [ValuativeExtension F E] [FiniteDimensional F E]
    (hO : IsOpen ((normUnits F E).range : Set Fˣ)) {f : E → ℂ}
    (hf : Continuous (fun x : Eˣ => f x))
    (hinv : ∀ (x : E) (u : Eˣ), Algebra.norm F (u : E) = 1 → f (x * u) = f x) :
    Continuous (nfib E f : Fˣ → ℂ) := by
  have hopen : IsOpenMap (normUnits F E) := GlobalTheory.CompanionTheory.NormLocal.isOpenMap_normUnits_of_isOpen_range hO
  have hC : IsClosed ((normUnits F E).range : Set Fˣ) := Subgroup.isClosed_of_isOpen _ hO
  refine continuous_def.2 fun S hS => isOpen_iff_mem_nhds.2 fun a ha => ?_
  by_cases hr : a ∈ (normUnits F E).range
  · obtain ⟨x, rfl⟩ := hr
    have hV : IsOpen (normUnits F E '' ((fun x : Eˣ => f x) ⁻¹' S)) := hopen _ (hS.preimage hf)
    refine Filter.mem_of_superset (hV.mem_nhds ⟨x, ?_, rfl⟩) ?_
    · have : nfib E f (normUnits F E x) ∈ S := ha
      rwa [nfib_normUnits hinv] at this
    · rintro _ ⟨y, hy, rfl⟩
      show nfib E f (normUnits F E y) ∈ S
      rwa [nfib_normUnits hinv]
  · refine Filter.mem_of_superset (hC.isOpen_compl.mem_nhds hr) fun b hb => ?_
    have h0 : (0 : ℂ) ∈ S := by
      have : nfib E f a ∈ S := ha
      rwa [nfib_eq_zero hr] at this
    show nfib E f b ∈ S
    rwa [nfib_eq_zero hb]

theorem fibProp_of_map [ValuativeExtension F E] [FiniteDimensional F E]
    (hO : IsOpen ((normUnits F E).range : Set Fˣ)) {c : ℝ≥0} (hc : 0 < c)
    (hmap : Measure.map (normUnits F E) (multHaar E) =
      c • (multHaar F).restrict ((normUnits F E).range : Set Fˣ)) :
    FibProp F E (c : ℝ) := by
  intro f hf hinv
  have hφ := continuous_nfib hO hf hinv
  have hm : Measurable (normUnits F E) := (continuous_normUnits F E).measurable
  have hcomp : (fun x : Eˣ => f x) = nfib E f ∘ normUnits F E :=
    funext fun x => (nfib_normUnits hinv x).symm
  have hsupp : Function.support (nfib E f : Fˣ → ℂ) ⊆ ((normUnits F E).range : Set Fˣ) := by
    intro a ha
    by_contra hr
    exact ha (nfib_eq_zero hr)
  constructor
  · rw [hcomp, ← integrable_map_measure hφ.aestronglyMeasurable hm.aemeasurable, hmap]
    have e : c • (multHaar F).restrict ((normUnits F E).range : Set Fˣ) =
        (c : ℝ≥0∞) • (multHaar F).restrict ((normUnits F E).range : Set Fˣ) := rfl
    rw [e, integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top]
    exact integrableOn_iff_integrable_of_support_subset hsupp
  · have e : ∫ x : Eˣ, f x ∂multHaar E = ∫ x : Eˣ, nfib E f (normUnits F E x) ∂multHaar E :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => congrFun hcomp x)
    rw [e, ← integral_map hm.aemeasurable hφ.aestronglyMeasurable, hmap,
      integral_smul_nnreal_measure,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => nfib_eq_zero ha,
      NNReal.smul_def, Complex.real_smul]

end Fib

theorem wFib : Ad3.K.GL2LocalData.WFib := by
  intro F _ _ _ _ _ _ _ χ _ _ E _ _ _ _ _ _ _ hd hc σ _ η _
  haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.NormModulus.valuativeExtension_of_continuous hc
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hd
  haveI : Fact (Module.finrank F E = 2) := ⟨hd⟩
  haveI : Algebra.IsSeparable F E := inferInstance
  have hO : IsOpen ((normUnits F E).range : Set Fˣ) :=
    GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.isOpen_range_normUnits (K := F) (E := E)
  obtain ⟨c, hc0, hmap⟩ := exists_map_eq_smul_restrict (normUnits F E)
    (isProperMap_normUnits F E) hO (multHaar E) (multHaar F)
  exact ⟨c, by exact_mod_cast hc0, fibProp_of_map hO hc0 hmap⟩

end GlobalTheory.CompanionTheory.NormFib
