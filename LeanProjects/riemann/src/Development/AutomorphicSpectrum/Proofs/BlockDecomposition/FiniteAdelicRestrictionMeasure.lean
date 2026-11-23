import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.GrowthHaar

theorem isHaarMeasure_map_restrict (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [MeasurableSpace (AutomorphicForm.archGroup E a)]
    [BorelSpace (AutomorphicForm.archGroup E a)] (U : Set (AdelicGLn.FiniteAdelicGL E a))
    (hUc : IsCompact U) (hU1 : U ∈ 𝓝 (1 : AdelicGLn.FiniteAdelicGL E a)) :
    ((μ.restrict ((fun h : GA E a => (AdelicGLn.prodEquiv E a h).2) ⁻¹' U)).map
      (fun h : GA E a => AutomorphicForm.archEquiv E a (AdelicGLn.prodEquiv E a h).1)).IsHaarMeasure := by
  haveI : T2Space (AdelicGLn.FiniteAdelicGL E a) := inferInstance
  haveI : T2Space (AutomorphicForm.archGroup E a) := inferInstance
  haveI : BorelSpace (GA E a) := inferInstance
  set q : GA E a → AdelicGLn.FiniteAdelicGL E a := fun h => (AdelicGLn.prodEquiv E a h).2 with hq_def
  set p : GA E a → AutomorphicForm.archGroup E a :=
    fun h => AutomorphicForm.archEquiv E a (AdelicGLn.prodEquiv E a h).1 with hp_def
  have hΦ : Continuous (AdelicGLn.prodEquiv E a) := (AdelicGLn.prodEquiv E a).continuous
  have hq : Continuous q := continuous_snd.comp hΦ
  have hp : Continuous p := (AutomorphicForm.archEquiv E a).continuous.comp (continuous_fst.comp hΦ)
  have hpm : Measurable p := hp.measurable
  have hS : MeasurableSet (q ⁻¹' U) := (hUc.isClosed.preimage hq).measurableSet
  have happly : ∀ B : Set (AutomorphicForm.archGroup E a), MeasurableSet B →
      ((μ.restrict (q ⁻¹' U)).map p) B = μ (p ⁻¹' B ∩ q ⁻¹' U) := fun B hB => by
    rw [Measure.map_apply hpm hB, Measure.restrict_apply (hpm hB)]
  have h1 : IsFiniteMeasureOnCompacts ((μ.restrict (q ⁻¹' U)).map p) := by
    refine ⟨fun K hK => ?_⟩
    rw [happly K hK.isClosed.measurableSet]
    have hK' : IsCompact ((AutomorphicForm.archEquiv E a).symm '' K) :=
      hK.image (AutomorphicForm.archEquiv E a).symm.continuous
    have hc : IsCompact (p ⁻¹' K ∩ q ⁻¹' U) := by
      have : p ⁻¹' K ∩ q ⁻¹' U = (AdelicGLn.prodEquiv E a).symm ''
          (((AutomorphicForm.archEquiv E a).symm '' K) ×ˢ U) := by
        ext h
        constructor
        · rintro ⟨hk, hu⟩
          exact ⟨AdelicGLn.prodEquiv E a h,
            ⟨⟨_, hk, (AutomorphicForm.archEquiv E a).symm_apply_apply _⟩, hu⟩,
            (AdelicGLn.prodEquiv E a).symm_apply_apply h⟩
        · rintro ⟨⟨x, y⟩, ⟨⟨k, hk, rfl⟩, hy⟩, rfl⟩
          refine ⟨?_, ?_⟩
          · simpa [hp_def] using hk
          · simpa [hq_def] using hy
      rw [this]
      exact (hK'.prod hUc).image (AdelicGLn.prodEquiv E a).symm.continuous
    exact hc.measure_lt_top
  have hpL : ∀ (s : AutomorphicForm.archGroup E a) (h : GA E a),
      p (AutomorphicForm.infEmb E a s * h) = s * p h := fun s h => by
    simp [hp_def, AutomorphicForm.prodEquiv_infEmb]
  have hqL : ∀ (s : AutomorphicForm.archGroup E a) (h : GA E a),
      q (AutomorphicForm.infEmb E a s * h) = q h := fun s h => by
    simp [hq_def, AutomorphicForm.prodEquiv_infEmb]
  have h2 : Measure.IsMulLeftInvariant ((μ.restrict (q ⁻¹' U)).map p) := by
    refine ⟨fun s => ?_⟩
    have hms : Measurable fun x : AutomorphicForm.archGroup E a => s * x :=
      (continuous_const.mul continuous_id).measurable
    ext B hB
    rw [Measure.map_apply hms hB, happly _ (hms hB), happly B hB,
      ← measure_preimage_mul μ (AutomorphicForm.infEmb E a s) (p ⁻¹' B ∩ q ⁻¹' U)]
    congr 1
    ext h
    simp only [Set.mem_inter_iff, Set.mem_preimage, hpL, hqL]
  have h3 : Measure.IsOpenPosMeasure ((μ.restrict (q ⁻¹' U)).map p) := by
    refine ⟨fun O hO ⟨s, hs⟩ => ?_⟩
    rw [happly O hO.measurableSet]
    have hV : IsOpen (p ⁻¹' O ∩ q ⁻¹' interior U) :=
      (hO.preimage hp).inter (isOpen_interior.preimage hq)
    have hne : (p ⁻¹' O ∩ q ⁻¹' interior U).Nonempty := by
      refine ⟨AutomorphicForm.infEmb E a s, ?_, ?_⟩
      · simpa [hp_def, AutomorphicForm.prodEquiv_infEmb] using hs
      · simpa [hq_def, AutomorphicForm.prodEquiv_infEmb] using mem_interior_iff_mem_nhds.2 hU1
    refine fun h0 => hV.measure_ne_zero μ hne (measure_mono_null ?_ h0)
    exact Set.inter_subset_inter_right _ (Set.preimage_mono interior_subset)
  exact { toIsFiniteMeasureOnCompacts := h1, toIsMulLeftInvariant := h2, toIsOpenPosMeasure := h3 }

end GlobalTheory.CompanionTheory.GrowthHaar
