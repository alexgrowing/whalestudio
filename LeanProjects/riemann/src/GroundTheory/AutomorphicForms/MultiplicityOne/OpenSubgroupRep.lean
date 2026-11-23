import Mathlib
import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract

open MeasureTheory Set Filter Topology Function

namespace GroundTheory.Automorphic

noncomputable section

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def compHom (π : UnitaryRep G H) {G' : Type*} [Group G'] [TopologicalSpace G'] (f : G' →* G)
    (hf : Continuous f) : UnitaryRep G' H :=
  ⟨π.toHom.comp f, fun v => (π.continuous_orbit v).comp hf⟩

@[simp] theorem compHom_apply (π : UnitaryRep G H) {G' : Type*} [Group G'] [TopologicalSpace G']
    (f : G' →* G) (hf : Continuous f) (g : G') : π.compHom f hf g = π (f g) := rfl

set_option linter.unusedSectionVars false

variable [IsTopologicalGroup G] [T2Space G]

open Classical in

def extendZero {L : Subgroup G} (hL : IsOpen (L : Set G)) (f : CompactlySupportedContinuousMap L ℂ) :
    CompactlySupportedContinuousMap G ℂ where
  toFun g := if h : g ∈ L then f ⟨g, h⟩ else 0
  continuous_toFun := by
    classical
    refine continuous_iff_continuousAt.2 fun g => ?_
    by_cases hg : g ∈ L
    · have he : IsOpenEmbedding ((↑) : L → G) := hL.isOpenEmbedding_subtypeVal
      have h1 : ((fun g => if h : g ∈ L then f ⟨g, h⟩ else 0) ∘ ((↑) : L → G)) = f := by
        funext x
        simp [x.2]
      have key : ContinuousAt ((fun g => if h : g ∈ L then f ⟨g, h⟩ else 0) ∘ ((↑) : L → G))
          (⟨g, hg⟩ : L) := by
        rw [h1]
        exact f.continuous.continuousAt
      exact he.continuousAt_iff.1 key
    · have hcl : IsOpen (L : Set G)ᶜ := (Subgroup.isClosed_of_isOpen L hL).isOpen_compl
      refine (continuousAt_const (y := (0 : ℂ))).congr ?_
      filter_upwards [hcl.mem_nhds hg] with x hx
      rw [dif_neg (show x ∉ L from hx)]
  hasCompactSupport' := by
    refine HasCompactSupport.intro (f.hasCompactSupport.isCompact.image continuous_subtype_val)
      fun g hg => ?_
    by_cases h : g ∈ L
    · rw [dif_pos h]
      exact image_eq_zero_of_notMem_tsupport fun ht => hg ⟨⟨g, h⟩, ht, rfl⟩
    · rw [dif_neg h]

open Classical in
theorem extendZero_apply_coe {L : Subgroup G} (hL : IsOpen (L : Set G))
    (f : CompactlySupportedContinuousMap L ℂ) (x : L) : extendZero hL f x = f x := by
  show (if h : (x : G) ∈ L then f ⟨x, h⟩ else 0) = f x
  rw [dif_pos x.2]

open Classical in
theorem extendZero_apply_of_notMem {L : Subgroup G} (hL : IsOpen (L : Set G))
    (f : CompactlySupportedContinuousMap L ℂ) {g : G} (hg : g ∉ L) : extendZero hL f g = 0 := by
  show (if h : g ∈ L then f ⟨g, h⟩ else 0) = 0
  rw [dif_neg hg]

variable [MeasurableSpace G] [BorelSpace G]

theorem isFiniteMeasureOnCompacts_comap (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {L : Subgroup G} (hL : IsOpen (L : Set G)) :
    IsFiniteMeasureOnCompacts (μ.comap ((↑) : L → G)) := by
  refine ⟨fun S hS => ?_⟩
  erw [(MeasurableEmbedding.subtype_coe hL.measurableSet).comap_apply]
  exact (hS.image continuous_subtype_val).measure_lt_top

theorem integrated_compHom_subtype (π : UnitaryRep G H) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {L : Subgroup G} (hL : IsOpen (L : Set G)) (f : CompactlySupportedContinuousMap L ℂ) :
    haveI := isFiniteMeasureOnCompacts_comap μ hL
    (π.compHom L.subtype continuous_subtype_val).integrated (μ.comap ((↑) : L → G))
        (ccToL1 (μ.comap ((↑) : L → G)) f) =
      π.integrated μ (ccToL1 μ (extendZero hL f)) := by
  have := isFiniteMeasureOnCompacts_comap μ hL
  refine ContinuousLinearMap.ext fun v => ?_
  rw [integrated_ccToL1_apply, integrated_ccToL1_apply]
  have h1 : ∫ x : L, f x • (π.compHom L.subtype continuous_subtype_val) x v
      ∂(μ.comap ((↑) : L → G)) =
      ∫ x : L, (fun g : G => extendZero hL f g • π g v) (x : G) ∂(μ.comap ((↑) : L → G)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show f x • _ = extendZero hL f x • _
    rw [extendZero_apply_coe]
    rfl
  rw [h1]
  refine (integral_subtype_comap (μ := μ) (s := (L : Set G)) hL.measurableSet
    (fun g => extendZero hL f g • π g v)).trans ?_
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_
  rw [extendZero_apply_of_notMem hL f hg, zero_smul]

theorem isCompactOperator_compHom_subtype (π : UnitaryRep G H) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {L : Subgroup G} (hL : IsOpen (L : Set G))
    (hcpt : ∀ F : CompactlySupportedContinuousMap G ℂ,
      IsCompactOperator (π.integrated μ (ccToL1 μ F)))
    (f : CompactlySupportedContinuousMap L ℂ) :
    haveI := isFiniteMeasureOnCompacts_comap μ hL
    IsCompactOperator ((π.compHom L.subtype continuous_subtype_val).integrated
      (μ.comap ((↑) : L → G)) (ccToL1 (μ.comap ((↑) : L → G)) f)) := by
  have := isFiniteMeasureOnCompacts_comap μ hL
  rw [integrated_compHom_subtype π μ hL f]
  exact hcpt _

end UnitaryRep

theorem UnitaryRep.isCompactOperator_restrict_integrated {G : Type*} [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (μ : Measure G) {V : Submodule ℂ H} [CompleteSpace V]
    (hV : IsClosed (V : Set H)) (hinv : π.IsInvariant V) (g : G →₁[μ] ℂ)
    (h : IsCompactOperator (π.integrated μ g)) :
    IsCompactOperator ((π.restrict V hinv).integrated μ g) := by
  have e := UnitaryRep.comp_integrated_of_mem_intertwiners (π.restrict V hinv) μ
    (UnitaryRep.subtypeL_mem_intertwiners π V hinv) g
  have hc : IsCompactOperator (V.subtypeL ∘L (π.restrict V hinv).integrated μ g) := by
    rw [e]
    exact h.comp_clm _
  have hmem : ∀ v, (fun v => (V.subtypeL ∘L (π.restrict V hinv).integrated μ g) v) v ∈ V :=
    fun v => ((π.restrict V hinv).integrated μ g v).2
  have hfun : (((π.restrict V hinv).integrated μ g : V →L[ℂ] V) : V → V) =
      Set.codRestrict (fun v => (V.subtypeL ∘L (π.restrict V hinv).integrated μ g) v) V hmem :=
    funext fun v => Subtype.ext rfl
  rw [hfun]
  exact hc.codRestrict hmem hV

end

end GroundTheory.Automorphic
