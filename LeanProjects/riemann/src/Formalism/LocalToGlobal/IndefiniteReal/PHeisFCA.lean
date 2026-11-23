import Formalism.LocalToGlobal.IndefiniteReal.IsWeilDatum
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompactAdele

noncomputable section

open MeasureTheory IsDedekindDomain NumberField Topology
open scoped RestrictedProduct Classical

namespace Formalism.IndefR.PHeisFC

variable (F : Type) [Field F] [NumberField F]

abbrev eM : InfiniteAdeleRing F ≃+* mixedEmbedding.mixedSpace F := InfiniteAdeleRing.ringEquiv_mixedSpace F

theorem eM_apply (x : InfiniteAdeleRing F) :
    eM F x = ((fun v : {w : InfinitePlace F // w.IsReal} =>
        InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1)),
      fun v : {w : InfinitePlace F // w.IsComplex} => InfinitePlace.Completion.extensionEmbedding v.1 (x v.1)) :=
  InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x

theorem continuous_eM : Continuous (eM F) := by
  have h : ∀ x : InfiniteAdeleRing F, eM F x = ((fun v : {w : InfinitePlace F // w.IsReal} =>
        InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1)),
      fun v : {w : InfinitePlace F // w.IsComplex} => InfinitePlace.Completion.extensionEmbedding v.1 (x v.1)) :=
    eM_apply F
  refine Continuous.congr ?_ (fun x => (h x).symm)
  first | apply Continuous.prodMk | apply Continuous.prod_mk
  · exact continuous_pi fun v =>
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply v.1)
  · exact continuous_pi fun v =>
      (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply v.1)

def Pinf : Set (InfiniteAdeleRing F) := eM F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)

theorem eM_algebraMap (a : F) : eM F (algebraMap F (InfiniteAdeleRing F) a) = mixedEmbedding F a := by
  first
  | exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp).symm
  | exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm
  | exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (x := a)).symm

theorem inf_exU (x : InfiniteAdeleRing F) : ∃! a : 𝓞 F, algebraMap F (InfiniteAdeleRing F) (a : F) + x ∈ Pinf F := by
  have key : ∀ a : 𝓞 F, (algebraMap F (InfiniteAdeleRing F) (a : F) + x ∈ Pinf F) ↔
      mixedEmbedding F (a : F) + eM F x ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) := by
    intro a
    show eM F (algebraMap F (InfiniteAdeleRing F) (a : F) + x) ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) ↔ _
    rw [map_add, eM_algebraMap]
  have hmem : ∀ a : 𝓞 F, mixedEmbedding F (a : F) ∈
      Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) := by
    intro a
    rw [mixedEmbedding.mem_span_latticeBasis]
    exact ⟨a, rfl⟩
  obtain ⟨v, hv, hu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (mixedEmbedding.latticeBasis F) (eM F x)
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 F, mixedEmbedding F (a : F) = (v : mixedEmbedding.mixedSpace F) := by
    have hv2 := v.2
    rw [mixedEmbedding.mem_span_latticeBasis] at hv2
    obtain ⟨a, ha⟩ := hv2
    exact ⟨a, ha⟩
  refine ⟨a, ?_, ?_⟩
  · show algebraMap F (InfiniteAdeleRing F) (a : F) + x ∈ Pinf F
    rw [key, ha]
    simpa [Submodule.vadd_def] using hv
  · intro b hb0
    have hb : algebraMap F (InfiniteAdeleRing F) (b : F) + x ∈ Pinf F := hb0
    rw [key] at hb
    have h1 : (⟨mixedEmbedding F (b : F), hmem b⟩ :
        Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F))) = v := by
      apply hu
      simpa [Submodule.vadd_def] using hb
    have h2 : mixedEmbedding F (b : F) = mixedEmbedding F (a : F) := by
      rw [ha]
      exact congrArg Subtype.val h1
    have h3 : (b : F) = (a : F) := mixedEmbedding_injective F h2
    first | exact RingOfIntegers.ext h3 | exact RingOfIntegers.coe_injective h3 | exact Subtype.ext h3

theorem measurableSet_Pinf : MeasurableSet (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) :=
  ZSpan.fundamentalDomain_measurableSet _

theorem Pinf_sub_compact : ∃ K : Set (InfiniteAdeleRing F), IsCompact K ∧ Pinf F ⊆ K := by
  obtain ⟨R, hR⟩ := (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis F)).subset_closedBall 0
  refine ⟨Set.pi Set.univ (fun w => (InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 R),
    ?_, ?_⟩
  · refine isCompact_univ_pi fun w => ?_
    have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
    first
    | exact hi.isClosedEmbedding.isCompact_preimage (isCompact_closedBall 0 R)
    | exact hi.closedEmbedding.isCompact_preimage (isCompact_closedBall 0 R)
  · intro x hx
    have hx' : ‖eM F x‖ ≤ R := mem_closedBall_zero_iff.mp (hR (show eM F x ∈ _ from hx))
    show ∀ w ∈ (Set.univ : Set (InfinitePlace F)),
      x w ∈ (InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 R
    intro w _
    have hn : ‖InfinitePlace.Completion.extensionEmbedding w (x w)‖ = ‖x w‖ :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (x w)
    show InfinitePlace.Completion.extensionEmbedding w (x w) ∈ Metric.closedBall 0 R
    rw [mem_closedBall_zero_iff, hn]
    by_cases hw : w.IsReal
    · have hr : ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x w)‖ = ‖x w‖ :=
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) (x w)
      have e : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x w) = (eM F x).1 ⟨w, hw⟩ := by
        rw [eM_apply]
      rw [← hr, e]
      exact ((norm_le_pi_norm _ _).trans (norm_fst_le _)).trans hx'
    · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have e : InfinitePlace.Completion.extensionEmbedding w (x w) = (eM F x).2 ⟨w, hc⟩ := by
        rw [eM_apply]
      rw [← hn, e]
      exact ((norm_le_pi_norm _ _).trans (norm_snd_le _)).trans hx'

abbrev Ohat : Set (FiniteAdeleRing (𝓞 F) F) := (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F : Set (FiniteAdeleRing (𝓞 F) F))

theorem isOpen_Ohat : IsOpen (Ohat F) := by
  first | exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.isOpen_intAd F | exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.isOpen_intAd

theorem isCompact_Ohat : IsCompact (Ohat F) := Formalism.L2.Col.rlt_isCompact_intAd

def F0 : Set (AdeleRing (𝓞 F) F) := {x | x.1 ∈ Pinf F ∧ x.2 ∈ Ohat F}

theorem ad_exU (x : AdeleRing (𝓞 F) F) : ∃! q : F, algebraMap F (AdeleRing (𝓞 F) F) q + x ∈ F0 F := by
  have hOa : ∀ a : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := by
    intro a
    show ∀ v : HeightOneSpectrum (𝓞 F), (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v ∈ v.adicCompletionIntegers F
    intro v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v = ((a : F) : v.adicCompletion F) := rfl
    rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    first
    | exact HeightOneSpectrum.valuation_le_one v a
    | (rw [show (a : F) = algebraMap (𝓞 F) F a from rfl, HeightOneSpectrum.valuation_of_algebraMap];
       exact HeightOneSpectrum.intValuation_le_one v a)
  have hint : ∀ q : F, algebraMap F (FiniteAdeleRing (𝓞 F) F) q ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F →
      ∃ a : 𝓞 F, (a : F) = q := by
    intro q hq
    have hr := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) q (by
      intro v
      have h1 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) q) v ∈ v.adicCompletionIntegers F := hq v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
      have h2 : Valued.v ((q : v.adicCompletion F)) ≤ 1 := h1
      rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2)
    obtain ⟨a, ha⟩ := hr
    first | exact ⟨a, ha⟩ | exact ⟨a, by simpa using ha⟩
  obtain ⟨u, hu⟩ : ∃ u : F, x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) u ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := by
    first
    | exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd F x.2
    | exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2
  obtain ⟨a, ha, hauniq⟩ := inf_exU F (algebraMap F (InfiniteAdeleRing F) (-u) + x.1)
  refine ⟨-u + (a : F), ?_, ?_⟩
  · simp only [F0, Set.mem_setOf_eq]
    constructor
    · change algebraMap F (InfiniteAdeleRing F) (-u + (a : F)) + x.1 ∈ Pinf F
      have e : algebraMap F (InfiniteAdeleRing F) (-u + (a : F)) + x.1 =
          algebraMap F (InfiniteAdeleRing F) (a : F) + (algebraMap F (InfiniteAdeleRing F) (-u) + x.1) := by
        rw [map_add]; abel
      rw [e]; exact ha
    · change algebraMap F (FiniteAdeleRing (𝓞 F) F) (-u + (a : F)) + x.2 ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F
      have e : algebraMap F (FiniteAdeleRing (𝓞 F) F) (-u + (a : F)) + x.2 =
          (x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) u) + algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) := by
        rw [map_add, map_neg]; abel
      rw [e]; exact add_mem hu (hOa a)
  · intro q hq
    simp only [F0, Set.mem_setOf_eq] at hq
    obtain ⟨h1, h2⟩ := hq
    have h2' : algebraMap F (FiniteAdeleRing (𝓞 F) F) q + x.2 ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := h2
    have h1' : algebraMap F (InfiniteAdeleRing F) q + x.1 ∈ Pinf F := h1
    have h3 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (q + u) ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := by
      have h4 := sub_mem h2' hu
      have e : algebraMap F (FiniteAdeleRing (𝓞 F) F) (q + u) =
          algebraMap F (FiniteAdeleRing (𝓞 F) F) q + x.2 - (x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) u) := by
        rw [map_add]; abel
      rw [e]; exact h4
    obtain ⟨b, hb⟩ := hint (q + u) h3
    have h5 : algebraMap F (InfiniteAdeleRing F) (b : F) + (algebraMap F (InfiniteAdeleRing F) (-u) + x.1) ∈ Pinf F := by
      have e : algebraMap F (InfiniteAdeleRing F) (b : F) + (algebraMap F (InfiniteAdeleRing F) (-u) + x.1) =
          algebraMap F (InfiniteAdeleRing F) q + x.1 := by
        rw [hb, map_add, map_neg]; abel
      rw [e]; exact h1'
    have hba : b = a := hauniq b h5
    rw [hba] at hb
    rw [hb]; ring

theorem fundamental_set_subset_compact : ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧ F0 F ⊆ K := by
  obtain ⟨K1, hK1, hsub⟩ := Pinf_sub_compact F
  refine ⟨K1 ×ˢ Ohat F, hK1.prod (isCompact_Ohat F), ?_⟩
  intro x hx
  simp only [F0, Set.mem_setOf_eq] at hx
  exact ⟨hsub hx.1, hx.2⟩

instance instT2SpaceFiniteAdeles : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ (v : HeightOneSpectrum (𝓞 F)), [v.adicCompletion F, v.adicCompletionIntegers F]))

instance t2Space_numberFieldInfiniteAdeles : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

instance t2AF : T2Space (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

instance wlcAfin : WeaklyLocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) where
  exists_compact_mem_nhds x := by
    refine ⟨(fun y => x + y) '' Ohat F, (isCompact_Ohat F).image (continuous_const.add continuous_id), ?_⟩
    have ho : IsOpen ((fun y => y - x) ⁻¹' Ohat F) := (isOpen_Ohat F).preimage (continuous_id.sub continuous_const)
    refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
    · show x - x ∈ Ohat F
      rw [sub_self]; exact zero_mem (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F)
    · intro y hy
      exact ⟨y - x, hy, by simp⟩

instance lcAfin : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := WeaklyLocallyCompactSpace.locallyCompactSpace

instance lcAF : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end Formalism.IndefR.PHeisFC

end
