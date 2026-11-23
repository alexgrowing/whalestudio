import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedCenterFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedLocusFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InactiveTotalSpaceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackUpToEmptyCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrictTransformTower
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace ChartFlatBaseChange

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  {k' : Type u} [Field k'] [CharZero k'] {Y' : Scheme.{u}} [AlgebraicGeometry.IsAffine Y']
  {pY' : Y' ⟶ Spec (CommRingCat.of k')} [AlgebraicGeometry.LocallyOfFiniteType pY']
  {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

private theorem congr_hom_apply {A B : Scheme.{u}} {f g : A ⟶ B} (e : f = g) (a : A) :
    f a = g a := by
  subst e
  rfl

@[reassoc]
theorem levelMap_succ_comp_transitionMap (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length)
    (hσ : F.reindex j ≤ F.reindex (j + 1)) :
    F.levelMap (j + 1) (Nat.succ_le_of_lt hj) ≫ S.ambientSeq.transitionMap hσ =
      S'.blowdown j ≫ F.levelMap j (le_of_lt hj) := by
  have hσ' : F.reindex j + 1 ≤ F.reindex (j + 1) := F.reindex_lt_succ j hj
  have key : S.ambientSeq.transitionMap hσ' ≫ S.blowdown (F.reindex j) = S.ambientSeq.transitionMap hσ := by
    rw [show S.blowdown (F.reindex j) = S.ambientSeq.transitionMap (Nat.le_succ (F.reindex j)) from
        S.ambientSeq.blowupMorphism_eq_transitionMap _, S.ambientSeq.transitionMap_trans]
  have hw := (F.isPullback_step j hj hσ').w
  rw [Category.assoc, key] at hw
  exact hw

@[reassoc]
theorem strictTransformComparison_succ_comp_strictTransformMapOfLE (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length)
    (hσ : F.reindex j ≤ F.reindex (j + 1)) :
    F.strictTransformComparison (j + 1) (Nat.succ_le_of_lt hj) ≫ S.strictTransformMapOfLE hσ =
      S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj) := by
  have : Mono (S.strictTransformι (F.reindex j)) := inferInstance
  rw [← cancel_mono (S.strictTransformι (F.reindex j))]
  have e1 : (F.strictTransformComparison (j + 1) (Nat.succ_le_of_lt hj) ≫ S.strictTransformMapOfLE hσ) ≫
        S.strictTransformι (F.reindex j)
      = S'.strictTransformι (j + 1) ≫ (S'.blowdown j ≫ F.levelMap j (le_of_lt hj)) := by
    rw [Category.assoc, S.strictTransformMapOfLE_strictTransformι, ← Category.assoc, F.strictTransformComparison_comp_strictTransformι,
      Category.assoc, F.levelMap_succ_comp_transitionMap j hj hσ]
  have e2 : (S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj)) ≫ S.strictTransformι (F.reindex j)
      = S'.strictTransformι (j + 1) ≫ (S'.blowdown j ≫ F.levelMap j (le_of_lt hj)) := by
    rw [Category.assoc, F.strictTransformComparison_comp_strictTransformι, ← Category.assoc, S'.strictTransformMap_comp_strictTransformι, Category.assoc]
  rw [e1, e2]

@[reassoc]
theorem inr_totalSpaceMap (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length) :
    (coprod.inr : S'.detachedCoprod j ⟶ S'.totalSpace j) ≫ F.totalSpaceMap j hj =
      F.inactiveTotalMap j hj ≫
        (coprod.inr : S.detachedCoprod (F.reindex j) ⟶ S.totalSpace (F.reindex j)) := by
  simp [ChartFlatBaseChange.totalSpaceMap]

private theorem totalTransition_comp_totalSpaceMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length)
    (hσ : F.reindex j ≤ F.reindex (j + 1)) :
    S'.totalTransition j ≫ F.totalSpaceMap j (le_of_lt hj) =
      F.totalSpaceMap (j + 1) (Nat.succ_le_of_lt hj) ≫ S.totalMapOfLE hσ := by
  apply coprod.hom_ext
  · have e1 : (coprod.inl : S'.strictTransform (j + 1) ⟶ S'.totalSpace (j + 1)) ≫
          (S'.totalTransition j ≫ F.totalSpaceMap j (le_of_lt hj))
        = S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj) ≫ coprod.inl := by
      rw [← Category.assoc, S'.inl_totalTransition, Category.assoc, F.inl_totalSpaceMap]
    have e2 : (coprod.inl : S'.strictTransform (j + 1) ⟶ S'.totalSpace (j + 1)) ≫
          (F.totalSpaceMap (j + 1) (Nat.succ_le_of_lt hj) ≫ S.totalMapOfLE hσ)
        = S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj) ≫ coprod.inl := by
      rw [← Category.assoc, F.inl_totalSpaceMap, Category.assoc, S.inl_totalMapOfLE,
        ← Category.assoc, F.strictTransformComparison_succ_comp_strictTransformMapOfLE j hj hσ, Category.assoc]
    rw [e1, e2]
  · apply S'.detachedCoprod_hom_ext (j + 1)
    intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hlt | heq
    · have h1 := F.detachedToCoprod_inr_totalSpaceMap (j + 1) (Nat.succ_le_of_lt hj) s hs
      have h4 := F.detachedToCoprod_inr_totalSpaceMap j (le_of_lt hj) s hlt
      have h2 := S.detachedToCoprod_detachedCoprodMapOfLE (F.reindex_lt_reindex hlt (le_of_lt hj)) hσ
      have h3 := S.detachedCoprodMapOfLE_inr_totalMapOfLE hσ
      have h6 := S'.detachedCoprodInl_inr_totalTransition_assoc j (F.totalSpaceMap j (le_of_lt hj))
      rw [reassoc_of% h1, ← h2]
      rw [S'.detachedToCoprod_succ_of_lt s j hlt]
      simp only [Category.assoc]
      rw [h6, h4, h3]
    · subst heq
      have h1 := F.detachedToCoprod_inr_totalSpaceMap (s + 1) (Nat.succ_le_of_lt hj) s hs
      rw [reassoc_of% h1, S.detachedToCoprod_inr_totalMapOfLE hσ (le_refl (F.reindex s))
          (F.reindex_lt_succ s hj), S.strictTransformMapOfLE_self]
      rw [S'.detachedToCoprod_self s]
      simp only [Category.id_comp]
      rw [S'.detachedCoprodInr_inr_totalTransition_assoc s (F.totalSpaceMap s (le_of_lt hj)),
        F.inl_totalSpaceMap, F.detachedSchemeComparison_comp_detachedι_assoc s hj coprod.inl]

private theorem totalCenter_eq_comap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (i : ℕ) (hi : i < S'.length) :
    S'.totalCenter i = (S.totalCenter (F.reindex i)).comap (F.totalSpaceMap i hi.le) := by
  apply FunctorialResolution.Blowup.idealSheafData_ext_coprod
  · have l1 : (S'.totalCenter i).comap
        (coprod.inl : S'.strictTransform i ⟶ S'.totalSpace i) = S'.centerOffDetached i := by
      rw [S'.totalCenter_eq, FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inl,
        Scheme.IdealSheafData.ker_subschemeι]
    have l2 : (S.totalCenter (F.reindex i)).comap
        (coprod.inl : S.strictTransform (F.reindex i) ⟶ S.totalSpace (F.reindex i))
        = S.centerOffDetached (F.reindex i) := by
      rw [S.totalCenter_eq, FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inl,
        Scheme.IdealSheafData.ker_subschemeι]
    rw [l1, ← Scheme.IdealSheafData.comap_comp, F.inl_totalSpaceMap,
      Scheme.IdealSheafData.comap_comp, l2, ← F.centerOffDetached_eq_comap i hi]
  · have r1 : (S'.totalCenter i).comap
        (coprod.inr : S'.detachedCoprod i ⟶ S'.totalSpace i) = ⊤ := by
      rw [S'.totalCenter_eq]
      exact FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inr _
    rw [r1, ← Scheme.IdealSheafData.comap_comp, F.inr_totalSpaceMap,
      Scheme.IdealSheafData.comap_comp, S.totalCenter_eq,
      FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inr]
    simp

private theorem comap_center_eq_top_of_not_mem_range_reindex (F : ChartFlatBaseChange S S') (h : S.TransitionsAreBlowups) (i : ℕ)
    (hi : i < S.length) (hskip : ∀ j, j < S'.length → F.reindex j ≠ i) :
    ((S.inducedBlowups h).center i).comap (pullback.snd F.baseMap ((S.inducedBlowups h).projectionToBase i)) = ⊤ := by
  rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_center]
  apply FunctorialResolution.Blowup.comap_eq_top_of_notMem_support
  intro x hx
  rw [S.totalCenter_eq] at hx
  have hmem : (pullback.snd F.baseMap ((S.inducedBlowups h).projectionToBase i)) x ∈
      closure (Set.range
        (⇑((S.centerOffDetached i).subschemeι ≫
          (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)))) := by
    rw [← Scheme.Hom.support_ker]
    exact hx
  have hrange : Set.range
        (⇑((S.centerOffDetached i).subschemeι ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)))
      ⊆ (⇑(coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) ''
        (↑(S.centerOffDetached i).support : Set (S.strictTransform i)) := by
    rintro y ⟨t, rfl⟩
    refine ⟨(S.centerOffDetached i).subschemeι t, ?_, (Scheme.Hom.comp_apply _ _ t).symm⟩
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Set.mem_range_self t
  have hce : Topology.IsClosedEmbedding
      (⇑(coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) :=
    AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding
      (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
  have hsupclosed : IsClosed (↑(S.centerOffDetached i).support : Set (S.strictTransform i)) :=
    (S.centerOffDetached i).support.2
  have hclosed : IsClosed ((⇑(coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) ''
      (↑(S.centerOffDetached i).support : Set (S.strictTransform i))) :=
    hce.isClosedMap _ hsupclosed
  obtain ⟨a, ha, hax⟩ := (closure_minimal hrange hclosed) hmem
  have ha2 : (S.strictTransformι i) a ∈ (↑(S.ambientCenter i).support : Set (S.schemeAt i)) :=
    S.support_centerOffDetached_subset_preimage i ha
  set b := (pullback.fst F.baseMap ((S.inducedBlowups h).projectionToBase i)) x with hb
  have hcond := congr_hom_apply (pullback.condition (f := F.baseMap)
    (g := (S.inducedBlowups h).projectionToBase i)) x
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hcond
  have hstr : ((S.inducedBlowups h).projectionToBase i) ((coprod.inl : S.strictTransform i ⟶ S.totalSpace i) a)
      = (S.strictTransformToBase i) a :=
    congr_hom_apply (FunctorialResolution.EmbeddedResolution.inl_inducedBlowups_projectionToBase S h i) a
  have hemb := congr_hom_apply F.isPullback_emb.w b
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hemb
  have hae := congr_hom_apply (S.strictTransformToBase_emb i) a
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hae
  have hcompat : F.ambientMap (S'.emb b) = (S.ambientSeq.projectionToBase i) ((S.strictTransformι i) a) := by
    rw [← hemb, ← hae, ← hstr, hax, ← hcond]
  obtain ⟨z, hz1, hz2⟩ :=
    Scheme.Pullback.exists_preimage_pullback (S'.emb b) ((S.strictTransformι i) a) hcompat
  have hcs := F.comap_center_skipped i hi (fun j hj => hskip j hj)
    (pullback F.ambientMap (S.ambientSeq.projectionToBase i))
    (pullback.snd F.ambientMap (S.ambientSeq.projectionToBase i))
    (pullback.fst F.ambientMap (S.ambientSeq.projectionToBase i))
    ((IsPullback.of_hasPullback F.ambientMap (S.ambientSeq.projectionToBase i)).flip)
  have hz0 : (pullback.snd F.ambientMap (S.ambientSeq.projectionToBase i)) z ∈
      (S.ambientCenter i).support := by
    rw [hz2]; exact ha2
  have hz : z ∈ ((S.ambientCenter i).comap
      (pullback.snd F.ambientMap (S.ambientSeq.projectionToBase i))).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hz0
  rw [hcs] at hz
  simp at hz
  exact hz

private def inducedBlowupsSchemeAtIsoPullback (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
    (i : ℕ) (hi : i ≤ (S'.inducedBlowups h').length) :
    (S'.inducedBlowups h').schemeAt i ≅ pullback F.baseMap ((S.inducedBlowups h).projectionToBase (F.reindex i)) :=
  ((F.isPullback_totalSpaceMap h h' i
    (by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi)).flip).isoPullback

private theorem inducedBlowupsIso_hom_fst (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
    (i : ℕ) (hi : i ≤ (S'.inducedBlowups h').length) :
    (F.inducedBlowupsSchemeAtIsoPullback h h' i hi).hom ≫ pullback.fst F.baseMap ((S.inducedBlowups h).projectionToBase (F.reindex i))
      = (S'.inducedBlowups h').projectionToBase i :=
  IsPullback.isoPullback_hom_fst _

private theorem inducedBlowupsIso_hom_snd (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
    (i : ℕ) (hi : i ≤ (S'.inducedBlowups h').length) :
    (F.inducedBlowupsSchemeAtIsoPullback h h' i hi).hom ≫ pullback.snd F.baseMap ((S.inducedBlowups h).projectionToBase (F.reindex i))
      = F.totalSpaceMap i (by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi) :=
  IsPullback.isoPullback_hom_snd _

theorem isPullbackUpToEmptyCenters_inducedBlowups (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y']
    (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups) :
    IsPullbackUpToEmptyCenters F.baseMap (S'.inducedBlowups h') (S.inducedBlowups h) := by
  refine ⟨F.reindex, fun i hi => F.inducedBlowupsSchemeAtIsoPullback h h' i hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi ⊢
    exact F.reindex_lt i hi
  · intro i j hj hij
    rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hj
    exact F.reindex_lt_reindex_of_lt hij hj
  · rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length, FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length]
    exact F.reindex_len
  · intro i hi hns
    have hi' : i < S.length := by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi
    have hskip : ∀ j, j < S'.length → F.reindex j ≠ i := by
      intro j hj he
      exact hns ⟨j, by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length], he⟩
    rintro ⟨x, hx⟩
    rw [F.comap_center_eq_top_of_not_mem_range_reindex h i hi' hskip] at hx
    simp at hx
    exact hx
  · intro i hi
    exact F.inducedBlowupsIso_hom_fst h h' i hi
  · intro i hi hr
    have hi' : i < S'.length := by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi
    apply pullback.hom_ext
    · rw [Category.assoc, F.inducedBlowupsIso_hom_fst, Category.assoc,
        SequenceOfBlowups.pullbackTransitionMap_comp_fst, F.inducedBlowupsIso_hom_fst,
        SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]
    · rw [Category.assoc, F.inducedBlowupsIso_hom_snd, Category.assoc,
        SequenceOfBlowups.pullbackTransitionMap_comp_snd, ← Category.assoc, F.inducedBlowupsIso_hom_snd,
        FunctorialResolution.EmbeddedResolution.inducedBlowups_blowupMorphism, FunctorialResolution.EmbeddedResolution.inducedBlowups_transitionMap]
      exact F.totalTransition_comp_totalSpaceMap i hi' hr
  · intro i hi
    have hi' : i < S'.length := by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi
    rw [F.inducedBlowupsIso_hom_snd, FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_center, FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_center]
    exact F.totalCenter_eq_comap i hi'

theorem isPullbackBlowupSequence_inducedBlowupsWithoutIso (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y']
    (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups) :
    IsPullbackBlowupSequence F.baseMap (S'.inducedBlowupsWithoutIso h') (S.inducedBlowupsWithoutIso h) :=
  (F.isPullbackUpToEmptyCenters_inducedBlowups h h').isPullbackSequenceOfBlowups_withoutIsoBlowups

end ChartFlatBaseChange

end FunctorialResolution.EmbeddedResolution

end
