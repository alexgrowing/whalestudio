import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.VanishingIdealOfComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IrreducibleComponentsFlatPreimage
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedLocus
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem exists_isPullback_subschemeι_comap {X X' : Scheme.{u}} (f : X' ⟶ X)
    (I : X.IdealSheafData) :
    ∃ g : (I.comap f).subscheme ⟶ I.subscheme,
      g ≫ I.subschemeι = (I.comap f).subschemeι ≫ f ∧
        IsPullback g (I.comap f).subschemeι I.subschemeι f := by
  have hker : Scheme.Hom.ker (I.comap f).subschemeι
      = Scheme.Hom.ker (pullback.fst f I.subschemeι) :=
    (Scheme.IdealSheafData.ker_subschemeι _).trans rfl
  obtain ⟨u, hufac⟩ : ∃ u : (I.comap f).subscheme ⟶ pullback f I.subschemeι,
      u ≫ pullback.fst f I.subschemeι = (I.comap f).subschemeι :=
    ⟨IsClosedImmersion.lift _ _ hker.ge, IsClosedImmersion.lift_fac _ _ hker.ge⟩
  obtain ⟨v, hvfac⟩ : ∃ v : pullback f I.subschemeι ⟶ (I.comap f).subscheme,
      v ≫ (I.comap f).subschemeι = pullback.fst f I.subschemeι :=
    ⟨IsClosedImmersion.lift _ _ hker.le, IsClosedImmersion.lift_fac _ _ hker.le⟩
  have huv : u ≫ v = 𝟙 _ := by
    apply (cancel_mono (I.comap f).subschemeι).1
    rw [Category.assoc, hvfac, hufac, Category.id_comp]
  have hvu : v ≫ u = 𝟙 _ := by
    apply (cancel_mono (pullback.fst f I.subschemeι)).1
    rw [Category.assoc, hufac, hvfac, Category.id_comp]
  have hw : (I.comap f).subschemeι ≫ f
      = (u ≫ pullback.snd f I.subschemeι) ≫ I.subschemeι := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hufac]
  refine ⟨u ≫ pullback.snd f I.subschemeι, hw.symm, ?_⟩
  exact (IsPullback.of_iso_pullback ⟨hw⟩
    (⟨u, v, huv, hvu⟩ : (I.comap f).subscheme ≅ pullback f I.subschemeι) hufac rfl).flip

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  {k' : Type u} [Field k'] [CharZero k'] {Y' : Scheme.{u}} [AlgebraicGeometry.IsAffine Y']
  {pY' : Y' ⟶ Spec (CommRingCat.of k')} [AlgebraicGeometry.LocallyOfFiniteType pY']

namespace EmbeddedBlowupSequence

theorem noetherianSpace_strictTransform (S : EmbeddedBlowupSequence k Y pY) (i : ℕ) (hi : i ≤ S.length) :
    TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) := by
  have : AlgebraicGeometry.IsNoetherian (S.schemeAt i) := S.isNoetherian_schemeAt i hi
  exact S.noetherianSpace_strictTransform_of_noetherianSpace_schemeAt i inferInstance

theorem isReduced_strictTransform (S : EmbeddedBlowupSequence k Y pY) [AlgebraicGeometry.IsReduced Y]
    (i : ℕ) (hi : i ≤ S.length) : AlgebraicGeometry.IsReduced (S.strictTransform i) :=
  S.isReduced_strictTransform_of_isNoetherian (fun j hj => S.isNoetherian_schemeAt j hj) i hi

end EmbeddedBlowupSequence

namespace ChartFlatBaseChange

variable {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

theorem mem_support_ambientCenter_iff (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length)
    (y : ↥(S'.strictTransform j)) :
    (S'.strictTransformι j) y ∈ (↑(S'.ambientCenter j).support : Set ↥(S'.schemeAt j)) ↔
      (S.strictTransformι (F.reindex j)) ((F.strictTransformComparison j hj.le) y) ∈
        (↑(S.ambientCenter (F.reindex j)).support : Set ↥(S.schemeAt (F.reindex j))) := by
  have hcomp : (S.strictTransformι (F.reindex j)) ((F.strictTransformComparison j hj.le) y)
      = (F.levelMap j hj.le) ((S'.strictTransformι j) y) :=
    congrArg (fun f : S'.strictTransform j ⟶ S.schemeAt (F.reindex j) => f y)
      (F.strictTransformComparison_comp_strictTransformι j hj.le)
  rw [F.center_eq j hj, FunctorialResolution.EmbeddedResolution.support_comap, Set.mem_preimage, hcomp]

theorem detachedLocus_eq_preimage (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length) :
    S'.detachedLocus j =
      (fun x : ↥(S'.strictTransform j) => (F.strictTransformComparison j hj.le) x) ⁻¹'
        S.detachedLocus (F.reindex j) := by
  have := F.flat_strictTransformComparison j hj.le
  have himg := F.mem_support_ambientCenter_iff j hj
  have hclosed : IsClosed
      ((fun z : ↥(S.strictTransform (F.reindex j)) => (S.strictTransformι (F.reindex j)) z) ⁻¹'
        (↑(S.ambientCenter (F.reindex j)).support : Set ↥(S.schemeAt (F.reindex j)))) := by
    rw [← FunctorialResolution.EmbeddedResolution.support_comap]
    exact ((S.ambientCenter (F.reindex j)).comap (S.strictTransformι (F.reindex j))).support.2
  refine Set.ext fun x => ?_
  simp only [Set.mem_preimage, S'.detachedLocus_eq_sUnion j, S.detachedLocus_eq_sUnion (F.reindex j), Set.mem_sUnion]
  constructor
  · rintro ⟨C', hC', hxC'⟩
    rw [S'.mem_detachedComponents] at hC'
    obtain ⟨hirr, hsub⟩ := hC'
    refine ⟨closure ((fun z : ↥(S'.strictTransform j) => (F.strictTransformComparison j hj.le) z) '' C'), ?_, ?_⟩
    · rw [S.mem_detachedComponents]
      refine ⟨FunctorialResolution.EmbeddedResolution.closure_image_mem_irreducibleComponents_of_flat _ hirr, ?_⟩
      rw [Set.image_subset_iff]
      refine closure_minimal ?_ hclosed
      rintro _ ⟨y, hy, rfl⟩
      exact (himg y).1 (hsub ⟨y, hy, rfl⟩)
    · exact subset_closure ⟨x, hxC', rfl⟩
  · rintro ⟨C, hC, hxC⟩
    rw [S.mem_detachedComponents] at hC
    obtain ⟨hirr, hsub⟩ := hC
    obtain ⟨C', hC'irr, hxC', hcl⟩ :=
      (FunctorialResolution.EmbeddedResolution.apply_mem_irreducibleComponent_iff_of_flat (F.strictTransformComparison j hj.le) hirr x).1 hxC
    refine ⟨C', ?_, hxC'⟩
    rw [S'.mem_detachedComponents]
    refine ⟨hC'irr, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    refine (himg y).2 ?_
    have hgy : (F.strictTransformComparison j hj.le) y ∈ C := by
      rw [← hcl]
      exact subset_closure ⟨y, hy, rfl⟩
    exact hsub ⟨_, hgy, rfl⟩

theorem coe_detachedClosure_eq_preimage (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length) :
    (↑(S'.detachedClosure j) : Set ↥(S'.strictTransform j)) =
      (fun x : ↥(S'.strictTransform j) => (F.strictTransformComparison j hj.le) x) ⁻¹'
        (↑(S.detachedClosure (F.reindex j)) : Set ↥(S.strictTransform (F.reindex j))) := by
  have : TopologicalSpace.NoetherianSpace ↥(S'.strictTransform j) :=
    S'.noetherianSpace_strictTransform j hj.le
  have : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (F.reindex j)) :=
    S.noetherianSpace_strictTransform (F.reindex j) (F.reindex_le_length hj.le)
  rw [S'.detachedClosure_coe j, S.detachedClosure_coe (F.reindex j), F.detachedLocus_eq_preimage j hj]

theorem detachedIdeal_eq_comap (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    S'.detachedIdeal j = (S.detachedIdeal (F.reindex j)).comap (F.strictTransformComparison j hj.le) := by
  have : TopologicalSpace.NoetherianSpace ↥(S'.strictTransform j) :=
    S'.noetherianSpace_strictTransform j hj.le
  have : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (F.reindex j)) :=
    S.noetherianSpace_strictTransform (F.reindex j) (F.reindex_le_length hj.le)
  have := S'.isReduced_strictTransform j hj.le
  have := S.isReduced_strictTransform (F.reindex j) (F.reindex_le_length hj.le)
  have := F.flat_strictTransformComparison j hj.le
  have hS : S.detachedComponents (F.reindex j) ⊆
      irreducibleComponents ↥(S.strictTransform (F.reindex j)) :=
    fun C hC => ((S.mem_detachedComponents (F.reindex j) C).1 hC).1
  have hZ : (↑(S.detachedClosure (F.reindex j)) : Set ↥(S.strictTransform (F.reindex j)))
      = ⋃₀ S.detachedComponents (F.reindex j) := by
    rw [S.detachedClosure_coe (F.reindex j)]
    exact S.detachedLocus_eq_sUnion (F.reindex j)
  have hZ' : (↑(S'.detachedClosure j) : Set ↥(S'.strictTransform j))
      = ⇑(F.strictTransformComparison j hj.le).base ⁻¹' (⋃₀ S.detachedComponents (F.reindex j)) := by
    have h := F.coe_detachedClosure_eq_preimage j hj
    rw [S.detachedClosure_coe (F.reindex j), S.detachedLocus_eq_sUnion (F.reindex j)] at h
    exact h
  rw [S'.detachedIdeal_eq j, S.detachedIdeal_eq (F.reindex j)]
  exact (comap_vanishingIdeal_sUnion (F.strictTransformComparison j hj.le)
    (S := S.detachedComponents (F.reindex j)) (Z := S.detachedClosure (F.reindex j))
    (Z' := S'.detachedClosure j) hS hZ hZ').symm

theorem exists_isPullback_detachedScheme (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    ∃ g : S'.detachedScheme j ⟶ S.detachedScheme (F.reindex j),
      g ≫ S.detachedι (F.reindex j) = S'.detachedι j ≫ F.strictTransformComparison j hj.le ∧
        IsPullback g (S'.detachedι j) (S.detachedι (F.reindex j)) (F.strictTransformComparison j hj.le) := by
  have key : ∀ J : (S'.strictTransform j).IdealSheafData,
      J = (S.detachedIdeal (F.reindex j)).comap (F.strictTransformComparison j hj.le) →
      ∃ g : J.subscheme ⟶ (S.detachedIdeal (F.reindex j)).subscheme,
        g ≫ (S.detachedIdeal (F.reindex j)).subschemeι =
            J.subschemeι ≫ F.strictTransformComparison j hj.le ∧
          IsPullback g J.subschemeι (S.detachedIdeal (F.reindex j)).subschemeι
            (F.strictTransformComparison j hj.le) := by
    rintro J rfl
    exact exists_isPullback_subschemeι_comap _ _
  exact key (S'.detachedIdeal j) (F.detachedIdeal_eq_comap j hj)

def detachedSchemeComparison (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    S'.detachedScheme j ⟶ S.detachedScheme (F.reindex j) :=
  (F.exists_isPullback_detachedScheme j hj).choose

theorem detachedSchemeComparison_comp_detachedι (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    F.detachedSchemeComparison j hj ≫ S.detachedι (F.reindex j) =
      S'.detachedι j ≫ F.strictTransformComparison j hj.le :=
  (F.exists_isPullback_detachedScheme j hj).choose_spec.1

theorem detachedSchemeComparison_comp_detachedι_assoc (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length) {Z : Scheme.{u}}
    (h : S.strictTransform (F.reindex j) ⟶ Z) :
    F.detachedSchemeComparison j hj ≫ S.detachedι (F.reindex j) ≫ h =
      S'.detachedι j ≫ F.strictTransformComparison j hj.le ≫ h := by
  rw [← Category.assoc, F.detachedSchemeComparison_comp_detachedι j hj, Category.assoc]

theorem isPullback_detachedSchemeComparison (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    IsPullback (F.detachedSchemeComparison j hj) (S'.detachedι j) (S.detachedι (F.reindex j))
      (F.strictTransformComparison j hj.le) :=
  (F.exists_isPullback_detachedScheme j hj).choose_spec.2

theorem detachedClosureCompl_eq_preimage (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length) :
    S'.detachedClosureCompl j = (F.strictTransformComparison j hj.le) ⁻¹ᵁ (S.detachedClosureCompl (F.reindex j)) := by
  refine TopologicalSpace.Opens.ext ?_
  have h1 : (↑(S'.detachedClosureCompl j) : Set ↥(S'.strictTransform j))
      = (↑(S'.detachedClosure j) : Set ↥(S'.strictTransform j))ᶜ := S'.detachedClosureCompl_coe j
  have h2 : (↑((F.strictTransformComparison j hj.le) ⁻¹ᵁ (S.detachedClosureCompl (F.reindex j)))
        : Set ↥(S'.strictTransform j))
      = (fun x : ↥(S'.strictTransform j) => (F.strictTransformComparison j hj.le) x) ⁻¹'
        (↑(S.detachedClosureCompl (F.reindex j)) : Set ↥(S.strictTransform (F.reindex j))) := rfl
  rw [h1, h2, S.detachedClosureCompl_coe (F.reindex j), Set.preimage_compl,
    F.coe_detachedClosure_eq_preimage j hj]

theorem isEmpty_of_forall_reindex_ne (F : ChartFlatBaseChange S S') (s : ℕ) (hs : s < S.length)
    (hskip : ∀ j, j < S'.length → F.reindex j ≠ s) (P : Scheme.{u})
    (q : P ⟶ S.detachedScheme s) (p : P ⟶ S'.ambient)
    (hcomm : q ≫ S.detachedι s ≫ S.strictTransformι s ≫ S.ambientSeq.projectionToBase s = p ≫ F.ambientMap) :
    IsEmpty ↥P := by
  have : TopologicalSpace.NoetherianSpace ↥(S.strictTransform s) :=
    S.noetherianSpace_strictTransform s hs.le
  constructor
  intro x
  have hcsq : (q ≫ S.detachedι s ≫ S.strictTransformι s) ≫ S.ambientSeq.projectionToBase s = p ≫ F.ambientMap := by
    simp only [Category.assoc]
    exact hcomm
  have hpb := IsPullback.of_hasPullback (S.ambientSeq.projectionToBase s) F.ambientMap
  have hcomap := F.comap_center_skipped s hs hskip
    (pullback (S.ambientSeq.projectionToBase s) F.ambientMap)
    (pullback.fst (S.ambientSeq.projectionToBase s) F.ambientMap)
    (pullback.snd (S.ambientSeq.projectionToBase s) F.ambientMap) hpb
  have hwf : hpb.lift _ _ hcsq ≫ pullback.fst (S.ambientSeq.projectionToBase s) F.ambientMap
      = q ≫ S.detachedι s ≫ S.strictTransformι s := hpb.lift_fst _ _ hcsq
  have hpt : (pullback.fst (S.ambientSeq.projectionToBase s) F.ambientMap) ((hpb.lift _ _ hcsq) x)
      = (S.strictTransformι s) ((S.detachedι s) (q x)) :=
    congrArg (fun f : P ⟶ S.schemeAt s => f x) hwf
  have hfl : (S.detachedι s) (q x) ∈ S.detachedLocus s := by
    have h1 : (S.detachedι s) (q x) ∈ (↑(S.detachedIdeal s).support : Set ↥(S.strictTransform s)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨q x, rfl⟩
    rw [S.detachedIdeal_eq s] at h1
    have h2 := (Scheme.IdealSheafData.coe_support_vanishingIdeal (S.detachedClosure s)).le h1
    rw [S.detachedClosure_coe s] at h2
    exact h2
  have hmem : (S.strictTransformι s) ((S.detachedι s) (q x)) ∈
      (↑(S.ambientCenter s).support : Set ↥(S.schemeAt s)) :=
    S.image_detachedLocus_subset_ambientCenter_support s ⟨_, hfl, rfl⟩
  have hmem2 : (hpb.lift _ _ hcsq) x ∈ (↑((S.ambientCenter s).comap
      (pullback.fst (S.ambientSeq.projectionToBase s) F.ambientMap)).support
        : Set ↥(pullback (S.ambientSeq.projectionToBase s) F.ambientMap)) := by
    rw [FunctorialResolution.EmbeddedResolution.support_comap, Set.mem_preimage, hpt]
    exact hmem
  rw [hcomap] at hmem2
  simp at hmem2

end ChartFlatBaseChange

end FunctorialResolution.EmbeddedResolution

end
