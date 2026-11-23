import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsOpenImmersion
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.IrreducibleComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.StrictTransformAvoidance
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.ChartIsolation
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.SmoothOrderOneCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.RestrictionToOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealGeometry
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealAssignment
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationConstruction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SmoothComponentsDisjoint
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineResolutionConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineDetachedConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.GenericPointsAvoidCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedLocus
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace OpenImmersionRestriction

def chartLevelStructureMorphism (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] (pY : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) (t : ℕ) :
    (principalizationOfEmbedding k Y pY D A).schemeAt t ⟶ Spec (CommRingCat.of k) :=
  (principalizationOfEmbedding k Y pY D A).structureMorphism t

theorem chartLevelStructureMorphism_eq_structureMorphism (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] (pY : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) (t : ℕ) :
    chartLevelStructureMorphism k Y pY D A t = (principalizationOfEmbedding k Y pY D A).structureMorphism t :=
  rfl

theorem subset_detachedLocus_of_mem_detachedComponents {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : EmbeddedBlowupSequence k Y pY) (t : ℕ)
    {C : Set ↥(S.strictTransform t)} (hC : C ∈ S.detachedComponents t) :
    C ⊆ S.detachedLocus t := by
  rw [EmbeddedBlowupSequence.detachedLocus_eq_sUnion]
  exact Set.subset_sUnion_of_mem hC

theorem exists_iso_of_ker_eq {X X' W : Scheme.{u}} (f : X ⟶ W) (g : X' ⟶ W)
    [AlgebraicGeometry.IsClosedImmersion f] [AlgebraicGeometry.IsClosedImmersion g]
    (h : AlgebraicGeometry.Scheme.Hom.ker f = AlgebraicGeometry.Scheme.Hom.ker g) :
    ∃ e : X ≅ X', e.hom ≫ g = f := by
  have hgf : AlgebraicGeometry.Scheme.Hom.ker f ≤ AlgebraicGeometry.Scheme.Hom.ker g :=
    le_of_eq h
  have hfg : AlgebraicGeometry.Scheme.Hom.ker g ≤ AlgebraicGeometry.Scheme.Hom.ker f :=
    le_of_eq h.symm
  obtain ⟨ψ, hψg⟩ : ∃ ψ : X ⟶ X', ψ ≫ g = f :=
    ⟨AlgebraicGeometry.IsClosedImmersion.lift g f hfg,
      AlgebraicGeometry.IsClosedImmersion.lift_fac g f hfg⟩
  obtain ⟨φ, hφf⟩ : ∃ φ : X' ⟶ X, φ ≫ f = g :=
    ⟨AlgebraicGeometry.IsClosedImmersion.lift f g hgf,
      AlgebraicGeometry.IsClosedImmersion.lift_fac f g hgf⟩
  have : CategoryTheory.Mono f := inferInstance
  have : CategoryTheory.Mono g := inferInstance
  have h1 : ψ ≫ φ = 𝟙 X := by
    apply (CategoryTheory.cancel_mono f).1
    rw [Category.assoc, hφf, hψg, Category.id_comp]
  have h2 : φ ≫ ψ = 𝟙 X' := by
    apply (CategoryTheory.cancel_mono g).1
    rw [Category.assoc, hψg, hφf, Category.id_comp]
  exact ⟨⟨ψ, φ, h1, h2⟩, hψg⟩

theorem ker_eq_comap_ker_of_isPullback_isOpenImmersion {X₁ Y₁ U V : Scheme.{u}}
    (f : X₁ ⟶ Y₁) [AlgebraicGeometry.QuasiCompact f] (g : V ⟶ Y₁)
    [AlgebraicGeometry.IsOpenImmersion g] (f' : U ⟶ V) (g' : U ⟶ X₁)
    (H : CategoryTheory.IsPullback g' f' f g) :
    AlgebraicGeometry.Scheme.Hom.ker f' =
      (AlgebraicGeometry.Scheme.Hom.ker f).comap g := by
  have : AlgebraicGeometry.QuasiCompact f' := FunctorialResolution.EmbeddedResolution.quasiCompact_of_isPullback H
  exact FunctorialResolution.EmbeddedResolution.ker_eq_comap_ker_of_isPullback_of_flat H

private theorem smooth_of_smooth_iso_hom_comp {X X' Sc : Scheme.{u}} (e : X ≅ X') (g : X' ⟶ Sc)
    (h : AlgebraicGeometry.Smooth (e.hom ≫ g)) : AlgebraicGeometry.Smooth g := by
  have := h
  have hg : AlgebraicGeometry.Smooth (e.inv ≫ (e.hom ≫ g)) := inferInstance
  rwa [← Category.assoc, e.inv_hom_id, Category.id_comp] at hg

theorem smooth_comp_of_iso_hom_eq {A B V W Sc : Scheme.{u}} (e : A ≅ B)
    (ι₀ : A ⟶ V) (a : V ⟶ W) (g : B ⟶ W) (q : W ⟶ Sc)
    (he : e.hom ≫ g = ι₀ ≫ a)
    (h : AlgebraicGeometry.Smooth (ι₀ ≫ a ≫ q)) :
    AlgebraicGeometry.Smooth (g ≫ q) := by
  refine smooth_of_smooth_iso_hom_comp e (g ≫ q) ?_
  have key : e.hom ≫ g ≫ q = ι₀ ≫ a ≫ q := by
    rw [← Category.assoc, he, Category.assoc]
  rw [key]
  exact h

theorem radical_ker_eq_ker {W Z : Scheme.{u}} [AlgebraicGeometry.IsReduced W]
    (f : W ⟶ Z) :
    (AlgebraicGeometry.Scheme.Hom.ker f).radical = AlgebraicGeometry.Scheme.Hom.ker f := by
  have hle : (AlgebraicGeometry.Scheme.Hom.ker f).radical
      ≤ AlgebraicGeometry.Scheme.Hom.ker f := by
    show (AlgebraicGeometry.Scheme.Hom.ker f).radical ≤
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals
        (fun U : Z.affineOpens =>
          RingHom.ker (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f U.1)))
    rw [AlgebraicGeometry.Scheme.IdealSheafData.le_ofIdeals_iff]
    intro U
    have h1 : (AlgebraicGeometry.Scheme.Hom.ker f).ideal U ≤
        RingHom.ker (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f U.1)) :=
      AlgebraicGeometry.Scheme.IdealSheafData.ideal_ofIdeals_le _ U
    refine le_trans (Ideal.radical_mono h1) ?_
    exact Ideal.isRadical_bot.comap _
  exact le_antisymm hle (AlgebraicGeometry.Scheme.IdealSheafData.le_radical _)

theorem nonzeroOnComponents_ideal {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {E : List X.IdealSheafData}
    (s : FunctorialResolution.EmbeddedResolution.IdealBlowupSequence p I E) (hI : FunctorialResolution.EmbeddedResolution.NonzeroOnComponents I) :
    ∀ i : ℕ, i ≤ s.toSequenceOfBlowups.length → FunctorialResolution.EmbeddedResolution.NonzeroOnComponents (s.ideal i) := by
  intro i
  induction i with
  | zero =>
    intro _
    have h0 : s.ideal 0 = I.comap s.toSequenceOfBlowups.isoZero.hom := by
      rw [s.ideal_zero, FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_zero]
    rw [h0]
    exact FunctorialResolution.EmbeddedResolution.nonzeroOnComponents_comap_iso_hom s.toSequenceOfBlowups.isoZero I hI
  | succ i ih =>
    intro hi
    have hi' : i < s.toSequenceOfBlowups.length := hi
    have htr : (s.toSequenceOfBlowups.center i).comap (s.toSequenceOfBlowups.transitionMapSucc i) ^ 1 * s.ideal (i + 1)
        = (s.ideal i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := by
      have h2 := s.ideal_succ i hi'
      rw [FunctorialResolution.Blowup.exceptionalIdeal_eq_comap] at h2
      rw [pow_one]
      exact h2
    exact FunctorialResolution.EmbeddedResolution.nonzeroOnComponents_of_pow_mul_eq_comap FunctorialResolution.EmbeddedResolution.effectiveCartierSupportContainsNoComponent
      (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)
      (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism i hi') 1 (s.ideal i) (s.ideal (i + 1)) htr
      (ih (Nat.le_of_succ_le hi))

theorem false_of_mem_support_center {k : Type u} [Field k] [CharZero k] {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (hp : AlgebraicGeometry.Smooth p)
    (I Z : W.IdealSheafData) (Mem : Set ↥W)
    (hcert : FunctorialResolution.EmbeddedResolution.PrincipalizationCertificate W p I 1 Mem Z)
    (T : Set ↥W) (hTcl : IsClosed T) (hTirr : IsIrreducible T)
    (ξ x : ↥W) (hξ : IsGenericPoint ξ T) (hx : x ∈ T)
    (hsmT : AlgebraicGeometry.Smooth
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨T, hTcl⟩ : TopologicalSpace.Closeds ↥W)).subschemeι ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ T)
    (hxi : ξ ∉ (Z.support : Set ↥W))
    (hdisj : Disjoint T Mem)
    (hagree : ∀ z ∈ T, AgreeNear I
      (Scheme.IdealSheafData.vanishingIdeal (⟨T, hTcl⟩ : TopologicalSpace.Closeds ↥W)) z)
    (hpt : x ∈ (Z.support : Set ↥W)) : False := by
  have hIso := smoothOrderOneCentersIsolated_vanishingIdealAssignment_of_principalizationCertificate
    (hcert.comap_of_isOpenImmersion (⊤ : W.Opens).ι)
  refine false_of_smoothOrderOneCentersIsolated_opens idealSheafGeometryHypotheses_vanishingIdealAssignment smoothVanishingHypotheses_vanishingIdealAssignment p I Z 1 Mem
    ⟨T, ξ, x, hTcl, hTirr, hξ, hx⟩ ⊤ ?_ hIso hp rfl ?_ hcomp hxi hdisj ?_ hpt
  · simp
  · rw [vanishingIdealAssignment_apply]
    exact hsmT
  · intro z hz
    rw [vanishingIdealAssignment_apply]
    exact hagree z hz

private theorem smooth_strictTransformι_comp_schemeAtToSpec_zero {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    (S : EmbeddedBlowupSequence k Y pY) (hsm : AlgebraicGeometry.Smooth pY) :
    AlgebraicGeometry.Smooth (S.strictTransformι 0 ≫ S.schemeAtToSpec 0) := by
  have : AlgebraicGeometry.Smooth pY := hsm
  have hker : AlgebraicGeometry.Scheme.Hom.ker (S.strictTransformι 0)
      = AlgebraicGeometry.Scheme.Hom.ker (S.emb ≫ S.ambientSeq.isoZero.inv) := by
    rw [EmbeddedBlowupSequence.strictTransformι_eq_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      EmbeddedBlowupSequence.strictTransformIdeal_zero]
  obtain ⟨e, he⟩ :=
    exists_iso_of_ker_eq (S.strictTransformι 0) (S.emb ≫ S.ambientSeq.isoZero.inv) hker
  have hstruct : S.ambientSeq.isoZero.inv ≫ S.schemeAtToSpec 0 = S.ambientStruct := by
    rw [EmbeddedBlowupSequence.schemeAtToSpec_eq, FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_zero,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have key : e.hom ≫ pY = S.strictTransformι 0 ≫ S.schemeAtToSpec 0 := by
    rw [← he]
    simp only [Category.assoc]
    rw [hstruct, S.emb_comp]
  rw [← key]
  infer_instance

private theorem smooth_strictTransformι_comp_schemeAtToSpec_succ {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    (S : EmbeddedBlowupSequence k Y pY)
    (hN : ∀ j ≤ S.length, AlgebraicGeometry.IsNoetherian (S.schemeAt j))
    (i : ℕ) (hi' : i < S.length)
    (ih' : AlgebraicGeometry.Smooth (S.strictTransformι i ≫ S.schemeAtToSpec i))
    (hcl : ∀ y : ↥(S.strictTransform (i + 1)),
      (S.blowdown i).base ((S.strictTransformι (i + 1)).base y) ∉
        ((S.ambientCenter i).support : Set ↥(S.schemeAt i))) :
    AlgebraicGeometry.Smooth (S.strictTransformι (i + 1) ≫ S.schemeAtToSpec (i + 1)) := by
  have := ih'
  have hredi : AlgebraicGeometry.IsReduced (S.strictTransform i) :=
    EmbeddedBlowupSequence.isReduced_strictTransform_of_isNoetherian S hN i (Nat.le_of_lt hi')
  have hredi1 : AlgebraicGeometry.IsReduced (S.strictTransform (i + 1)) :=
    EmbeddedBlowupSequence.isReduced_strictTransform_of_isNoetherian S hN (i + 1) hi'
  set U : (S.schemeAt (i + 1)).Opens :=
    (TopologicalSpace.Opens.map (S.blowdown i).base).obj (S.ambientCenterSupportCompl i) with _hU
  have hUsub : (U : Set ↥(S.schemeAt (i + 1))) ⊆
      ⇑(S.blowdown i).base ⁻¹'
        ((S.ambientCenterSupportCompl i : (S.schemeAt i).Opens) : Set ↥(S.schemeAt i)) := fun _ hx => hx
  have hgi : AlgebraicGeometry.IsOpenImmersion (U.ι ≫ S.blowdown i) :=
    EmbeddedBlowupSequence.isOpenImmersion_ι_comp_blowdown S i hi' U hUsub
  have hrangeA : Set.range ⇑(S.strictTransformι (i + 1)).base ⊆ Set.range ⇑U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro z ⟨y, rfl⟩
    exact (S.mem_ambientCenterSupportCompl i _).mpr (hcl y)
  set j := AlgebraicGeometry.IsOpenImmersion.lift U.ι (S.strictTransformι (i + 1)) hrangeA with _hjdef
  have hj : j ≫ U.ι = S.strictTransformι (i + 1) :=
    AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have hjc : AlgebraicGeometry.IsClosedImmersion (j ≫ U.ι) := by
    rw [hj]; infer_instance
  have : AlgebraicGeometry.IsClosedImmersion j :=
    AlgebraicGeometry.IsClosedImmersion.of_comp j U.ι
  have hbase : ∀ y : ↥(S.strictTransform (i + 1)),
      U.ι.base (j.base y) = (S.strictTransformι (i + 1)).base y := by
    intro y
    rw [show U.ι.base (j.base y) = (j ≫ U.ι).base y from rfl, hj]
  have hkeymap : ∀ y : ↥(S.strictTransform (i + 1)),
      (S.blowdown i).base ((S.strictTransformι (i + 1)).base y)
        = (S.strictTransformι i).base ((S.strictTransformMap i).base y) := by
    intro y
    have h : (S.strictTransformMap i ≫ S.strictTransformι i).base y
        = (S.strictTransformι (i + 1) ≫ S.blowdown i).base y := by
      rw [S.strictTransformMap_comp_strictTransformι i]
    exact h.symm
  set pre : Set ↥(U.toScheme) := ⇑(U.ι ≫ S.blowdown i).base ⁻¹'
      (((S.strictTransformIdeal i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
        Set ↥(S.schemeAt i)) with hpre
  have hsuppcl : IsClosed pre := by
    rw [hpre]
    exact (S.strictTransformIdeal i).support.2.preimage
      (U.ι ≫ S.blowdown i).base.hom.continuous
  have hker_eq : S.strictTransformIdeal i = AlgebraicGeometry.Scheme.Hom.ker (S.strictTransformι i) := by
    rw [EmbeddedBlowupSequence.strictTransformι_eq_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
  have h1 : Scheme.IdealSheafData.vanishingIdeal
      ((S.strictTransformIdeal i).support) = S.strictTransformIdeal i := by
    rw [Scheme.IdealSheafData.vanishingIdeal_support, hker_eq]
    exact radical_ker_eq_ker (S.strictTransformι i)
  have hKvan : (S.strictTransformIdeal i).comap (U.ι ≫ S.blowdown i)
      = Scheme.IdealSheafData.vanishingIdeal
          (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme)) := by
    calc (S.strictTransformIdeal i).comap (U.ι ≫ S.blowdown i)
        = (Scheme.IdealSheafData.vanishingIdeal
            ((S.strictTransformIdeal i).support)).comap (U.ι ≫ S.blowdown i) := by rw [h1]
      _ = Scheme.IdealSheafData.vanishingIdeal
            (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme)) :=
          comap_vanishingIdeal_of_isOpenImmersion (U.ι ≫ S.blowdown i) _ _ rfl
  have hrange1 : Set.range ⇑j.base = pre := by
    rw [hpre]
    ext z
    simp only [Set.mem_range, Set.mem_preimage]
    constructor
    · rintro ⟨y, rfl⟩
      rw [show (U.ι ≫ S.blowdown i).base (j.base y)
          = (S.blowdown i).base (U.ι.base (j.base y)) from rfl, hbase y, hkeymap y,
        ← Scheme.IdealSheafData.range_subschemeι (S.strictTransformIdeal i)]
      exact ⟨(S.strictTransformMap i).base y, rfl⟩
    · intro hz
      have hzU : U.ι.base z ∈ ((U : (S.schemeAt (i + 1)).Opens) :
          Set ↥(S.schemeAt (i + 1))) := by
        rw [← Scheme.Opens.range_ι U]
        exact ⟨z, rfl⟩
      have hnc : (S.blowdown i).base (U.ι.base z) ∉
          (((S.ambientCenter i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
            Set ↥(S.schemeAt i)) :=
        (S.mem_ambientCenterSupportCompl i _).mp (hUsub hzU)
      have hin : (S.blowdown i).base (U.ι.base z) ∈
          (((S.strictTransformIdeal i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
            Set ↥(S.schemeAt i)) := hz
      have hrr : Set.range ⇑(S.strictTransformι (i + 1)).base
          = closure (⇑(S.blowdown i).base ⁻¹'
              ((((S.strictTransformIdeal i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
                  Set ↥(S.schemeAt i)) \
                (((S.ambientCenter i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
                  Set ↥(S.schemeAt i)))) :=
        EmbeddedBlowupSequence.range_strictTransformι_succ S hN i hi'
      have hx : U.ι.base z ∈ Set.range ⇑(S.strictTransformι (i + 1)).base := by
        rw [hrr]
        exact subset_closure ⟨hin, hnc⟩
      obtain ⟨w, hw⟩ := hx
      refine ⟨w, ?_⟩
      apply U.ι.isOpenEmbedding.injective
      rw [hbase w, hw]
  have hrange2 : Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal
      (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subschemeι.base
        = pre := by
    rw [FunctorialResolution.EmbeddedResolution.range_base_subschemeι,
      AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : AlgebraicGeometry.IsReduced
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subscheme :=
    AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _ _
  obtain ⟨e, he⟩ := FunctorialResolution.EmbeddedResolution.exists_iso_of_range_base_eq j
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subschemeι
    (hrange1.trans hrange2.symm)
  have ihsub : AlgebraicGeometry.Smooth
      ((S.strictTransformIdeal i).subschemeι ≫ S.schemeAtToSpec i) := by
    rw [← EmbeddedBlowupSequence.strictTransformι_eq_subschemeι]
    exact ih'
  have hsm2 := smooth_comap_subschemeι_of_isOpenImmersion
    (U.ι ≫ S.blowdown i) (S.strictTransformIdeal i) (S.schemeAtToSpec i) ihsub
  rw [hKvan] at hsm2
  have hlev : S.blowdown i ≫ S.schemeAtToSpec i = S.schemeAtToSpec (i + 1) := by
    rw [EmbeddedBlowupSequence.schemeAtToSpec_eq, EmbeddedBlowupSequence.schemeAtToSpec_eq, ← Category.assoc,
      ← FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_succ]
  have hgoal : S.strictTransformι (i + 1) ≫ S.schemeAtToSpec (i + 1)
      = e.hom ≫ ((Scheme.IdealSheafData.vanishingIdeal
          (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subschemeι
          ≫ ((U.ι ≫ S.blowdown i) ≫ S.schemeAtToSpec i)) := by
    rw [← hj, ← hlev, ← he]
    simp only [Category.assoc]
  rw [hgoal]
  have := hsm2
  infer_instance

private theorem agreeNear_vanishingIdeal_image_of_avoidsCenters_le_of_disjoint_zero
    {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u})
    (hDisj0 : ∀ C₁ C₂ : Set ↥((D.toEmbeddedBlowupSequence A).strictTransform 0),
      C₁ ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) →
      C₂ ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) →
      C₁ ≠ C₂ → Disjoint C₁ C₂) :
    ∀ (t : ℕ),
      (∀ s, s ≤ t → ∀ y : ↥((D.toEmbeddedBlowupSequence A).strictTransform s),
        (D.toEmbeddedBlowupSequence A).AvoidsCenters s (((D.toEmbeddedBlowupSequence A).strictTransformι s).base y)) →
      t ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C : Set ↥((D.toEmbeddedBlowupSequence A).strictTransform t),
        C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform t) →
        ∀ hCcl : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C),
        ∀ x : ↥((D.toEmbeddedBlowupSequence A).schemeAt t),
          x ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C →
          AgreeNear ((principalizationOfEmbedding k Y pY D A).ideal t)
            (Scheme.IdealSheafData.vanishingIdeal
              (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C, hCcl⟩ :
                TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt t))) x := by
  intro t
  induction t with
  | zero =>
    intro _ _ C hC hCcl x hx
    classical
    have hNoeth : TopologicalSpace.NoetherianSpace ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) :=
      (D.toEmbeddedBlowupSequence A).noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) 0
        (Nat.zero_le _)
    have hemb := (D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι 0
    have hclr : IsClosed (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base) := hemb.isClosed_range
    have hid0 := principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal D A hclr
    obtain ⟨Bad, hBaddef⟩ : ∃ B : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt 0),
        B = ⋃ C'' ∈ (irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) \ {C}),
          ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C'' := ⟨_, rfl⟩
    have hfin : (irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) \ {C}).Finite :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.sdiff_subset
    have hBadcl : IsClosed Bad := by
      rw [hBaddef]
      exact hfin.isClosed_biUnion fun C'' hC'' =>
        hemb.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ hC''.1)
    have hxU : x ∈ Badᶜ := by
      intro hmem
      rw [hBaddef] at hmem
      obtain ⟨C'', hC''D, hxim⟩ := Set.mem_iUnion₂.mp hmem
      obtain ⟨z, hzC'', hz⟩ := hxim
      obtain ⟨w, hwC, hw⟩ := hx
      have hzw : z = w := hemb.injective (hz.trans hw.symm)
      rw [hzw] at hzC''
      have hne : C'' ≠ C := fun h => hC''D.2 (Set.mem_singleton_iff.mpr h)
      exact Set.disjoint_left.mp (hDisj0 C'' C hC''D.1 hC hne) hzC'' hwC
    have hinter : (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base) ∩ Badᶜ
        = (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C) ∩ Badᶜ := by
      ext z
      constructor
      · rintro ⟨⟨w, rfl⟩, hz⟩
        refine ⟨?_, hz⟩
        by_cases hw : w ∈ C
        · exact ⟨w, hw, rfl⟩
        · refine absurd ?_ hz
          rw [hBaddef]
          refine Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents w, ?_⟩
            ⟨w, mem_irreducibleComponent, rfl⟩
          intro h
          exact hw (h ▸ mem_irreducibleComponent)
      · rintro ⟨⟨w, hwC, rfl⟩, hz⟩
        exact ⟨⟨w, rfl⟩, hz⟩
    rw [hid0]
    exact agreeNear_vanishingIdeal_of_inter_eq _ _ ⟨Badᶜ, hBadcl.isOpen_compl⟩ _ hxU hinter
  | succ i ih =>
    intro hcl hi C hC hCcl x hx
    classical
    have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D A
    have hi' : i < (D.toEmbeddedBlowupSequence A).length := Nat.lt_of_succ_le hi
    have hilt : i < (principalizationOfEmbedding k Y pY D A).length := hi'
    obtain ⟨η, hηgen⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents _ hC)
    obtain ⟨C', hC'm, hη', _⟩ :=
      (D.toEmbeddedBlowupSequence A).exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi' C hC η hηgen
    have hC'cl : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C') :=
      ((D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι i).isClosedMap _
        (isClosed_of_mem_irreducibleComponents _ hC'm)
    obtain ⟨y, hyC, hxy⟩ := hx
    have hclx : (D.toEmbeddedBlowupSequence A).AvoidsCenters (i + 1) x := by
      rw [← hxy]
      exact hcl (i + 1) le_rfl y
    have hnot := (((D.toEmbeddedBlowupSequence A).avoidsCenters_succ_iff i x).mp hclx).1
    have hblow : ((D.toEmbeddedBlowupSequence A).blowdown i).base x ∈
        ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' :=
      EmbeddedBlowupSequence.mem_image_strictTransformι_of_mem_image_succ (D.toEmbeddedBlowupSequence A) i C η hηgen
        C' hη' x ⟨y, hyC, hxy⟩
    obtain ⟨V, hxV, hVeq⟩ := (agreeNear_iff _ _ _).mp
      (ih (fun s hs => hcl s (le_trans hs (Nat.le_succ i))) (Nat.le_of_succ_le hi)
        C' hC'm hC'cl _ hblow)
    obtain ⟨V', hV'⟩ : ∃ V' : ((D.toEmbeddedBlowupSequence A).schemeAt i).Opens, V' = V := ⟨V, rfl⟩
    have hxV' : ((D.toEmbeddedBlowupSequence A).blowdown i).base x ∈ V' := by
      rw [hV']; exact hxV
    have hV'eq : ((principalizationOfEmbedding k Y pY D A).ideal i).comap V'.ι
        = (Scheme.IdealSheafData.vanishingIdeal
            (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
              TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap V'.ι := by
      rw [hV']; exact hVeq
    obtain ⟨U, hUdef⟩ : ∃ U : ((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)).Opens,
        U = (TopologicalSpace.Opens.map ((D.toEmbeddedBlowupSequence A).blowdown i).base).obj
          (V' ⊓ (D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i) := ⟨_, rfl⟩
    have hUsub : (U : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1))) ⊆
        ⇑((D.toEmbeddedBlowupSequence A).blowdown i).base ⁻¹'
          (((D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i : ((D.toEmbeddedBlowupSequence A).schemeAt i).Opens) :
            Set ↥((D.toEmbeddedBlowupSequence A).schemeAt i)) := by
      rw [hUdef]
      intro z hz
      exact hz.2
    have hmemU : ∀ z : ↥U, ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z) ∉
        (((D.toEmbeddedBlowupSequence A).ambientCenter i).support :
          Set ↥((D.toEmbeddedBlowupSequence A).schemeAt i)) := by
      intro z
      exact hUsub z.2
    have hxU : x ∈ U := by
      rw [hUdef]
      exact ⟨hxV', ((D.toEmbeddedBlowupSequence A).mem_ambientCenterSupportCompl i _).mpr hnot⟩
    have : AlgebraicGeometry.IsOpenImmersion (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
      EmbeddedBlowupSequence.isOpenImmersion_ι_comp_blowdown (D.toEmbeddedBlowupSequence A) i hi' U hUsub
    have hexc : ((principalizationOfEmbedding k Y pY D A).exceptionalIdeal i).comap U.ι = ⊤ := by
      refine FunctorialResolution.EmbeddedResolution.comap_ι_eq_top_of_disjoint _ _ ?_
      rw [Set.disjoint_left]
      intro z hz hmem
      rw [(principalizationOfEmbedding k Y pY D A).exceptionalIdeal_eq i] at hmem
      exact absurd (mem_support_of_mem_support_comap
        ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i) _ z hmem) (hUsub hz)
    have hJ : ((principalizationOfEmbedding k Y pY D A).ideal (i + 1)).comap U.ι
        = ((principalizationOfEmbedding k Y pY D A).ideal i).comap
            (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
      comap_eq_comap_comp_of_mul_eq _ U _ _ _
        ((principalizationOfEmbedding k Y pY D A).ideal_succ i hilt) hexc
    have hle : U ≤ (TopologicalSpace.Opens.map
        ((D.toEmbeddedBlowupSequence A).blowdown i).base).obj V' := by
      rw [hUdef]
      intro z hz
      exact hz.1
    have hcomapφ : ((principalizationOfEmbedding k Y pY D A).ideal i).comap
          (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i)
        = (Scheme.IdealSheafData.vanishingIdeal
            (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
              TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap
            (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
      AlgebraicGeometry.Scheme.IdealSheafData.comap_ι_comp_eq_of_comap_ι_eq
        ((D.toEmbeddedBlowupSequence A).blowdown i) V' U hle _ _ hV'eq
    have hLHS : (Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
            TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap
          (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i)
        = Scheme.IdealSheafData.vanishingIdeal
            (FunctorialResolution.EmbeddedResolution.closedPreimage U.ι
              (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C, hCcl⟩ :
                TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)))) := by
      refine FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq
        (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) _ _ ?_
      ext z
      have hcb : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base z
          = ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z) := rfl
      have hiff := EmbeddedBlowupSequence.mem_image_strictTransformι_iff_of_notMem_ambientCenter
        (D.toEmbeddedBlowupSequence A) hN i hi' C η hηgen C' hη' (U.ι.base z) (hmemU z)
      constructor
      · intro hz
        have hz1 : U.ι.base z ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C := hz
        have hz2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z)
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := hiff.mpr hz1
        have hz3 : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base z
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := by
          rw [hcb]; exact hz2
        exact hz3
      · intro hz
        have hz1 : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base z
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := hz
        have hz2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z)
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := by
          rw [← hcb]; exact hz1
        exact hiff.mp hz2
    refine (agreeNear_iff _ _ _).mpr ⟨U, hxU, ?_⟩
    exact hJ.trans (hcomapφ.trans (hLHS.trans
      (FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion U.ι
        (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C, hCcl⟩ :
          TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)))).symm))

private theorem smooth_vanishingIdeal_image_of_smooth_strictTransformι
    {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u})
    (t : ℕ) (ht : t ≤ (D.toEmbeddedBlowupSequence A).length)
    (hsmq : AlgebraicGeometry.Smooth
      ((D.toEmbeddedBlowupSequence A).strictTransformι t ≫ chartLevelStructureMorphism k Y pY D A t))
    (C : Set ↥((D.toEmbeddedBlowupSequence A).strictTransform t))
    (hC : C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform t))
    (hCcl : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C)) :
    AlgebraicGeometry.Smooth
      ((Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C, hCcl⟩ :
            TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt t))).subschemeι ≫
        chartLevelStructureMorphism k Y pY D A t) := by
  have := hsmq
  have hPlevel : (D.toEmbeddedBlowupSequence A).schemeAtToSpec t = chartLevelStructureMorphism k Y pY D A t := rfl
  have hftq : AlgebraicGeometry.LocallyOfFiniteType
      ((D.toEmbeddedBlowupSequence A).strictTransformι t ≫ chartLevelStructureMorphism k Y pY D A t) := by
    have h1 := (D.toEmbeddedBlowupSequence A).locallyOfFiniteType_strictTransformToSpec t ht
    rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.strictTransformToSpec_eq, hPlevel] at h1
    exact h1
  have hclopen : IsClopen C :=
    FunctorialResolution.EmbeddedResolution.isClopen_of_mem_irreducibleComponents_of_smooth
      ((D.toEmbeddedBlowupSequence A).strictTransformι t ≫ chartLevelStructureMorphism k Y pY D A t) C hC
  have hsub := FunctorialResolution.EmbeddedResolution.smooth_subschemeι_vanishingIdeal_comp_of_isClopen
      ((D.toEmbeddedBlowupSequence A).strictTransformι t ≫ chartLevelStructureMorphism k Y pY D A t) C hclopen
  have : AlgebraicGeometry.IsReduced
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨C, hclopen.isClosed⟩ :
          TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).strictTransform t))).subscheme :=
    AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _ _
  have : AlgebraicGeometry.IsReduced
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C, hCcl⟩ :
          TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt t))).subscheme :=
    AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _ _
  have hrange :
      Set.range ⇑((Scheme.IdealSheafData.vanishingIdeal
            (⟨C, hclopen.isClosed⟩ :
              TopologicalSpace.Closeds
                ↥((D.toEmbeddedBlowupSequence A).strictTransform t))).subschemeι ≫
          (D.toEmbeddedBlowupSequence A).strictTransformι t).base
        = Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal
            (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C, hCcl⟩ :
              TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt t))).subschemeι.base := by
    rw [Scheme.Hom.range_comp_base, FunctorialResolution.EmbeddedResolution.range_base_subschemeι,
      FunctorialResolution.EmbeddedResolution.range_base_subschemeι,
      AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal,
      AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨e, he⟩ := FunctorialResolution.EmbeddedResolution.exists_iso_of_range_base_eq _ _ hrange
  exact smooth_comp_of_iso_hom_eq e _ _ _ _ he hsub

private theorem notMem_ambientCenter_support_of_notMem_detachedComponents
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY)
    (t : ℕ) (ht : t < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    (hsmq : AlgebraicGeometry.Smooth
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t))
    (hcl : ∀ s, s ≤ t →
      ∀ y : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform s),
      (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).AvoidsCenters s
        (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι s).base y))
    (hDisj0 : ∀ C₁ C₂ :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0),
      C₁ ∈ irreducibleComponents
        ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0) →
      C₂ ∈ irreducibleComponents
        ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0) →
      C₁ ≠ C₂ → Disjoint C₁ C₂)
    (C : Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hC : C ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hfr : C ∉ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedComponents t)
    (z : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t)) (hz : z ∈ C) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base z ∉
      (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t).support :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t)) := by
  classical
  intro hmem
  have hemb := (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).isClosedEmbedding_strictTransformι t
  have hCcl : IsClosed
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C) :=
    hemb.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ hC)
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents _ hC)
  have hagree := agreeNear_vanishingIdeal_image_of_avoidsCenters_le_of_disjoint_zero D (canonicalPrincipalization hres hrad) hDisj0 t hcl
    (le_of_lt ht) C hC hCcl
  have hsmV := smooth_vanishingIdeal_image_of_smooth_strictTransformι D
    (canonicalPrincipalization hres hrad) t (le_of_lt ht) hsmq C hC hCcl
  have hsmp : AlgebraicGeometry.Smooth
      (chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) := by
    rw [chartLevelStructureMorphism_eq_structureMorphism]
    exact IdealBlowupSequence.smooth_structureMorphism
      (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)) t (le_of_lt ht)
  have hspec := (PrincipalizationRules.isMaxOrderReduction_outputLevelData (canonicalAlgorithmRules hres) hB
      (krullDimSucc D.ambient)).cert
      (markedTripleOrderOne k D.ambient D.ambientStruct (AlgebraicGeometry.Scheme.Hom.ker D.emb) [])
      (markedTripleOrderOne_isAdmissible k D.ambient D.ambientStruct
        (AlgebraicGeometry.Scheme.Hom.ker D.emb) D.nonzeroOnComponents_ker [] D.sncEmpty)
      (le_of_eq (markedTripleOrderOne_dim k D.ambient D.ambientStruct
        (AlgebraicGeometry.Scheme.Hom.ker D.emb) []))
      t ht
  have hcert : FunctorialResolution.EmbeddedResolution.PrincipalizationCertificate
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t)
      (chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t)
      ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t) 1
      (⋃ E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary t,
        (E.support :
          Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t)))
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t) := hspec
  have hgen : IsGenericPoint
      (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base η)
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C) :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding hemb hη
  have hirr : IsIrreducible
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C) :=
    hC.1.image _ hemb.continuous.continuousOn
  have hIsupp :
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C) ⊆
      ((((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t).support) :
        Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t)) := by
    refine subset_support_of_agreeNear idealSheafGeometryHypotheses_vanishingIdealAssignment _ _ _ hCcl ?_
    intro x hx
    rw [vanishingIdealAssignment_apply]
    exact hagree x hx
  have hnz : FunctorialResolution.EmbeddedResolution.NonzeroOnComponents
      ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t) :=
    nonzeroOnComponents_ideal (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad))
      D.nonzeroOnComponents_ker t (le_of_lt ht)
  have hcomp : ∀ E ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t),
      ¬ E ⊆ (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C) := by
    intro E hE hEsub
    exact (FunctorialResolution.EmbeddedResolution.nonzeroOnComponents_iff _).1 hnz E hE (hEsub.trans hIsupp)
  have hxi : ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base η ∉
      ((((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t).support) :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t)) :=
    (D.toEmbeddedBlowupSequence
      (canonicalPrincipalization hres hrad)).notMem_ambientCenter_support_of_isGenericPoint t
      C hC hfr η hη
  have hdisj : Disjoint
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C)
      (⋃ E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary t,
        (E.support :
          Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t))) := by
    rw [Set.disjoint_left]
    rintro a ⟨w, hwC, rfl⟩ ha
    obtain ⟨E, hE, haE⟩ := Set.mem_iUnion₂.mp ha
    exact not_avoidsCenters_of_mem_boundary_support D (canonicalPrincipalization hres hrad) t
      (le_of_lt ht) E hE _ haE (hcl t le_rfl w)
  exact false_of_mem_support_center
    (chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) hsmp
    ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t)
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t)
    (⋃ E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary t,
      (E.support :
        Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t)))
    hcert
    (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C) hCcl hirr
    (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base η)
    (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base z)
    hgen ⟨z, hz, rfl⟩ hsmV hcomp hxi hdisj hagree hmem

theorem avoidsCenters_strictTransformι_of_smooth
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY) (t : ℕ)
    (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    (y : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t)) :
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).AvoidsCenters t
      (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base y) := by
  classical
  have := hsm
  have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D (canonicalPrincipalization hres hrad)
  have hsm0 : AlgebraicGeometry.Smooth
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι 0 ≫
        (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAtToSpec 0) :=
    smooth_strictTransformι_comp_schemeAtToSpec_zero (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) hsm
  have hDisj0 : ∀ C₁ C₂ :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0),
      C₁ ∈ irreducibleComponents
        ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0) →
      C₂ ∈ irreducibleComponents
        ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0) →
      C₁ ≠ C₂ → Disjoint C₁ C₂ := by
    intro C₁ C₂ h₁ h₂ hne
    exact FunctorialResolution.EmbeddedResolution.irreducibleComponentsDisjointOfSmooth k _ _ hsm0 C₁ h₁ C₂ h₂ hne
  have main : ∀ s : ℕ, s ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length →
      AlgebraicGeometry.Smooth
        ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι s ≫
          (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAtToSpec s) ∧
      ∀ r, r ≤ s →
        ∀ w : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform r),
        (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).AvoidsCenters r
          (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι r).base w) := by
    intro s
    induction s with
    | zero =>
      intro _
      refine ⟨hsm0, ?_⟩
      intro r hr w
      obtain rfl : r = 0 := Nat.le_zero.mp hr
      exact (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).avoidsCenters_zero _
    | succ i ih =>
      intro hi
      have hi' : i < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length :=
        Nat.lt_of_succ_le hi
      obtain ⟨ihsm, ihcl⟩ := ih (Nat.le_of_succ_le hi)
      have hsmq' : AlgebraicGeometry.Smooth
          ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι i ≫
            chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) i) := ihsm
      have hclear : ∀ w :
          ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform (i + 1)),
          (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).AvoidsCenters (i + 1)
            (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι (i + 1)).base w) := by
        intro w
        have hCw : irreducibleComponent w ∈ irreducibleComponents
            ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform (i + 1)) :=
          irreducibleComponent_mem_irreducibleComponents w
        obtain ⟨η₁, hη₁⟩ :=
          QuasiSober.sober hCw.1 (isClosed_of_mem_irreducibleComponents _ hCw)
        obtain ⟨C', hC'm, hη', hfr⟩ :=
          (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi'
            (irreducibleComponent w) hCw η₁ hη₁
        have hcont : Continuous
            ⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformMap i).base :=
          ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformMap i).base.hom.continuous
        have hsubcl : closure ({η₁} :
            Set ↥((D.toEmbeddedBlowupSequence
              (canonicalPrincipalization hres hrad)).strictTransform (i + 1))) ⊆
            ⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformMap i).base ⁻¹'
              closure ({((D.toEmbeddedBlowupSequence
                  (canonicalPrincipalization hres hrad)).strictTransformMap i).base η₁} :
                Set ↥((D.toEmbeddedBlowupSequence
                  (canonicalPrincipalization hres hrad)).strictTransform i)) := by
          refine closure_minimal ?_ (isClosed_closure.preimage hcont)
          intro v hv
          have hv' : v = η₁ := hv
          subst hv'
          exact subset_closure rfl
        have hwC : w ∈ closure ({η₁} :
            Set ↥((D.toEmbeddedBlowupSequence
              (canonicalPrincipalization hres hrad)).strictTransform (i + 1))) := by
          rw [hη₁]; exact mem_irreducibleComponent
        have hzC' : ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformMap i).base w
            ∈ C' := by
          have hmm := hsubcl hwC
          rw [Set.mem_preimage, hη'] at hmm
          exact hmm
        have hkey : ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι i).base
            (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformMap i).base w)
            = ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).blowdown i).base
                (((D.toEmbeddedBlowupSequence
                  (canonicalPrincipalization hres hrad)).strictTransformι (i + 1)).base w) := by
          have h : (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformMap i) ≫
              ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι i)).base w
              = (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι (i + 1)) ≫
                ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).blowdown i)).base w := by
            rw [(D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformMap_comp_strictTransformι i]
          simpa using h
        refine ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).avoidsCenters_succ_iff i _).mpr
          ⟨?_, ?_⟩
        · rw [← hkey]
          exact notMem_ambientCenter_support_of_notMem_detachedComponents hres hB hrad D i hi'
            hsmq' ihcl hDisj0 C' hC'm hfr _ hzC'
        · rw [← hkey]
          exact ihcl i le_rfl _
      refine ⟨smooth_strictTransformι_comp_schemeAtToSpec_succ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) hN i hi'
        ihsm ?_, ?_⟩
      · intro w
        exact (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).avoidsCenters_succ_iff i _).mp
          (hclear w)).1
      · intro r hr w
        rcases Nat.lt_or_ge r (i + 1) with hlt | hge
        · exact ihcl r (Nat.lt_succ_iff.mp hlt) w
        · obtain rfl : r = i + 1 := le_antisymm hr hge
          exact hclear w
  exact (main t ht).2 t le_rfl y

theorem strictTransformι_notMem_support_of_mem_boundary
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY) (t : ℕ)
    (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    (y : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (E : ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t).IdealSheafData)
    (hE : E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary t) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base y ∉
      (E.support :
        Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t)) := by
  intro hx
  exact not_avoidsCenters_of_mem_boundary_support D (canonicalPrincipalization hres hrad) t ht E hE _ hx
    (avoidsCenters_strictTransformι_of_smooth hres hB hrad D hsm t ht y)

end OpenImmersionRestriction

end FunctorialResolution.EmbeddedResolution

end
