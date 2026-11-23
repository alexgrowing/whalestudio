import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MapToEarlierScheme
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCasePrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialBlowupIteration
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialInvariantDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonotoneInvariantSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

noncomputable abbrev MarkedIdealWithBoundary.pullbackWithBoundary (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (E' : List Y.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  (T.pullbackOverField Y k' q g).withBoundary E'

private theorem false_of_mem_support_top {X : Scheme.{u}} (y : ↥X)
    (h : y ∈ (⊤ : X.IdealSheafData).support) : False := by
  have hb : (⊤ : X.IdealSheafData).support = ⊥ :=
    (Scheme.IdealSheafData.support_eq_bot_iff _).mpr rfl
  rw [hb] at h
  have h' : y ∈ ((⊥ : TopologicalSpace.Closeds ↥X) : Set ↥X) := h
  rw [TopologicalSpace.Closeds.coe_bot] at h'
  simp at h'

private theorem false_of_mem_support_of_comap_eq_top {A B : Scheme.{u}} (u : B ⟶ A)
    (I : A.IdealSheafData) (htop : I.comap u = ⊤) (y : ↥B) (hz : u.base y ∈ I.support) : False := by
  have hmem : y ∈ (I.comap u).support := Scheme.IdealSheafData.mem_support_comap.mpr hz
  rw [htop] at hmem
  exact false_of_mem_support_top y hmem

private theorem flat_lastMap {X X' : Scheme.{u}} {φ : X' ⟶ X}
    [AlgebraicGeometry.Flat φ] {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (c : SequenceOfBlowupsPullback φ s' s) : AlgebraicGeometry.Flat c.lastMap :=
  MorphismProperty.of_isPullback c.isPullback_lastMap.flip inferInstance

private theorem isNoetherian_schemeAt_of_le_length {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (hX : AlgebraicGeometry.IsNoetherian X) (d : MarkedBlowupSequenceData p I m E) :
    ∀ i ≤ d.length, AlgebraicGeometry.IsNoetherian (d.obj i) := by
  have : AlgebraicGeometry.IsNoetherian X := hX
  intro i
  induction i with
  | zero =>
      intro _
      exact isNoetherian_of_iso d.toBlowupSequenceData.isoZero.symm
  | succ n ih =>
      intro hn
      have : AlgebraicGeometry.IsNoetherian (d.obj n) := ih (le_of_lt hn)
      exact isNoetherian_of_isBlowupAlongIdealSheaf (d.toBlowupSequenceData.isBlowup n hn)

private theorem centerAtLast_ne_top_of_isAdmissibleCenter {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (h : MarkedBlowupSequenceData.IsAdmissibleCenter s) : s.centerAtLast ≠ ⊤ := h.1

private theorem length_monomialIterateFromEmpty_zero (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) :
    (monomialIterateFromEmpty hinv T 0).length = 0 := emptyMarkedBlowupSequenceData_length _ _ _ _

private theorem nonempty_sequenceOfBlowupsPullback_of_length_eq_one {A B : Scheme.{u}} (φ : B ⟶ A)
    (t : BlowupSequenceData A) (t' : BlowupSequenceData B) (ht : t.length = 1) (ht' : t'.length = 1)
    (ψ : t'.obj 0 ⟶ t.obj 0)
    (hψ : t'.isoZero.hom ≫ φ ≫ t.isoZero.inv = ψ) (hflat : AlgebraicGeometry.Flat ψ)
    (hcen : t'.center 0 = (t.center 0).comap ψ) (hne : t'.center 0 ≠ ⊤) :
    Nonempty (SequenceOfBlowupsPullback φ t'.toSequenceOfBlowups t.toSequenceOfBlowups) := by
  have := hflat
  have hlt : (0 : ℕ) < t.length := by rw [ht]; omega
  have hlt' : (0 : ℕ) < t'.length := by rw [ht']; omega
  have hB : Blowup.IsBlowupAlongIdealSheaf (t.map 0) (t.center 0) := t.isBlowup 0 hlt
  have hB' : Blowup.IsBlowupAlongIdealSheaf (t'.map 0) ((t.center 0).comap ψ) := by
    have h := t'.isBlowup 0 hlt'
    rwa [hcen] at h
  obtain ⟨qq, -, hqq⟩ := hB.exists_isPullback_of_flat ψ hB'
  refine ⟨SequenceOfBlowupsPullback.ofLengthOne φ t t' ht ht' qq ?_ ?_ hne⟩
  · rw [hψ]
    exact hqq
  · rw [hψ]
    exact hcen

private theorem nonempty_sequenceOfBlowupsPullback_blowupAtCenter_of_comap_eq_top {k₁ k₂ : Type u}
    [Field k₁] [Field k₂] {X₁ X₂ : Scheme.{u}}
    {p₁ : X₁ ⟶ Spec (CommRingCat.of k₁)} {I₁ : X₁.IdealSheafData} {m₁ : ℕ}
    {E₁ : List X₁.IdealSheafData} {p₂ : X₂ ⟶ Spec (CommRingCat.of k₂)} {I₂ : X₂.IdealSheafData}
    {m₂ : ℕ} {E₂ : List X₂.IdealSheafData} (g : X₂ ⟶ X₁) (hg : AlgebraicGeometry.Flat g)
    (hinv : ComapIsoInvariance.{u}) (S : MarkedBlowupSequenceData p₁ I₁ m₁ E₁)
    (S' : MarkedBlowupSequenceData p₂ I₂ m₂ E₂) (hS : MarkedBlowupSequenceData.IsAdmissibleCenter S)
    (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups)
    (htop : (S.centerAtLast).comap c.lastMap = ⊤) :
    Nonempty (SequenceOfBlowupsPullback g S'.toSequenceOfBlowups (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups) := by
  have := hg
  have : AlgebraicGeometry.Flat c.lastMap := flat_lastMap c
  have hmiss : ∀ i : ℕ, i < (S.monomialBlowupStep hS).toBlowupSequenceData.length →
      ∀ z : ↥((S.monomialBlowupStep hS).toBlowupSequenceData.obj i),
        z ∈ ((S.monomialBlowupStep hS).toBlowupSequenceData.center i).support →
        ∀ y : ↥(S'.obj S'.length),
          c.lastMap.base y ≠ ((S.monomialBlowupStep hS).toBlowupSequenceData.projectionToBase i).base z := by
    intro i hi z hz y heq
    have hlen : (S.monomialBlowupStep hS).toBlowupSequenceData.length = 1 :=
      MarkedBlowupSequenceData.monomialBlowupStep_length ..
    have hi0 : i = 0 := by omega
    subst hi0
    have hzz : ((S.monomialBlowupStep hS).toBlowupSequenceData.projectionToBase 0).base z ∈ S.centerAtLast.support := hz
    have hz2 : c.lastMap.base y ∈ S.centerAtLast.support := by
      rw [heq]
      exact hzz
    exact false_of_mem_support_of_comap_eq_top c.lastMap S.centerAtLast htop y hz2
  have hE0 : (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData.length = 0 := emptyMarkedBlowupSequenceData_length _ _ _ _
  have e := SequenceOfBlowupsPullback.ofCentersMissImage c.lastMap (S.monomialBlowupStep hS).toBlowupSequenceData hmiss
    (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData hE0
  have c2 := SequenceOfBlowupsPullback.concat S.toBlowupSequenceData (S.monomialBlowupStep hS).toBlowupSequenceData
    S'.toBlowupSequenceData
    (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData c e
  refine ⟨?_⟩
  rw [MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv S hS, MarkedBlowupSequenceData.append_toBlowupSequenceData]
  exact SequenceOfBlowupsPullback.ofConcatLengthZero g S'.toBlowupSequenceData
    (S.appendToBlowupSequenceData (S.monomialBlowupStep hS)).toSequenceOfBlowups
    (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData hE0 c2

private theorem nonempty_sequenceOfBlowupsPullback_blowupAtCenter {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    {X₁ X₂ : Scheme.{u}}
    {p₁ : X₁ ⟶ Spec (CommRingCat.of k₁)} {I₁ : X₁.IdealSheafData} {m₁ : ℕ}
    {E₁ : List X₁.IdealSheafData} {p₂ : X₂ ⟶ Spec (CommRingCat.of k₂)} {I₂ : X₂.IdealSheafData}
    {m₂ : ℕ} {E₂ : List X₂.IdealSheafData} (g : X₂ ⟶ X₁) (hg : AlgebraicGeometry.Flat g)
    (hinv : ComapIsoInvariance.{u}) (S : MarkedBlowupSequenceData p₁ I₁ m₁ E₁)
    (S' : MarkedBlowupSequenceData p₂ I₂ m₂ E₂) (hS : MarkedBlowupSequenceData.IsAdmissibleCenter S)
    (hS' : MarkedBlowupSequenceData.IsAdmissibleCenter S') (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups)
    (hcen : S'.centerAtLast = (S.centerAtLast).comap c.lastMap) :
    Nonempty (SequenceOfBlowupsPullback g (MarkedBlowupSequenceData.blowupAtCenter hinv S').toSequenceOfBlowups
      (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups) := by
  have := hg
  have : AlgebraicGeometry.Flat c.lastMap := flat_lastMap c
  have h1 : (S'.monomialBlowupStep hS').toBlowupSequenceData.isoZero.hom ≫ c.lastMap ≫
      (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv
      = c.lastMap ≫ (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv :=
    Category.id_comp _
  have h2 : c.lastMap ≫ (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv = c.lastMap :=
    Category.comp_id _
  have hconj : (S'.monomialBlowupStep hS').toBlowupSequenceData.isoZero.hom ≫ c.lastMap ≫
      (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv = c.lastMap := h1.trans h2
  obtain ⟨e⟩ := nonempty_sequenceOfBlowupsPullback_of_length_eq_one c.lastMap
    (S.monomialBlowupStep hS).toBlowupSequenceData
    (S'.monomialBlowupStep hS').toBlowupSequenceData (MarkedBlowupSequenceData.monomialBlowupStep_length ..)
    (MarkedBlowupSequenceData.monomialBlowupStep_length ..) c.lastMap hconj
    (flat_lastMap c) hcen (centerAtLast_ne_top_of_isAdmissibleCenter S' hS')
  refine ⟨?_⟩
  rw [MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv S hS,
    MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv S' hS',
    MarkedBlowupSequenceData.append_toBlowupSequenceData, MarkedBlowupSequenceData.append_toBlowupSequenceData]
  exact SequenceOfBlowupsPullback.concat S.toBlowupSequenceData (S.monomialBlowupStep hS).toBlowupSequenceData
    S'.toBlowupSequenceData (S'.monomialBlowupStep hS').toBlowupSequenceData c e

private theorem minIndexCard_ne_zero_and_monomialCenter_comap_of_flat (hGeom : MonomialGeometryHypotheses.{u})
    (Tn : MarkedIdealWithBoundary.{u})
    (Yj : Scheme.{u}) (k' : Type u) [instk' : Field k'] (qj : Yj ⟶ Spec (CommRingCat.of k'))
    (φ : Yj ⟶ Tn.scheme) (hφ : AlgebraicGeometry.Flat φ)
    (I' : Yj.IdealSheafData) (E2 : List Yj.IdealSheafData)
    (hTn : MonomialCenter.IsLocallyMonomialTriple Tn)
    (hTj : MonomialCenter.IsLocallyMonomialTriple (@MarkedIdealWithBoundary.mk k' instk' Yj qj I' Tn.mult E2))
    (hI' : I' = Tn.ideal.comap φ)
    (hE2 : MarkedIdealWithBoundary.SameNontrivialBoundary E2 (Tn.boundary.map fun D => D.comap φ))
    (hordφ : ∀ (A : Tn.scheme.IdealSheafData) (y : ↥Yj),
      orderAt (A.comap φ) y = orderAt A (φ y)) :
    (minIndexCard I' Tn.mult E2 ≠ 0 → minIndexCard Tn.ideal Tn.mult Tn.boundary ≠ 0) ∧
      (minIndexCard Tn.ideal Tn.mult Tn.boundary ≠ 0 →
        ((monomialCenter Tn.ideal Tn.mult Tn.boundary).comap φ = ⊤ ∨
          (minIndexCard I' Tn.mult E2 ≠ 0 ∧
            monomialCenter I' Tn.mult E2 = (monomialCenter Tn.ideal Tn.mult Tn.boundary).comap φ))) := by
  classical
  have := hφ
  subst hI'
  have htrip : (@MarkedIdealWithBoundary.mk k' instk' Yj qj (Tn.ideal.comap φ) Tn.mult E2).withBoundary
      (Tn.boundary.map fun D => D.comap φ) = Tn.pullbackOverField Yj k' qj φ :=
    MarkedIdealWithBoundary.mk_eq_mk Yj Tn.mult rfl rfl rfl
  have hTpb : MonomialCenter.IsLocallyMonomialTriple (Tn.pullbackOverField Yj k' qj φ) := by
    rw [← htrip]
    exact MonomialCenter.isLocallyMonomialTriple_withBoundary hGeom _ hTj _ hE2
  have hP : MonomialCenter.IsComponentCompatiblePullback Tn Yj k' qj φ :=
    MonomialCenter.IsComponentCompatiblePullback.of_flat hGeom Tn hTn.valid Yj k' qj φ hTpb.valid hordφ
  have hmin : minIndexCard (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
      (Tn.pullbackOverField Yj k' qj φ).boundary = minIndexCard (Tn.ideal.comap φ) Tn.mult E2 :=
    (MonomialCenter.minIndexCard_eq_of_sameNontrivialBoundary (Tn.ideal.comap φ) Tn.mult hE2).symm
  have hcenpb : monomialCenter (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
      (Tn.pullbackOverField Yj k' qj φ).boundary = monomialCenter (Tn.ideal.comap φ) Tn.mult E2 :=
    (MonomialCenter.monomialCenter_eq_of_sameNontrivialBoundary (Tn.ideal.comap φ) Tn.mult hE2).symm
  refine ⟨?_, ?_⟩
  · intro hne
    have hne' : minIndexCard (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
        (Tn.pullbackOverField Yj k' qj φ).boundary ≠ 0 := by
      rw [hmin]
      exact hne
    exact (MonomialCenter.minIndexCard_ne_zero_and_le_pullbackOverField hGeom Tn Yj k' qj φ hTn hTpb hP hne').1
  · intro h0
    by_cases hz : minIndexCard (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
        (Tn.pullbackOverField Yj k' qj φ).boundary = 0
    · exact Or.inl (MonomialCenter.comap_monomialCenter_eq_top hGeom Tn Yj k' qj φ hTn hTpb hP h0
        (Or.inl hz))
    · have hle := (MonomialCenter.minIndexCard_pullbackOverField_eq_zero_or_centerInvariant_le hGeom Tn Yj k' qj φ hTn hTpb
        hP).resolve_left hz
      rw [MonomialCenter.centerInvariant_le_iff] at hle
      rcases hle with hlt | ⟨hm, hx, hs⟩
      · exact Or.inl (MonomialCenter.comap_monomialCenter_eq_top hGeom Tn Yj k' qj φ hTn hTpb hP h0
          (Or.inr hlt))
      · refine Or.inr ⟨?_, ?_⟩
        · rw [← hmin]
          exact hz
        · rw [← hcenpb]
          exact MonomialCenter.monomialCenter_pullbackOverField_eq_comap hGeom Tn Yj k' qj φ hTn hTpb hP
            hm.symm hx.symm
            (MonomialCenter.lexMaxIndices_pullbackOverField_eq_image Tn Yj k' qj φ hs)

private theorem sequenceOfBlowupsPullback_blowupAtCenter_cases
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hg : AlgebraicGeometry.Flat g) (E' : List Y.IdealSheafData)
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap g))
    (hT' : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y k' q g E'))
    (hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b g →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z))
    (S : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (S' : MarkedBlowupSequenceData (T.pullbackWithBoundary Y k' q g E').structMap
      (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
      (T.pullbackWithBoundary Y k' q g E').boundary)
    (hTn : MonomialCenter.IsLocallyMonomialTriple (tripleAtLastBlowup T S))
    (hTj : MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLastBlowup (T.pullbackWithBoundary Y k' q g E') S'))
    (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups) :
    (MarkedBlowupSequenceData.IsAdmissibleCenter S' →
        minIndexCard (tripleAtLastBlowup T S).ideal (tripleAtLastBlowup T S).mult
          (tripleAtLastBlowup T S).boundary ≠ 0) ∧
      (MarkedBlowupSequenceData.IsAdmissibleCenter S →
        Nonempty (SequenceOfBlowupsPullback g S'.toSequenceOfBlowups
            (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups) ∨
          (MarkedBlowupSequenceData.IsAdmissibleCenter S' ∧
            Nonempty (SequenceOfBlowupsPullback g
              (MarkedBlowupSequenceData.blowupAtCenter hinv S').toSequenceOfBlowups
              (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups))) := by
  classical
  have hfl1 : AlgebraicGeometry.Flat g := hg
  have hfl2 : @AlgebraicGeometry.Flat (T.pullbackWithBoundary Y k' q g E').scheme T.scheme g := hg
  have hflt : AlgebraicGeometry.Flat c.lastMap := flat_lastMap c
  have hN : ∀ i : ℕ, i ≤ S.length → AlgebraicGeometry.IsNoetherian (S.obj i) :=
    isNoetherian_schemeAt_of_le_length hT.valid.isNoetherian S
  have hN' : ∀ i : ℕ, i ≤ S'.length → AlgebraicGeometry.IsNoetherian (S'.obj i) :=
    isNoetherian_schemeAt_of_le_length hT'.valid.isNoetherian S'
  obtain ⟨hIdeal, hboundary⟩ := SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap S S' c rfl hE hN hN'
  have hsq : IsPullback c.lastMap (S'.proj S'.length) (S.proj S.length) g := by
    rw [MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups S S.length,
      MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups S' S'.length]
    exact c.isPullback_lastMap
  have hordφ : ∀ (A : (S.obj S.length).IdealSheafData) (y : ↥(S'.obj S'.length)),
      orderAt (A.comap c.lastMap) y = orderAt A (c.lastMap y) :=
    fun A y => hord (S.obj S.length) (S.proj S.length) (S.proj S.length ≫ T.structMap) rfl
      (S.ideal S.length) (S.boundary S.length) hTn.valid (S'.obj S'.length) c.lastMap
      (S'.proj S'.length) hsq A y
  have hminCard := minIndexCard_ne_zero_and_monomialCenter_comap_of_flat hGeom (tripleAtLastBlowup T S)
    (S'.obj S'.length) k' (S'.proj S'.length ≫ q) c.lastMap
    (flat_lastMap c) (S'.ideal S'.length) (S'.boundary S'.length)
    hTn hTj hIdeal hboundary hordφ
  refine ⟨fun hok' => hminCard.1
    (minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter (T.pullbackWithBoundary Y k' q g E') S' hok'), ?_⟩
  intro hok
  have h0 := minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T S hok
  rcases hminCard.2 h0 with hmiss | ⟨hne', hcenEq⟩
  · exact Or.inl
      (nonempty_sequenceOfBlowupsPullback_blowupAtCenter_of_comap_eq_top g hg hinv S S' hok c hmiss)
  · have hok' : MarkedBlowupSequenceData.IsAdmissibleCenter S' :=
      isAdmissibleCenter_of_minIndexCard_tripleAtLastBlowup_ne_zero hGeom (T.pullbackWithBoundary Y k' q g E') S'
        hTj hne'
    exact Or.inr ⟨hok', nonempty_sequenceOfBlowupsPullback_blowupAtCenter g hg hinv S S' hok hok' c hcenEq⟩

private theorem exists_sequenceOfBlowupsPullback_monomialIterateFromEmpty
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hg : AlgebraicGeometry.Flat g) (E' : List Y.IdealSheafData)
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap g))
    (hT' : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y k' q g E'))
    (hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b g →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z))
    (n : ℕ) :
    n ≤ monomialStallIndexOfTriple hinv T →
    ∃ j : ℕ,
      (∀ j' : ℕ, j' < j →
        MarkedBlowupSequenceData.IsAdmissibleCenter (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j')) ∧
      Nonempty (SequenceOfBlowupsPullback g
        (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j).toSequenceOfBlowups
        (monomialIterateFromEmpty hinv T n).toSequenceOfBlowups) := by
  have := hg
  induction n with
  | zero =>
    intro _
    refine ⟨0, fun j' hj' => absurd hj' (Nat.not_lt_zero j'), ⟨?_⟩⟩
    refine SequenceOfBlowupsPullback.ofCentersMissImage g (monomialIterateFromEmpty hinv T 0).toBlowupSequenceData ?_
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') 0).toBlowupSequenceData
      (length_monomialIterateFromEmpty_zero hinv (T.pullbackWithBoundary Y k' q g E'))
    intro i hi
    exact absurd hi (by rw [length_monomialIterateFromEmpty_zero hinv T]; exact Nat.not_lt_zero i)
  | succ n ih =>
    intro hn
    have hn' : n < monomialStallIndexOfTriple hinv T := lt_of_lt_of_le (Nat.lt_succ_self n) hn
    obtain ⟨j, hjstep, hc⟩ := ih (le_of_lt hn')
    obtain ⟨c⟩ := hc
    have hok : MarkedBlowupSequenceData.IsAdmissibleCenter (monomialIterateFromEmpty hinv T n) :=
      isAdmissibleCenter_of_lt_monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary n hn'
    rcases (sequenceOfBlowupsPullback_blowupAtCenter_cases hGeom hinv T Y k' q g hg E' hT hE hT' hord
      (monomialIterateFromEmpty hinv T n)
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT n)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv
        (T.pullbackWithBoundary Y k' q g E') hT' j) c).2 hok with h | ⟨hok', h⟩
    · exact ⟨j, hjstep, h⟩
    · refine ⟨j + 1, ?_, h⟩
      intro j' hj'
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj') with h1 | h1
      · exact hjstep j' h1
      · rw [h1]
        exact hok'

theorem monomialPrincipalization_isPullbackBlowupSequence_of_flat
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) [AlgebraicGeometry.Flat g] (E' : List Y.IdealSheafData)
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap g))
    (hT' : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y k' q g E'))
    (hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b g →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z)) :
    IsPullbackBlowupSequence g
      (monomialPrincipalization hinv (T.pullbackWithBoundary Y k' q g E')).toSequenceOfBlowups
      (monomialPrincipalization hinv T).toSequenceOfBlowups := by
  classical
  have hg : AlgebraicGeometry.Flat g := inferInstance
  obtain ⟨j, hjstep, hc⟩ := exists_sequenceOfBlowupsPullback_monomialIterateFromEmpty hGeom hinv T Y k' q g hg E'
    hT hE hT' hord (monomialStallIndexOfTriple hinv T) le_rfl
  obtain ⟨c⟩ := hc
  have hstall : ¬ MarkedBlowupSequenceData.IsAdmissibleCenter
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j) := by
    intro hok'
    refine (sequenceOfBlowupsPullback_blowupAtCenter_cases hGeom hinv T Y k' q g hg E' hT hE hT' hord
      (monomialIterateFromEmpty hinv T (monomialStallIndexOfTriple hinv T))
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT
        (monomialStallIndexOfTriple hinv T))
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv
        (T.pullbackWithBoundary Y k' q g E') hT' j) c).1 hok' ?_
    exact minIndexCard_monomialIterateFromEmpty_stallIndex_eq_zero hGeom hinv T hT
  have hjeq : monomialStallIndex hinv (T.pullbackWithBoundary Y k' q g E').structMap
      (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
      (T.pullbackWithBoundary Y k' q g E').boundary = j :=
    monomialStallIndex_eq_of_isStationaryAt hinv (T.pullbackWithBoundary Y k' q g E').structMap
      (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
      (T.pullbackWithBoundary Y k' q g E').boundary j
      ((MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv
        (emptyMarkedBlowupSequenceData (T.pullbackWithBoundary Y k' q g E').structMap
          (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
          (T.pullbackWithBoundary Y k' q g E').boundary) j).mpr hstall) hjstep
  rw [monomialPrincipalization_apply, monomialPrincipalization_apply, monomialBlowupSeq_eq_monomialBlowupIterate,
    monomialBlowupSeq_eq_monomialBlowupIterate, hjeq]
  exact SequenceOfBlowupsPullback.isPullbackSequenceOfBlowups c

private theorem smooth_fst_of_isPullback {X Y B Q : Scheme.{u}} {hm : Y ⟶ X}
    [AlgebraicGeometry.Smooth hm] {b : B ⟶ X} {a : Q ⟶ B} {b' : Q ⟶ Y}
    (hsq : IsPullback a b' b hm) : AlgebraicGeometry.Smooth a :=
  MorphismProperty.of_isPullback hsq.flip inferInstance

theorem monomialPrincipalization_isPullbackBlowupSequence_of_smooth
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h] (_hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (hT' : MonomialCenter.IsLocallyMonomialTriple ((T.pullbackAlong Y q h).withBoundary E')) :
    IsPullbackBlowupSequence h
      (monomialPrincipalization hinv ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
      (monomialPrincipalization hinv T).toSequenceOfBlowups := by
  have : AlgebraicGeometry.Flat h := inferInstance
  have hE2 : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap h) := hE.symm
  have hT2 : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y T.base q h E') := hT'
  have hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b h →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z) := by
    intro B b pB hbp IB EB hvalid Q a b' hsq A z
    have : CharZero T.base := hvalid.charZero
    have : AlgebraicGeometry.Smooth pB := hvalid.smooth
    have : AlgebraicGeometry.Smooth a := smooth_fst_of_isPullback hsq
    exact orderAt_comap T.base pB a A z
  exact monomialPrincipalization_isPullbackBlowupSequence_of_flat hGeom hinv T Y T.base q h E' hT hE2 hT2 hord

end FunctorialResolution.EmbeddedResolution

end
