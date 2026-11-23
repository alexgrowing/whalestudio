import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IdealSheafFlatDescent
import Development.ResolutionOfSingularities.Foundations.Schemes.AffineOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.ClosedImmersionKrullDim
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.DisjointUnionCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.StrictTransformClosedImmersion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev markedTripleOfIdeal (k : Type u) [Field k] (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of k)) (J : Y.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  { base := k, scheme := Y, structMap := q, ideal := J, mult := 1, boundary := [] }

@[simp] theorem markedTripleOfIdeal_scheme (k : Type u) [Field k] (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of k)) (J : Y.IdealSheafData) :
    (markedTripleOfIdeal k Y q J).scheme = Y := rfl

@[simp] theorem markedTripleOfIdeal_structureMorphism (k : Type u) [Field k] (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of k)) (J : Y.IdealSheafData) :
    (markedTripleOfIdeal k Y q J).structMap = q := rfl

@[simp] theorem markedTripleOfIdeal_ideal (k : Type u) [Field k] (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of k)) (J : Y.IdealSheafData) :
    (markedTripleOfIdeal k Y q J).ideal = J := rfl

def HasLocalEtaleCharts {X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) : Prop :=
  ∀ x : X', ∃ (W : X'.Opens) (_ : x ∈ W) (n : ℕ), Nonempty (EtaleChart p W n)

private theorem ofIdealTop_mono {X : Scheme.{u}} {I J : Ideal Γ(X, ⊤)} (h : I ≤ J) :
    AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop I ≤
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop J := by
  intro U
  exact Ideal.map_mono h

theorem EtaleChart.coordIdeal_mono {Y : Scheme.{u}} {k : Type u} [Field k]
    {p : Y ⟶ Spec (CommRingCat.of k)} {U : Y.Opens} {m : ℕ} (ch : EtaleChart p U m)
    {S S' : Finset (Fin m)} (h : S ⊆ S') :
    ch.coordIdeal S ≤ ch.coordIdeal S' := by
  simp only [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  apply Scheme.IdealSheafData.comap_mono
  apply ofIdealTop_mono
  apply Ideal.span_mono
  rintro x ⟨i, hi, rfl⟩
  exact ⟨i, Finset.mem_coe.mpr (h (Finset.mem_coe.mp hi)), rfl⟩

private theorem coe_support_ker_eq_range {X X' : Scheme.{u}} (τ : X ⟶ X') [IsClosedImmersion τ] :
    (↑(Scheme.Hom.ker τ).support : Set X') = Set.range τ.base := by
  have h1 : ∀ z, ((FunctorialResolution.EmbeddedResolution.kerSubschemeIso τ).hom ≫ τ).base z
      = (Scheme.Hom.ker τ).subschemeι.base z := by
    intro z
    rw [FunctorialResolution.EmbeddedResolution.kerSubschemeIso_hom_comp τ]
  have h2 : ∀ x, ((FunctorialResolution.EmbeddedResolution.kerSubschemeIso τ).inv ≫ (Scheme.Hom.ker τ).subschemeι).base x
      = τ.base x := by
    intro x
    rw [FunctorialResolution.EmbeddedResolution.kerSubschemeIso_inv_comp τ]
  rw [← Scheme.IdealSheafData.range_subschemeι]
  apply Set.Subset.antisymm
  · rintro y ⟨z, rfl⟩
    exact ⟨(FunctorialResolution.EmbeddedResolution.kerSubschemeIso τ).hom.base z, h1 z⟩
  · rintro y ⟨x, rfl⟩
    exact ⟨(FunctorialResolution.EmbeddedResolution.kerSubschemeIso τ).inv.base x, h2 x⟩

theorem restrictIdeal_ker_eq_top_of_not_mem {X X' : Scheme.{u}} (τ : X ⟶ X')
    [IsClosedImmersion τ] (U : X'.Opens) (h : ∀ x : X, τ.base x ∉ U) :
    restrictIdeal τ.ker U = ⊤ := by
  rw [restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.eq_top_iff_support_eq_empty, support_comap_eq,
    coe_support_ker_eq_range τ]
  refine Set.subset_empty_iff.mp ?_
  rintro y ⟨x, hx⟩
  refine absurd ?_ (h x)
  rw [hx]
  exact y.2

structure AdaptedEtaleChart {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') (c : ℕ) : Type u where
  opens : X'.Opens
  isAffine : IsAffineOpen opens
  coordCount : ℕ
  chart : EtaleChart p opens coordCount
  idxSet : Finset (Fin coordCount)
  card_idxSet : idxSet.card = c
  coord : Fin coordCount
  coord_mem : coord ∈ idxSet
  restrictIdeal_ker : restrictIdeal τ.ker opens = chart.coordIdeal idxSet

private theorem coordIdeal_restrict {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U V : X.Opens} {m : ℕ} (ch : EtaleChart p U m)
    (h : V ≤ U) (S : Finset (Fin m)) :
    (ch.restrict h).coordIdeal S = (ch.coordIdeal S).comap (X.homOfLE h) := by
  simp only [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.restrict_map]
  rw [Scheme.IdealSheafData.comap_comp]

theorem exists_adaptedEtaleChart {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') (c : ℕ) (hc : 1 ≤ c)
    (hcodim : HasEtaleCoordCodim p τ c) :
    ∀ x : X, ∃ A : AdaptedEtaleChart p τ c, τ.base x ∈ A.opens := by
  intro x
  obtain ⟨U, hxU, m, ch, S, hcard, hker⟩ := hcodim x
  obtain ⟨V, hxV, hVU⟩ := AlgebraicGeometry.Scheme.exists_affineOpens_mem_le hxU
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  obtain ⟨j, hj⟩ := hSne
  refine ⟨⟨(V : X'.Opens), V.2, m, ch.restrict hVU, S, hcard, j, hj, ?_⟩, hxV⟩
  rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal (Scheme.Hom.ker τ) hVU, hker,
    coordIdeal_restrict ch hVU S]

structure DisjointEtaleChart {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') : Type u where
  opens : X'.Opens
  isAffine : IsAffineOpen opens
  coordCount : ℕ
  chart : EtaleChart p opens coordCount
  not_mem : ∀ x : X, τ.base x ∉ opens

theorem exists_disjointEtaleChart {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') [IsClosedImmersion τ]
    (hcharts : HasLocalEtaleCharts p) (y : X') (hy : ∀ x : X, τ.base x ≠ y) :
    ∃ F : DisjointEtaleChart p τ, y ∈ F.opens := by
  obtain ⟨W, hyW, n, ⟨ch⟩⟩ := hcharts y
  have hclosed : IsClosed (Set.range τ.base) := by
    rw [← coe_support_ker_eq_range τ]
    exact (Scheme.Hom.ker τ).support.2
  have hopen : IsOpen ((W : Set X') ∩ (Set.range τ.base)ᶜ) :=
    W.isOpen.inter hclosed.isOpen_compl
  have hynot : y ∉ Set.range τ.base := by
    rintro ⟨x, hx⟩
    exact hy x hx
  set O : X'.Opens := ⟨(W : Set X') ∩ (Set.range τ.base)ᶜ, hopen⟩
  have hyO : y ∈ O := Set.mem_inter hyW hynot
  obtain ⟨U, hyU, hUO⟩ := AlgebraicGeometry.Scheme.exists_affineOpens_mem_le hyO
  have hUW : (U : X'.Opens) ≤ W := by
    intro z hz
    exact (hUO hz).1
  refine ⟨⟨(U : X'.Opens), U.2, n, ch.restrict hUW, ?_⟩, hyU⟩
  intro x hx
  exact (hUO hx).2 ⟨x, rfl⟩

def coverOpens {X X' : Scheme.{u}} {k : Type u} [Field k]
    {p : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ} {α : Type v} {β : Type w}
    (A : α → AdaptedEtaleChart p τ c) (B : β → DisjointEtaleChart p τ) : α ⊕ β → X'.Opens
  | Sum.inl a => (A a).opens
  | Sum.inr b => (B b).opens

@[simp] theorem coverOpens_inl {X X' : Scheme.{u}} {k : Type u} [Field k]
    {p : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ} {α : Type v} {β : Type w}
    (A : α → AdaptedEtaleChart p τ c) (B : β → DisjointEtaleChart p τ) (a : α) :
    coverOpens A B (Sum.inl a) = (A a).opens := rfl

@[simp] theorem coverOpens_inr {X X' : Scheme.{u}} {k : Type u} [Field k]
    {p : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ} {α : Type v} {β : Type w}
    (A : α → AdaptedEtaleChart p τ c) (B : β → DisjointEtaleChart p τ) (b : β) :
    coverOpens A B (Sum.inr b) = (B b).opens := rfl

def coverHypersurfaceIdeal {X X' : Scheme.{u}} {k : Type u} [Field k]
    {p : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ} {α : Type v} {β : Type w}
    (A : α → AdaptedEtaleChart p τ c) (B : β → DisjointEtaleChart p τ) :
    (i : α ⊕ β) → (coverOpens A B i).toScheme.IdealSheafData
  | Sum.inl a => (A a).chart.coordIdeal {(A a).coord}
  | Sum.inr _ => ⊤

theorem coverHypersurfaceIdeal_inl {X X' : Scheme.{u}} {k : Type u} [Field k]
    {p : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ} {α : Type v} {β : Type w}
    (A : α → AdaptedEtaleChart p τ c) (B : β → DisjointEtaleChart p τ) (a : α) :
    coverHypersurfaceIdeal A B (Sum.inl a) = (A a).chart.coordIdeal {(A a).coord} := rfl

theorem coverHypersurfaceIdeal_inr {X X' : Scheme.{u}} {k : Type u} [Field k]
    {p : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ} {α : Type v} {β : Type w}
    (A : α → AdaptedEtaleChart p τ c) (B : β → DisjointEtaleChart p τ) (b : β) :
    coverHypersurfaceIdeal A B (Sum.inr b) = ⊤ := rfl

structure MaximalContactCover {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') (I : X.IdealSheafData) (c : ℕ) :
    Type (u + 1) where
  toCoverData : MaxContactReduction.FiniteOpenCoverWithIdeals (markedTripleOfIdeal k X' p (imageIdealSheaf τ I))
  covers : iSup toCoverData.opens = ⊤
  isAffine : ∀ i : toCoverData.idx, IsAffineOpen (toCoverData.opens i)
  hasChart : ∀ i : toCoverData.idx, ∃ n : ℕ,
    Nonempty (EtaleChart p (toCoverData.opens i) n)
  hypersurface : ∀ i : toCoverData.idx, toCoverData.localIdeal i = ⊤ ∨
    ∃ (n : ℕ) (ch : EtaleChart p (toCoverData.opens i) n) (j : Fin n),
      toCoverData.localIdeal i = ch.coordIdeal {j}
  adapted : ∀ i : toCoverData.idx,
    (toCoverData.localIdeal i = ⊤ ∧ ∀ x : X, τ.base x ∉ toCoverData.opens i) ∨
    ∃ (n : ℕ) (ch : EtaleChart p (toCoverData.opens i) n) (S : Finset (Fin n)) (j : Fin n),
      S.card = c ∧ j ∈ S ∧
        restrictIdeal τ.ker (toCoverData.opens i) = ch.coordIdeal S ∧
        toCoverData.localIdeal i = ch.coordIdeal {j}

theorem nonempty_maximalContactCover {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.QuasiCompact p]
    (τ : X ⟶ X') [IsClosedImmersion τ] (I : X.IdealSheafData) (c : ℕ) (hc : 1 ≤ c)
    (hcodim : HasEtaleCoordCodim p τ c) (hcharts : HasLocalEtaleCharts p) :
    Nonempty (MaximalContactCover p τ I c) := by
  classical
  have hSpec : IsCompact (Set.univ : Set ↥(Spec (CommRingCat.of k))) := by
    have h := (AlgebraicGeometry.isAffineOpen_top (Spec (CommRingCat.of k))).isCompact
    rwa [TopologicalSpace.Opens.coe_top] at h
  have hX'c : IsCompact (Set.univ : Set ↥X') := by
    have h := AlgebraicGeometry.QuasiCompact.isCompact_preimage (f := p) Set.univ isOpen_univ hSpec
    rwa [Set.preimage_univ] at h
  have hcover : ∀ y : ↥X', ∃ q : AdaptedEtaleChart p τ c ⊕ DisjointEtaleChart p τ,
      y ∈ coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q := by
    intro y
    by_cases hy : ∃ x : ↥X, τ.base x = y
    · obtain ⟨x, hx⟩ := hy
      obtain ⟨A, hA⟩ := exists_adaptedEtaleChart p τ c hc hcodim x
      refine ⟨Sum.inl A, ?_⟩
      rw [← hx]
      exact hA
    · have hy' : ∀ x : X, τ.base x ≠ y := fun x hx => hy ⟨x, hx⟩
      obtain ⟨F, hF⟩ := exists_disjointEtaleChart p τ hcharts y hy'
      exact ⟨Sum.inr F, hF⟩
  have hsub : (Set.univ : Set ↥X') ⊆
      ⋃ q : AdaptedEtaleChart p τ c ⊕ DisjointEtaleChart p τ,
        ((coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q :
          X'.Opens) : Set ↥X') := by
    intro y _
    obtain ⟨q, hq⟩ := hcover y
    exact Set.mem_iUnion.2 ⟨q, hq⟩
  obtain ⟨t, ht⟩ := hX'c.elim_finite_subcover
    (fun q : AdaptedEtaleChart p τ c ⊕ DisjointEtaleChart p τ =>
      ((coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q :
        X'.Opens) : Set ↥X'))
    (fun q => (coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q).isOpen)
    hsub
  refine ⟨⟨⟨{ q : AdaptedEtaleChart p τ c ⊕ DisjointEtaleChart p τ // q ∈ t }, inferInstance,
    fun q => coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q.1,
    fun q => coverHypersurfaceIdeal (fun a : AdaptedEtaleChart p τ c => a)
      (fun b : DisjointEtaleChart p τ => b) q.1⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨q, hqt, hq⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact Set.mem_iUnion.2 ⟨⟨q, hqt⟩, hq⟩
  · rintro ⟨A | F, _⟩
    · exact A.isAffine
    · exact F.isAffine
  · rintro ⟨A | F, _⟩
    · exact ⟨A.coordCount, ⟨A.chart⟩⟩
    · exact ⟨F.coordCount, ⟨F.chart⟩⟩
  · rintro ⟨A | F, _⟩
    · exact Or.inr ⟨A.coordCount, A.chart, A.coord, rfl⟩
    · exact Or.inl rfl
  · rintro ⟨A | F, _⟩
    · exact Or.inr ⟨A.coordCount, A.chart, A.idxSet, A.coord, A.card_idxSet, A.coord_mem,
        A.restrictIdeal_ker, rfl⟩
    · exact Or.inl ⟨rfl, F.not_mem⟩

namespace MaximalContactCover

variable {X X' : Scheme.{u}} {k : Type u} [Field k] {p : X' ⟶ Spec (CommRingCat.of k)}
  {τ : X ⟶ X'} {I : X.IdealSheafData} {c : ℕ}

abbrev projection (C : MaximalContactCover p τ I c) : C.toCoverData.disjointUnion ⟶ X' :=
  C.toCoverData.disjointUnionMap

@[simp] theorem projection_eq (C : MaximalContactCover p τ I c) :
    C.projection = C.toCoverData.disjointUnionMap := rfl

theorem isAffine_disjointUnion (C : MaximalContactCover p τ I c) : IsAffine C.toCoverData.disjointUnion :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.isAffine_disjointUnion C.toCoverData C.isAffine

instance instIsAffineTotal (C : MaximalContactCover p τ I c) : IsAffine C.toCoverData.disjointUnion :=
  C.isAffine_disjointUnion

theorem quasiCompact_projection_comp (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.QuasiCompact (C.projection ≫ p) :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.quasiCompact_disjointUnionMap_comp C.toCoverData C.isAffine

instance instQuasiCompactProjComp (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.QuasiCompact (C.projection ≫ p) :=
  C.quasiCompact_projection_comp

theorem smooth_projection_comp (C : MaximalContactCover p τ I c) [AlgebraicGeometry.Smooth p] :
    AlgebraicGeometry.Smooth (C.projection ≫ p) := by
  have h : AlgebraicGeometry.Smooth C.toCoverData.disjointUnionMap :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.smooth_disjointUnionMap C.toCoverData
  exact MorphismProperty.comp_mem (@AlgebraicGeometry.Smooth) C.toCoverData.disjointUnionMap p h
    inferInstance

instance instSmoothProjComp (C : MaximalContactCover p τ I c) [AlgebraicGeometry.Smooth p] :
    AlgebraicGeometry.Smooth (C.projection ≫ p) :=
  C.smooth_projection_comp

theorem locallyOfFiniteType_projection_comp (C : MaximalContactCover p τ I c)
    [AlgebraicGeometry.LocallyOfFiniteType p] :
    AlgebraicGeometry.LocallyOfFiniteType (C.projection ≫ p) := by
  have h1 : AlgebraicGeometry.LocallyOfFiniteType C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.locallyOfFiniteType_disjointUnionMap C.toCoverData
  exact MorphismProperty.comp_mem (@AlgebraicGeometry.LocallyOfFiniteType) C.projection p h1
    inferInstance

instance instLocallyOfFiniteTypeProjComp (C : MaximalContactCover p τ I c)
    [AlgebraicGeometry.LocallyOfFiniteType p] :
    AlgebraicGeometry.LocallyOfFiniteType (C.projection ≫ p) :=
  C.locallyOfFiniteType_projection_comp

theorem isSmoothDivisor_iInfImageIdeal (C : MaximalContactCover p τ I c) :
    IsSmoothDivisor (C.projection ≫ p) C.toCoverData.iInfImageIdeal :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.isSmoothDivisor_iInfImageIdeal_of_forall_eq_top_or_coordIdeal C.toCoverData C.hypersurface C.hasChart

theorem surjective_projection (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Surjective C.projection :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.surjective_disjointUnionMap C.toCoverData C.covers

abbrev pullbackFiber (C : MaximalContactCover p τ I c) : Scheme.{u} :=
  Limits.pullback τ C.projection

abbrev pullbackFiberToTotal (C : MaximalContactCover p τ I c) : C.pullbackFiber ⟶ C.toCoverData.disjointUnion :=
  Limits.pullback.snd τ C.projection

abbrev pullbackFiberToBase (C : MaximalContactCover p τ I c) : C.pullbackFiber ⟶ X :=
  Limits.pullback.fst τ C.projection

theorem isPullback_pullbackFiber (C : MaximalContactCover p τ I c) :
    IsPullback C.pullbackFiberToBase C.pullbackFiberToTotal τ C.projection :=
  IsPullback.of_hasPullback τ C.projection

theorem isClosedImmersion_pullbackFiberToTotal (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsClosedImmersion C.pullbackFiberToTotal := by
  have h : IsClosedImmersion τ := inferInstance
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.IsClosedImmersion) C.isPullback_pullbackFiber h

instance instIsClosedImmersionStarEmb (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsClosedImmersion C.pullbackFiberToTotal :=
  C.isClosedImmersion_pullbackFiberToTotal

theorem flat_pullbackFiberToBase (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Flat C.pullbackFiberToBase := by
  have h : AlgebraicGeometry.Flat C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.flat_disjointUnionMap C.toCoverData
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Flat) C.isPullback_pullbackFiber.flip h

instance instFlatStarToBase (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Flat C.pullbackFiberToBase :=
  C.flat_pullbackFiberToBase

theorem smooth_pullbackFiberToBase (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Smooth C.pullbackFiberToBase := by
  have h : AlgebraicGeometry.Smooth C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.smooth_disjointUnionMap C.toCoverData
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Smooth) C.isPullback_pullbackFiber.flip h

instance instSmoothStarToBase (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Smooth C.pullbackFiberToBase :=
  C.smooth_pullbackFiberToBase

theorem surjective_pullbackFiberToBase (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Surjective C.pullbackFiberToBase := by
  have h : AlgebraicGeometry.Surjective C.projection := C.surjective_projection
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Surjective) C.isPullback_pullbackFiber.flip h

instance instSurjectiveStarToBase (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Surjective C.pullbackFiberToBase :=
  C.surjective_pullbackFiberToBase

theorem ker_pullbackFiberToTotal (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    Scheme.Hom.ker C.pullbackFiberToTotal = τ.ker.comap C.projection := by
  have hq : AlgebraicGeometry.QuasiCompact τ := inferInstance
  have hq' : AlgebraicGeometry.QuasiCompact C.pullbackFiberToTotal :=
    quasiCompact_of_isPullback C.isPullback_pullbackFiber
  have hf : AlgebraicGeometry.Flat C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.flat_disjointUnionMap C.toCoverData
  exact ker_eq_comap_ker_of_isPullback_of_flat C.isPullback_pullbackFiber

theorem exists_factor_pullbackFiberToTotal (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    ∃ f : C.pullbackFiber ⟶ C.toCoverData.iInfImageIdeal.subscheme,
      f ≫ C.toCoverData.iInfImageIdeal.subschemeι = C.pullbackFiberToTotal := by
  have hle : C.toCoverData.iInfImageIdeal ≤ Scheme.Hom.ker C.pullbackFiberToTotal := by
    have hker : Scheme.Hom.ker C.pullbackFiberToTotal
        = (Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap := C.ker_pullbackFiberToTotal
    rw [hker]
    refine MaxContactReduction.FiniteOpenCoverWithIdeals.le_of_comap_summandι_le C.toCoverData ?_
    intro i
    have e1 : C.toCoverData.iInfImageIdeal.comap (C.toCoverData.summandι i)
        = C.toCoverData.localIdeal i :=
      MaxContactReduction.FiniteOpenCoverWithIdeals.comap_iInfImageIdeal_summandι C.toCoverData i
    have e2 : ((Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap).comap
          (C.toCoverData.summandι i)
        = restrictIdeal (Scheme.Hom.ker τ) (C.toCoverData.opens i) := by
      rw [← Scheme.IdealSheafData.comap_comp,
        MaxContactReduction.FiniteOpenCoverWithIdeals.summandι_comp_disjointUnionMap, restrictIdeal_eq_comap_ι]
    rw [e1, e2]
    rcases C.adapted i with ⟨htop, hnot⟩ | ⟨n, ch, S, j, hcard, hjS, hrestrict, hloc⟩
    · exact le_of_eq (htop.trans (restrictIdeal_ker_eq_top_of_not_mem τ _ hnot).symm)
    · rw [hloc, hrestrict]
      exact ch.coordIdeal_mono (Finset.singleton_subset_iff.mpr hjS)
  have hle' : Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι
      ≤ Scheme.Hom.ker C.pullbackFiberToTotal := by
    rwa [Scheme.IdealSheafData.ker_subschemeι]
  exact ⟨IsClosedImmersion.lift C.toCoverData.iInfImageIdeal.subschemeι C.pullbackFiberToTotal hle',
    IsClosedImmersion.lift_fac C.toCoverData.iInfImageIdeal.subschemeι C.pullbackFiberToTotal hle'⟩

def pullbackFiberToHypersurface (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    C.pullbackFiber ⟶ C.toCoverData.iInfImageIdeal.subscheme :=
  (C.exists_factor_pullbackFiberToTotal).choose

theorem pullbackFiberToHypersurface_comp_subschemeι (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    C.pullbackFiberToHypersurface ≫ C.toCoverData.iInfImageIdeal.subschemeι = C.pullbackFiberToTotal :=
  (C.exists_factor_pullbackFiberToTotal).choose_spec

theorem pullbackFiberToHypersurface_comp_subschemeι_assoc (C : MaximalContactCover p τ I c) [IsClosedImmersion τ]
    {Z : Scheme.{u}} (h : C.toCoverData.disjointUnion ⟶ Z) :
    C.pullbackFiberToHypersurface ≫ C.toCoverData.iInfImageIdeal.subschemeι ≫ h = C.pullbackFiberToTotal ≫ h := by
  rw [← Category.assoc, C.pullbackFiberToHypersurface_comp_subschemeι]

private theorem isClosedImmersion_pullbackFiberToHypersurface_comp_subschemeι (C : MaximalContactCover p τ I c)
    [IsClosedImmersion τ] :
    IsClosedImmersion (C.pullbackFiberToHypersurface ≫ C.toCoverData.iInfImageIdeal.subschemeι) := by
  rw [C.pullbackFiberToHypersurface_comp_subschemeι]
  infer_instance

theorem isClosedImmersion_pullbackFiberToHypersurface (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsClosedImmersion C.pullbackFiberToHypersurface := by
  have := isClosedImmersion_pullbackFiberToHypersurface_comp_subschemeι C
  exact AlgebraicGeometry.IsClosedImmersion.of_comp C.pullbackFiberToHypersurface
    C.toCoverData.iInfImageIdeal.subschemeι

instance instIsClosedImmersionStarFactor (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsClosedImmersion C.pullbackFiberToHypersurface :=
  C.isClosedImmersion_pullbackFiberToHypersurface

def comapImageIdealSheaf (C : MaximalContactCover p τ I c) : C.toCoverData.disjointUnion.IdealSheafData :=
  (imageIdealSheaf τ I).comap C.projection

theorem comapImageIdealSheaf_eq (C : MaximalContactCover p τ I c) :
    C.comapImageIdealSheaf = (imageIdealSheaf τ I).comap C.projection := rfl

def idealOnHypersurface (C : MaximalContactCover p τ I c) :
    C.toCoverData.iInfImageIdeal.subscheme.IdealSheafData :=
  C.comapImageIdealSheaf.comap C.toCoverData.iInfImageIdeal.subschemeι

theorem idealOnHypersurface_eq_comap (C : MaximalContactCover p τ I c) :
    C.idealOnHypersurface = C.comapImageIdealSheaf.comap C.toCoverData.iInfImageIdeal.subschemeι := rfl

private theorem localIdeal_le_restrictIdeal_ker (C : MaximalContactCover p τ I c) [IsClosedImmersion τ]
    (i : C.toCoverData.idx) :
    C.toCoverData.localIdeal i ≤ restrictIdeal (Scheme.Hom.ker τ) (C.toCoverData.opens i) := by
  rcases C.adapted i with ⟨htop, hnot⟩ | ⟨n, ch, S, j, hcard, hjS, hker, hloc⟩
  · have h1 := restrictIdeal_ker_eq_top_of_not_mem τ (C.toCoverData.opens i) hnot
    rw [htop]
    exact h1.ge
  · rw [hloc, hker]
    exact ch.coordIdeal_mono (Finset.singleton_subset_iff.mpr hjS)

private theorem iInfImageIdeal_le_comap_ker (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    C.toCoverData.iInfImageIdeal ≤ (Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap := by
  refine MaxContactReduction.FiniteOpenCoverWithIdeals.le_of_comap_summandι_le C.toCoverData ?_
  intro i
  rw [MaxContactReduction.FiniteOpenCoverWithIdeals.comap_iInfImageIdeal_summandι,
    ← Scheme.IdealSheafData.comap_comp,
    MaxContactReduction.FiniteOpenCoverWithIdeals.summandι_comp_disjointUnionMap]
  exact localIdeal_le_restrictIdeal_ker C i

theorem comapImageIdealSheaf_eq_imageIdealSheaf_idealOnHypersurface (C : MaximalContactCover p τ I c)
    [IsClosedImmersion τ] :
    C.comapImageIdealSheaf = imageIdealSheaf C.toCoverData.iInfImageIdeal.subschemeι C.idealOnHypersurface := by
  have hG : Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι = C.toCoverData.iInfImageIdeal := by
    simp
  have hle : Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι ≤ C.comapImageIdealSheaf := by
    rw [hG, C.comapImageIdealSheaf_eq]
    exact le_trans (iInfImageIdeal_le_comap_ker C)
      (Scheme.IdealSheafData.comap_mono C.projection (ker_le_map_idealSheaf τ I))
  have h2 := ker_subschemeι_comp_eq_of_ker_le C.toCoverData.iInfImageIdeal.subschemeι C.comapImageIdealSheaf hle
    C.idealOnHypersurface C.idealOnHypersurface_eq_comap
  exact h2.symm

theorem idealOnHypersurface_eq_imageIdealSheaf (C : MaximalContactCover p τ I c)
    [IsClosedImmersion τ] :
    C.idealOnHypersurface = imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase) := by
  have hqc : AlgebraicGeometry.QuasiCompact τ := inferInstance
  have hflat : AlgebraicGeometry.Flat C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.flat_disjointUnionMap C.toCoverData
  have h1 : (imageIdealSheaf τ I).comap C.projection
      = imageIdealSheaf C.pullbackFiberToTotal (I.comap C.pullbackFiberToBase) :=
    comap_map_eq_map_comap_of_isPullback C.isPullback_pullbackFiber I
  have h2 : imageIdealSheaf C.pullbackFiberToTotal (I.comap C.pullbackFiberToBase)
      = imageIdealSheaf C.toCoverData.iInfImageIdeal.subschemeι
          (imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)) := by
    have h := Scheme.IdealSheafData.map_comp (I.comap C.pullbackFiberToBase) C.pullbackFiberToHypersurface
      C.toCoverData.iInfImageIdeal.subschemeι
    rw [C.pullbackFiberToHypersurface_comp_subschemeι] at h
    exact h
  have h3 : (imageIdealSheaf C.toCoverData.iInfImageIdeal.subschemeι
        (imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase))).comap
        C.toCoverData.iInfImageIdeal.subschemeι
      = imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase) :=
    Blowup.comap_map_of_isClosedImmersion
      C.toCoverData.iInfImageIdeal.subschemeι (imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase))
  rw [C.idealOnHypersurface_eq_comap, C.comapImageIdealSheaf_eq, h1, h2, h3]

end MaximalContactCover

end FunctorialResolution.EmbeddedResolution

end
