import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.IrreducibleComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.StrictTransformAvoidance
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineResolutionConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedLocus
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem range_base_subschemeι {X : Scheme.{u}} (I : X.IdealSheafData) :
    Set.range ⇑I.subschemeι.base = ((I.support : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
  rw [Scheme.IdealSheafData.range_subschemeι]

private theorem mem_of_mem_support_vanishingIdeal {W : Scheme.{u}} (Z : TopologicalSpace.Closeds ↥W)
    (x : ↥W) (hx : x ∈ (Scheme.IdealSheafData.vanishingIdeal Z).support) : x ∈ (Z : Set ↥W) := by
  have h2 : x ∈ (((Scheme.IdealSheafData.vanishingIdeal Z).support :
      TopologicalSpace.Closeds ↥W) : Set ↥W) := hx
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at h2
  exact h2

private theorem exists_iso_subscheme_vanishingIdeal_of_closure_range {A W : Scheme.{u}} (f : A ⟶ W)
    [AlgebraicGeometry.IsClosedImmersion f] [AlgebraicGeometry.IsReduced A]
    (K : TopologicalSpace.Closeds ↥W)
    (hK : (K : Set ↥W) = closure (Set.range ⇑f.base))
    (hle : Scheme.Hom.ker f ≤ Scheme.IdealSheafData.vanishingIdeal K) :
    ∃ e : (Scheme.IdealSheafData.vanishingIdeal K).subscheme ≅ A,
      e.hom ≫ f = (Scheme.IdealSheafData.vanishingIdeal K).subschemeι := by
  have hrange : Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal K).subschemeι.base
      = (K : Set ↥W) := by
    rw [range_base_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hle' : Scheme.Hom.ker f
      ≤ Scheme.Hom.ker (Scheme.IdealSheafData.vanishingIdeal K).subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact hle
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Scheme.IdealSheafData.vanishingIdeal K).subscheme ⟶ A,
      ψ ≫ f = (Scheme.IdealSheafData.vanishingIdeal K).subschemeι :=
    ⟨IsClosedImmersion.lift f (Scheme.IdealSheafData.vanishingIdeal K).subschemeι hle',
      IsClosedImmersion.lift_fac _ _ hle'⟩
  have hψbase : ∀ x, f.base (ψ.base x)
      = (Scheme.IdealSheafData.vanishingIdeal K).subschemeι.base x := by
    intro x
    show (ψ ≫ f).base x = (Scheme.IdealSheafData.vanishingIdeal K).subschemeι.base x
    rw [hψ]
  have hinj : Function.Injective ⇑f.base := f.isEmbedding.injective
  have hsurj : Function.Surjective ⇑ψ.base := by
    intro a
    have h1 : f.base a ∈ (K : Set ↥W) := by
      rw [hK]
      exact subset_closure (Set.mem_range_self a)
    rw [← hrange] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨y, hinj (by rw [hψbase y]; exact hy)⟩
  have hru : Set.range ⇑ψ.base = (Set.univ : Set ↥A) := hsurj.range_eq
  have : IsPreimmersion (ψ ≫ f) := by rw [hψ]; infer_instance
  have : IsPreimmersion ψ := IsPreimmersion.of_comp ψ f
  have : IsClosedImmersion ψ :=
    IsClosedImmersion.of_isPreimmersion ψ (by rw [hru]; exact isClosed_univ)
  have hker : Scheme.Hom.ker ψ = ⊥ := by
    rw [← Scheme.IdealSheafData.support_eq_top_iff]
    refine TopologicalSpace.Closeds.ext ?_
    rw [Scheme.Hom.support_ker, hru, closure_univ]
    simp
  have : IsIso ψ := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  exact ⟨asIso ψ, hψ⟩

theorem exists_iso_of_range_base_eq {A B W : Scheme.{u}} (f : A ⟶ W) (g : B ⟶ W)
    [AlgebraicGeometry.IsClosedImmersion f] [AlgebraicGeometry.IsClosedImmersion g]
    [AlgebraicGeometry.IsReduced A] [AlgebraicGeometry.IsReduced B]
    (h : Set.range ⇑f.base = Set.range ⇑g.base) :
    ∃ e : A ≅ B, e.hom ≫ g = f := by
  have hA : ((Scheme.Hom.ker f).support : Set ↥W) = closure (Set.range ⇑f.base) :=
    Scheme.Hom.support_ker f
  have hB : ((Scheme.Hom.ker f).support : Set ↥W) = closure (Set.range ⇑g.base) := by
    rw [Scheme.Hom.support_ker f, h]
  have hKeq : (Scheme.Hom.ker g).support = (Scheme.Hom.ker f).support :=
    TopologicalSpace.Closeds.ext (by rw [Scheme.Hom.support_ker g, hB])
  obtain ⟨e₁, he₁⟩ := exists_iso_subscheme_vanishingIdeal_of_closure_range f (Scheme.Hom.ker f).support hA
    (by rw [Scheme.IdealSheafData.vanishingIdeal_support]
        exact Scheme.IdealSheafData.le_radical _)
  obtain ⟨e₂, he₂⟩ := exists_iso_subscheme_vanishingIdeal_of_closure_range g (Scheme.Hom.ker f).support hB
    (by rw [← hKeq, Scheme.IdealSheafData.vanishingIdeal_support]
        exact Scheme.IdealSheafData.le_radical _)
  refine ⟨e₁.symm ≪≫ e₂, ?_⟩
  have hcomp : (e₁.symm ≪≫ e₂).hom = e₁.inv ≫ e₂.hom := rfl
  rw [hcomp, Category.assoc, he₂, ← he₁, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem isNoetherian_ambientLevel_ofAffine (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] (pY : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] :
    ∀ i ≤ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength,
      AlgebraicGeometry.IsNoetherian ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i) := by
  intro i hi
  have h := EmbeddedBlowupSequence.isNoetherian_schemeAt
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence i hi
  rw [AffineSpacePrincipalizationData.toEmbeddedBlowupSequence_schemeAt] at h
  exact h

private theorem mem_support_of_le {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J)
    (x : ↥X) (hx : x ∈ J.support) : x ∈ I.support :=
  (mem_orderAtLeastLocus_one_iff I x).mp
    (orderAtLeastLocus_subset_of_le_ideal h 1 ((mem_orderAtLeastLocus_one_iff J x).mpr hx))

private theorem mem_support_mul {X : Scheme.{u}} (I J : X.IdealSheafData) (x : ↥X) :
    x ∈ (I * J).support ↔ x ∈ I.support ∨ x ∈ J.support := by
  have h : (((I * J).support : TopologicalSpace.Closeds ↥X) : Set ↥X)
      = ((I.support : TopologicalSpace.Closeds ↥X) : Set ↥X)
        ∪ ((J.support : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
    simp
  constructor
  · intro hx
    have h2 : x ∈ (((I * J).support : TopologicalSpace.Closeds ↥X) : Set ↥X) := hx
    rw [h] at h2
    exact h2
  · intro hx
    have h2 : x ∈ (((I * J).support : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
      rw [h]
      exact hx
    exact h2

private theorem mem_support_comap {X Z : Scheme.{u}} (f : X ⟶ Z) (I : Z.IdealSheafData) (x : ↥X) :
    x ∈ (I.comap f).support ↔ ⇑f.base x ∈ I.support := by
  constructor
  · intro hx
    have h : x ∈ ((((I.comap f)).support : TopologicalSpace.Closeds ↥X) : Set ↥X) := hx
    rw [support_comap_eq] at h
    exact h
  · intro hx
    have h : x ∈ ((((I.comap f)).support : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
      rw [support_comap_eq]
      exact hx
    exact h

private theorem exists_mem_list_subset_of_isIrreducible {α : Type*} [TopologicalSpace α] {ι : Type*}
    {s : Set α} (hs : IsIrreducible s) (g : ι → Set α) :
    ∀ L : List ι, (∀ t ∈ L, IsClosed (g t)) → s ⊆ (⋃ t ∈ L, g t) → ∃ t ∈ L, s ⊆ g t := by
  intro L
  induction L with
  | nil =>
      intro _ hsub
      obtain ⟨x, hx⟩ := hs.nonempty
      obtain ⟨t, ht, -⟩ := Set.mem_iUnion₂.mp (hsub hx)
      simp at ht
  | cons a L ih =>
      intro hcl hsub
      have hsub' : s ⊆ g a ∪ ⋃ t ∈ L, g t := by
        intro z hz
        obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.mp (hsub hz)
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact Or.inl hzt
        · exact Or.inr (Set.mem_biUnion ht' hzt)
      have hacl : IsClosed (g a) := hcl a (List.mem_cons.mpr (Or.inl rfl))
      have hUcl : IsClosed (⋃ t ∈ L, g t) :=
        Set.Finite.isClosed_biUnion L.finite_toSet
          (fun t ht => hcl t (List.mem_cons.mpr (Or.inr ht)))
      rcases isPreirreducible_iff_isClosed_union_isClosed.mp hs.2 _ _ hacl hUcl hsub' with h | h
      · exact ⟨a, List.mem_cons.mpr (Or.inl rfl), h⟩
      · obtain ⟨t, ht, hts⟩ := ih (fun t ht => hcl t (List.mem_cons.mpr (Or.inr ht))) h
        exact ⟨t, List.mem_cons.mpr (Or.inr ht), hts⟩

private theorem quasiCompact_strictTransformImmersion {X' X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace ↥X'] (π : X' ⟶ X) (Z J : X.IdealSheafData) :
    AlgebraicGeometry.QuasiCompact (Blowup.strictTransformImmersion π Z J) := by
  have : AlgebraicGeometry.IsPreimmersion (Blowup.strictTransformImmersion π Z J) := by
    rw [Blowup.strictTransformImmersion_eq]
    infer_instance
  refine ⟨fun U _ _ => ?_⟩
  refine ((Blowup.strictTransformImmersion π Z J).isEmbedding.isInducing.isCompact_iff).mpr ?_
  exact TopologicalSpace.NoetherianSpace.isCompact _

private theorem mem_support_strictTransform {X' X : Scheme.{u}} (π : X' ⟶ X)
    (Z J : X.IdealSheafData)
    (hqc : AlgebraicGeometry.QuasiCompact (Blowup.strictTransformImmersion π Z J)) (x : ↥X')
    (h1 : ⇑π.base x ∈ J.support) (h2 : ⇑π.base x ∉ Z.support) :
    x ∈ (Blowup.strictTransform π Z J).support := by
  have := hqc
  have hxr : x ∈ Set.range ⇑(J.comap π).subschemeι.base := by
    rw [range_base_subschemeι]
    exact (mem_support_comap π J x).mpr h1
  obtain ⟨y, hy⟩ := hxr
  have h3 : ⇑(J.comap π).subschemeι.base y ∉ (Z.comap π).support := by
    intro hc
    have h5 := (mem_support_comap π Z _).mp hc
    rw [hy] at h5
    exact h2 h5
  have hyo : y ∈ Blowup.strictTransformOpens π Z J := by
    rw [Blowup.strictTransformOpens_eq]
    have h4 : ⇑(J.comap π).subschemeι.base y
        ∉ ((((Z.comap π)).support : TopologicalSpace.Closeds ↥X') : Set ↥X') := h3
    exact h4
  have hyr : y ∈ Set.range ⇑(Blowup.strictTransformOpens π Z J).ι.base := by
    have hrι : Set.range ⇑(Blowup.strictTransformOpens π Z J).ι.base
        = ((Blowup.strictTransformOpens π Z J : (J.comap π).subscheme.Opens) :
            Set ↥(J.comap π).subscheme) := (Blowup.strictTransformOpens π Z J).range_ι
    rw [hrι]
    exact hyo
  obtain ⟨y', hy'⟩ := hyr
  have hcomp : ⇑(Blowup.strictTransformImmersion π Z J).base y' = x := by
    rw [Blowup.strictTransformImmersion_eq]
    show ⇑(J.comap π).subschemeι.base (⇑(Blowup.strictTransformOpens π Z J).ι.base y') = x
    rw [hy', hy]
  have hfin : x ∈ ((((Blowup.strictTransform π Z J)).support : TopologicalSpace.Closeds ↥X')
      : Set ↥X') := by
    rw [Blowup.strictTransform_eq_ker, Scheme.Hom.support_ker]
    exact subset_closure ⟨y', hcomp⟩
  exact hfin

private def principalizationSequenceIdeal {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) (j : ℕ) :
    (S.ambientLevel j).IdealSheafData :=
  S.principalizationSequence.ideal j

private theorem exceptionalIdeal_mul_weakTransform_succ {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) (j : ℕ)
    (hj : j < S.ambientLength) :
    Blowup.exceptionalIdeal (S.ambientBlowupMorphism j) (S.ambientCenter j) * principalizationSequenceIdeal S (j + 1)
      = (principalizationSequenceIdeal S j).comap (S.ambientBlowupMorphism j) :=
  S.principalizationSequence.ideal_succ j hj

private theorem weakTransform_le_ambientCenter {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) (j : ℕ)
    (hj : j < S.ambientLength) : principalizationSequenceIdeal S j ≤ S.ambientCenter j :=
  (vanishesAlong_iff_le _ _).mp (S.principalizationSequence.ideal_vanishes j hj)

private theorem boundary_succ_eq {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) (j : ℕ)
    (hj : j < S.ambientLength) :
    S.boundary (j + 1)
      = List.map (Blowup.strictTransform (S.ambientBlowupMorphism j) (S.ambientCenter j)) (S.boundary j)
        ++ [Blowup.exceptionalIdeal (S.ambientBlowupMorphism j) (S.ambientCenter j)] :=
  S.principalizationSequence.boundary_succ j hj

private theorem mem_range_strictTransformι_iff {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) (j : ℕ)
    (x : ↥(S.ambientLevel j)) :
    x ∈ Set.range ⇑(S.strictTransformι j).base ↔ x ∈ (S.strictTransformIdeal j).support := by
  have h : Set.range ⇑(S.strictTransformι j).base
      = (((S.strictTransformIdeal j).support : TopologicalSpace.Closeds ↥(S.ambientLevel j))
          : Set ↥(S.ambientLevel j)) := by
    rw [S.strictTransformι_eq_subschemeι j]
    exact range_base_subschemeι _
  constructor
  · intro hx
    have h2 : x ∈ Set.range ⇑(S.strictTransformι j).base := hx
    rw [h] at h2
    exact h2
  · intro hx
    have h2 : x ∈ (((S.strictTransformIdeal j).support : TopologicalSpace.Closeds ↥(S.ambientLevel j))
        : Set ↥(S.ambientLevel j)) := hx
    rw [← h] at h2
    exact h2

private theorem support_weakTransform_subset_range_or_boundary {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY)
    (hN : ∀ j ≤ S.ambientLength, AlgebraicGeometry.IsNoetherian (S.ambientLevel j))
    (hbase : ∀ x : ↥(S.ambientLevel 0), x ∈ (principalizationSequenceIdeal S 0).support →
      x ∈ Set.range ⇑(S.strictTransformι 0).base) :
    ∀ j ≤ S.ambientLength, ∀ x : ↥(S.ambientLevel j), x ∈ (principalizationSequenceIdeal S j).support →
      x ∈ Set.range ⇑(S.strictTransformι j).base ∨ ∃ E ∈ S.boundary j, x ∈ E.support := by
  intro j
  induction j with
  | zero =>
      intro _ x hx
      exact Or.inl (hbase x hx)
  | succ j ih =>
      intro hj x hx
      have hjlt : j < S.ambientLength := hj
      have hNs : AlgebraicGeometry.IsNoetherian (S.ambientLevel (j + 1)) := hN (j + 1) hj
      have hNSs : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (j + 1)) := inferInstance
      have hxp : x ∈ (Blowup.exceptionalIdeal (S.ambientBlowupMorphism j) (S.ambientCenter j)
          * principalizationSequenceIdeal S (j + 1)).support :=
        (mem_support_mul (Blowup.exceptionalIdeal (S.ambientBlowupMorphism j) (S.ambientCenter j))
          (principalizationSequenceIdeal S (j + 1)) x).mpr (Or.inr hx)
      rw [exceptionalIdeal_mul_weakTransform_succ S j hjlt] at hxp
      have hx1 : ⇑(S.ambientBlowupMorphism j).base x ∈ (principalizationSequenceIdeal S j).support :=
        (mem_support_comap (S.ambientBlowupMorphism j) (principalizationSequenceIdeal S j) x).mp hxp
      by_cases hexc : x ∈ (Blowup.exceptionalIdeal (S.ambientBlowupMorphism j) (S.ambientCenter j)).support
      · have hmem1 : Blowup.exceptionalIdeal (S.ambientBlowupMorphism j) (S.ambientCenter j) ∈ S.boundary (j + 1) := by
          rw [boundary_succ_eq S j hjlt]
          simp
        exact Or.inr ⟨_, hmem1, hexc⟩
      · have hnc : ⇑(S.ambientBlowupMorphism j).base x ∉ (S.ambientCenter j).support := by
          intro hc
          apply hexc
          have h6 : x ∈ ((S.ambientCenter j).comap (S.ambientBlowupMorphism j)).support :=
            (mem_support_comap (S.ambientBlowupMorphism j) (S.ambientCenter j) x).mpr hc
          rw [Blowup.exceptionalIdeal_eq_comap]
          exact h6
        rcases ih (le_of_lt hjlt) (⇑(S.ambientBlowupMorphism j).base x) hx1 with hA | ⟨E, hE, hxE⟩
        · refine Or.inl ?_
          have h1 : ⇑(S.ambientBlowupMorphism j).base x ∈ (S.strictTransformIdeal j).support :=
            (mem_range_strictTransformι_iff S j _).mp hA
          have h2 := mem_support_strictTransform (S.ambientBlowupMorphism j) (S.ambientCenter j)
            (S.strictTransformIdeal j)
            (quasiCompact_strictTransformImmersion (S.ambientBlowupMorphism j) (S.ambientCenter j)
              (S.strictTransformIdeal j)) x h1 hnc
          refine (mem_range_strictTransformι_iff S (j + 1) x).mpr ?_
          rw [S.strictTransformIdeal_succ_eq_strictTransform j]
          exact h2
        · have hmem1 : Blowup.strictTransform (S.ambientBlowupMorphism j) (S.ambientCenter j) E
              ∈ S.boundary (j + 1) := by
            rw [boundary_succ_eq S j hjlt]
            simp only [List.mem_append, List.mem_map]
            exact Or.inl ⟨E, hE, rfl⟩
          have hmem2 := mem_support_strictTransform (S.ambientBlowupMorphism j) (S.ambientCenter j) E
            (quasiCompact_strictTransformImmersion (S.ambientBlowupMorphism j) (S.ambientCenter j) E) x hxE hnc
          exact Or.inr ⟨_, hmem1, hmem2⟩

private theorem detachedClopenInCenter_of_isNoetherian_of_support {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY)
    (hN : ∀ j ≤ S.ambientLength, AlgebraicGeometry.IsNoetherian (S.ambientLevel j))
    (hsupp : ∀ j ≤ S.ambientLength, ∀ x : ↥(S.ambientLevel j), x ∈ (principalizationSequenceIdeal S j).support →
      x ∈ Set.range ⇑(S.strictTransformι j).base ∨ ∃ E ∈ S.boundary j, x ∈ E.support)
    (hmk : ∀ j ≤ S.ambientLength, ∀ C ∈ irreducibleComponents ↥(S.strictTransform j), ∀ E ∈ S.boundary j,
      ¬ (⇑(S.strictTransformι j).base '' C ⊆
        ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel j)) : Set ↥(S.ambientLevel j)))) :
    S.DetachedClopenInCenter := by
  intro i hi
  have hNi : AlgebraicGeometry.IsNoetherian (S.ambientLevel i) := hN i hi.le
  have hNSi : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel i) := inferInstance
  have hnoeth : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) :=
    S.noetherianSpace_strictTransform_of_ambientLevel i hNSi
  have hsmW : AlgebraicGeometry.Smooth
      ((S.ambientCenter i).subschemeι ≫ S.schemeAtToSpec i) := S.principalizationSequence.smooth_center_subschemeι i hi
  have hredW : AlgebraicGeometry.IsReduced (S.ambientCenter i).subscheme :=
    smooth_isReduced ((S.ambientCenter i).subschemeι ≫ S.schemeAtToSpec i) hsmW
  have hNW : TopologicalSpace.NoetherianSpace ↥(S.ambientCenter i).subscheme := inferInstance
  have hrangeA : Set.range ⇑(S.strictTransformι i).base
      = (((S.strictTransformIdeal i).support : TopologicalSpace.Closeds ↥(S.ambientLevel i))
          : Set ↥(S.ambientLevel i)) := by
    rw [S.strictTransformι_eq_subschemeι i]
    exact range_base_subschemeι _
  have hrangeC : Set.range ⇑((S.ambientCenter i).subschemeι).base
      = (((S.ambientCenter i).support : TopologicalSpace.Closeds ↥(S.ambientLevel i))
          : Set ↥(S.ambientLevel i)) :=
    range_base_subschemeι _
  have hdom : ∀ x : ↥(S.ambientCenter i).subscheme,
      IsDomain (((S.ambientCenter i).subscheme).presheaf.stalk x) := fun x =>
    smooth_isDomain_stalk ((S.ambientCenter i).subschemeι ≫ S.schemeAtToSpec i) hsmW x
  have hsubr : ⇑(S.strictTransformι i).base '' S.discardedLocus i
      ⊆ Set.range ⇑((S.ambientCenter i).subschemeι).base := by
    rw [hrangeC]
    exact S.image_discardedLocus_subset_support i
  have hRcl : IsClosed (Set.range ⇑(S.strictTransformι i).base ∪
      ⋃ E ∈ S.boundary i,
        ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i))) := by
    refine IsClosed.union ?_ ?_
    · rw [hrangeA]
      exact ((S.strictTransformIdeal i).support).2
    · exact Set.Finite.isClosed_biUnion (S.boundary i).finite_toSet (fun E _ => (E.support).2)
  have hcomp : ∀ C ∈ S.discardedComponents i,
      ⇑((S.ambientCenter i).subschemeι).base ⁻¹' (⇑(S.strictTransformι i).base '' C)
        ∈ irreducibleComponents ↥(S.ambientCenter i).subscheme := by
    intro C hC
    obtain ⟨hCcomp, hCsub⟩ := (S.mem_discardedComponents_iff i C).mp hC
    have himg : IsIrreducible (⇑(S.strictTransformι i).base '' C) :=
      hCcomp.1.image _ ((S.strictTransformι i).continuous).continuousOn
    have hsubrC : ⇑(S.strictTransformι i).base '' C
        ⊆ Set.range ⇑((S.ambientCenter i).subschemeι).base := by
      rw [hrangeC]
      exact hCsub
    refine ⟨isIrreducible_preimage_of_isEmbedding
      ((S.ambientCenter i).subschemeι.isEmbedding) himg hsubrC, ?_⟩
    intro s hs hKle
    have hcimg : ⇑((S.ambientCenter i).subschemeι).base ''
        (⇑((S.ambientCenter i).subschemeι).base ⁻¹' (⇑(S.strictTransformι i).base '' C))
        = ⇑(S.strictTransformι i).base '' C := Set.image_preimage_eq_of_subset hsubrC
    have hFirr : IsIrreducible (closure (⇑((S.ambientCenter i).subschemeι).base '' s)) :=
      (hs.image _ (((S.ambientCenter i).subschemeι).continuous).continuousOn).closure
    have hCsubF : ⇑(S.strictTransformι i).base '' C
        ⊆ closure (⇑((S.ambientCenter i).subschemeι).base '' s) := by
      rw [← hcimg]
      exact (Set.image_mono hKle).trans subset_closure
    have hcsI : ⇑((S.ambientCenter i).subschemeι).base '' s
        ⊆ Set.range ⇑(S.strictTransformι i).base ∪
          ⋃ E ∈ S.boundary i,
            ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i)) := by
      intro z hz
      obtain ⟨w, -, rfl⟩ := hz
      have h1 : ⇑((S.ambientCenter i).subschemeι).base w ∈ (S.ambientCenter i).support := by
        have h0 : ⇑((S.ambientCenter i).subschemeι).base w
            ∈ (((S.ambientCenter i).support : TopologicalSpace.Closeds ↥(S.ambientLevel i))
                : Set ↥(S.ambientLevel i)) := by
          rw [← hrangeC]
          exact Set.mem_range_self w
        exact h0
      have h2 : ⇑((S.ambientCenter i).subschemeι).base w ∈ (principalizationSequenceIdeal S i).support :=
        mem_support_of_le (weakTransform_le_ambientCenter S i hi) _ h1
      rcases hsupp i hi.le _ h2 with hA | ⟨E, hE, hxE⟩
      · exact Or.inl hA
      · exact Or.inr (Set.mem_biUnion hE hxE)
    have hFsub : closure (⇑((S.ambientCenter i).subschemeι).base '' s)
        ⊆ Set.range ⇑(S.strictTransformι i).base ∪
          ⋃ E ∈ S.boundary i,
            ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i)) :=
      (IsClosed.closure_subset_iff hRcl).mpr hcsI
    rcases isPreirreducible_iff_isClosed_union_isClosed.mp hFirr.2 _ _
        (by rw [hrangeA]; exact ((S.strictTransformIdeal i).support).2)
        (Set.Finite.isClosed_biUnion (S.boundary i).finite_toSet (fun E _ => (E.support).2))
        hFsub with hcase | hcase
    · have hG := hCcomp.2
        (isIrreducible_preimage_of_isEmbedding ((S.strictTransformι i).isEmbedding) hFirr hcase)
        (fun z hz => hCsubF (Set.mem_image_of_mem _ hz))
      have hclosure : closure (⇑((S.ambientCenter i).subschemeι).base '' s)
          ⊆ ⇑(S.strictTransformι i).base '' C := by
        rw [← Set.image_preimage_eq_of_subset hcase]
        exact Set.image_mono hG
      intro z hz
      exact hclosure (subset_closure (Set.mem_image_of_mem _ hz))
    · obtain ⟨E, hE, hFsubE⟩ := exists_mem_list_subset_of_isIrreducible hFirr
        (fun E : (S.ambientLevel i).IdealSheafData =>
          ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i)))
        (S.boundary i) (fun E _ => (E.support).2) hcase
      exact ((hmk i hi.le C hCcomp E hE) (hCsubF.trans hFsubE)).elim
  have hPreimageDiscarded : ⇑((S.ambientCenter i).subschemeι).base ⁻¹'
      (⇑(S.strictTransformι i).base '' S.discardedLocus i)
      = ⋃₀ ((fun C : Set ↥(S.strictTransform i) =>
          ⇑((S.ambientCenter i).subschemeι).base ⁻¹' (⇑(S.strictTransformι i).base '' C))
            '' S.discardedComponents i) := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ := hz
      rw [S.discardedLocus_eq_sUnion_discardedComponents i] at hw
      obtain ⟨C, hC, hwC⟩ := hw
      exact ⟨_, ⟨C, hC, rfl⟩, ⟨w, hwC, hwz⟩⟩
    · intro hz
      obtain ⟨t, ⟨C, hC, rfl⟩, hzt⟩ := hz
      obtain ⟨w, hwC, hwz⟩ := hzt
      refine ⟨w, ?_, hwz⟩
      rw [S.discardedLocus_eq_sUnion_discardedComponents i]
      exact ⟨C, hC, hwC⟩
  have hopenU : IsOpen (⇑((S.ambientCenter i).subschemeι).base ⁻¹'
      (⇑(S.strictTransformι i).base '' S.discardedLocus i)) := by
    rw [hPreimageDiscarded]
    refine isOpen_sUnion_of_irreducibleComponents _ ?_
    · intro Zs hZs W hW hWnot
      obtain ⟨C, hC, rfl⟩ := hZs
      rw [Set.disjoint_left]
      intro z hz1 hz2
      have heqq := irreducibleComponents_eq_of_stalk_isDomain _ hdom (hcomp C hC) hW hz1 hz2
      refine hWnot ?_
      rw [← heqq]
      exact ⟨C, hC, rfl⟩
  have hembA : Topology.IsClosedEmbedding ⇑(S.strictTransformι i).base := by
    refine ⟨(S.strictTransformι i).isEmbedding, ?_⟩
    rw [hrangeA]
    exact ((S.strictTransformIdeal i).support).2
  have hclosedU : IsClosed (⇑((S.ambientCenter i).subschemeι).base ⁻¹'
      (⇑(S.strictTransformι i).base '' S.discardedLocus i)) :=
    (hembA.isClosedMap _ (S.isClosed_discardedLocus i)).preimage
      ((S.ambientCenter i).subschemeι).continuous
  obtain ⟨U, hUcoe⟩ : ∃ U : ((S.ambientCenter i).subscheme).Opens,
      (U : Set ↥(S.ambientCenter i).subscheme)
        = ⇑((S.ambientCenter i).subschemeι).base ⁻¹'
          (⇑(S.strictTransformι i).base '' S.discardedLocus i) :=
    ⟨⟨_, hopenU⟩, rfl⟩
  have hUcl : IsClosed ((U : Set ↥(S.ambientCenter i).subscheme)) := by
    rw [hUcoe]
    exact hclosedU
  have : AlgebraicGeometry.IsClosedImmersion U.ι :=
    Scheme.Opens.isClosedImmersion_ι_of_isClosed U hUcl
  have : AlgebraicGeometry.IsReduced (S.discardedIdeal i).subscheme := by
    rw [S.discardedIdeal_eq_vanishingIdeal i]
    exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _ _
  have hRangeDiscarded : Set.range ⇑(S.discardedι i).base = S.discardedLocus i := by
    have h1 : Set.range ⇑(S.discardedι i).base
        = (((S.discardedIdeal i).support : TopologicalSpace.Closeds ↥(S.strictTransform i))
            : Set ↥(S.strictTransform i)) := range_base_subschemeι _
    rw [h1, S.discardedIdeal_eq_vanishingIdeal i, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      S.coe_discardedLocusClosure i]
  have hrf : Set.range ⇑(S.discardedι i ≫ S.strictTransformι i).base
      = ⇑(S.strictTransformι i).base '' S.discardedLocus i := by
    rw [Scheme.Hom.range_comp_base, hRangeDiscarded]
  have hrU : Set.range ⇑U.ι.base = (U : Set ↥(S.ambientCenter i).subscheme) := U.range_ι
  have hrg : Set.range ⇑(U.ι ≫ (S.ambientCenter i).subschemeι).base
      = ⇑(S.strictTransformι i).base '' S.discardedLocus i := by
    rw [Scheme.Hom.range_comp_base, hrU, hUcoe]
    exact Set.image_preimage_eq_of_subset hsubr
  obtain ⟨e, he⟩ := exists_iso_of_range_base_eq (S.discardedι i ≫ S.strictTransformι i)
    (U.ι ≫ (S.ambientCenter i).subschemeι) (hrf.trans hrg.symm)
  exact ⟨U, hUcl, e, he⟩

private theorem detachedClopenInCenter_ofAffine (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] :
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).DetachedClopenInCenter := by
  have hN := isNoetherian_ambientLevel_ofAffine A hemb hsnc hsm k Y pY
  have hcl0 :
      IsClosed (Set.range ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι 0).base) := by
    rw [(AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι_eq_subschemeι 0, range_base_subschemeι]
    exact (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformIdeal 0).support).2
  have heq : principalizationSequenceIdeal (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) 0
      = Scheme.IdealSheafData.vanishingIdeal
        (⟨Set.range ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι 0).base, hcl0⟩ :
          TopologicalSpace.Closeds ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel 0)) :=
    OpenImmersionRestriction.principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal
      (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A hcl0
  have hbase : ∀ x : ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel 0),
      x ∈ (principalizationSequenceIdeal (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) 0).support →
        x ∈ Set.range ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι 0).base := by
    intro x hx
    rw [heq] at hx
    exact mem_of_mem_support_vanishingIdeal _ x hx
  refine detachedClopenInCenter_of_isNoetherian_of_support _ hN (support_weakTransform_subset_range_or_boundary _ hN hbase) ?_
  intro j hj C hC E hE
  exact OpenImmersionRestriction.not_image_irreducibleComponent_subset_boundary_support
    (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A j hj C hC E hE

theorem affineDetachedSmooth (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) :
    AffineDetachedSmooth A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _ i hi
  obtain ⟨T, hTcl, e, he⟩ := detachedClopenInCenter_ofAffine A hemb hsnc hsm k Y pY i hi
  have hsmC : AlgebraicGeometry.Smooth
      (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientCenter i).subschemeι
        ≫ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).schemeAtToSpec i) :=
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).principalizationSequence.smooth_center_subschemeι i hi
  have : AlgebraicGeometry.IsClosedImmersion T.ι :=
    Scheme.Opens.isClosedImmersion_ι_of_isClosed T hTcl
  have key := congrArg
    (fun m => m ≫ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).schemeAtToSpec i) he
  simp only [Category.assoc] at key
  rw [← key]
  infer_instance

theorem affineDetachedClopenInCenter (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) :
    AffineDetachedClopenInCenter A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact detachedClopenInCenter_ofAffine A hemb hsnc hsm k Y pY

end FunctorialResolution.EmbeddedResolution

end
