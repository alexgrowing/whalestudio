import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.CoordinateIdealOrderOne
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimClosedSubset
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FiniteKrullDim
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem smooth_ker_subschemeι_comp {k : Type u} [Field k] {X X' : Scheme.{u}}
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X')
    [AlgebraicGeometry.IsClosedImmersion τ] [AlgebraicGeometry.Smooth (τ ≫ p)] :
    AlgebraicGeometry.Smooth (τ.ker.subschemeι ≫ p) := by
  have hinv : inv τ.toImage ≫ τ = τ.ker.subschemeι :=
    (IsIso.inv_comp_eq _).mpr τ.toImage_imageι.symm
  have hcomp : τ.ker.subschemeι ≫ p = inv τ.toImage ≫ (τ ≫ p) := by
    rw [← Category.assoc, hinv]
  rw [hcomp]
  infer_instance

theorem ker_le_map_idealSheaf {X X' : Scheme.{u}} (f : X ⟶ X') (I : X.IdealSheafData) :
    f.ker ≤ I.map f := by
  have hle : (⊥ : X.IdealSheafData).map f ≤ I.map f :=
    Scheme.IdealSheafData.map_mono f bot_le
  rwa [Scheme.IdealSheafData.map_bot] at hle

theorem orderAt_map_le_one_of_isClosedImmersion {k : Type u} [Field k] [CharZero k]
    {X X' : Scheme.{u}} (p : X' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (τ : X ⟶ X') [AlgebraicGeometry.IsClosedImmersion τ]
    [AlgebraicGeometry.Smooth (τ ≫ p)]
    (hker : NonzeroOnComponents τ.ker) (I : X.IdealSheafData) (x : ↥X') :
    orderAt (I.map τ) x ≤ 1 := by
  refine le_trans (orderAt_le_of_le (ker_le_map_idealSheaf τ I) x) ?_
  by_cases hx : x ∈ τ.ker.support
  · have : AlgebraicGeometry.Smooth (τ.ker.subschemeι ≫ p) := smooth_ker_subschemeι_comp p τ
    obtain ⟨U, m, c, S, hxU, hU, hD⟩ :=
      exists_chart_restrictIdeal_eq_coordIdeal p τ.ker x hx
    have hD' : τ.ker.comap U.ι = c.coordIdeal S := hD
    rcases S.eq_empty_or_nonempty with hS | ⟨j, hj⟩
    · subst hS
      exfalso
      have hcoord : c.coordIdeal (∅ : Finset (Fin m))
          = (⊥ : (affineSpaceFin k m).IdealSheafData).comap c.map := by
        rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_empty]
      have hUsupp : (U : Set ↥X') ⊆ (τ.ker.support : Set ↥X') := by
        intro y hy
        have hy' : y ∈ Set.range ⇑U.ι.base := by
          rw [Scheme.Opens.range_ι]
          exact hy
        obtain ⟨z, rfl⟩ := hy'
        have h1 : z ∈ ((τ.ker.comap U.ι).support : Set ↥U.toScheme) := by
          rw [hD', hcoord, support_comap_eq]
          simp [Scheme.IdealSheafData.support_bot]
        rw [support_comap_eq] at h1
        exact h1
      have hCmem : irreducibleComponent x ∈ irreducibleComponents ↥X' :=
        irreducibleComponent_mem_irreducibleComponents x
      refine hker _ hCmem ?_
      have hcl := closure_inter_open_eq (isClosed_irreducibleComponent)
        (isIrreducible_irreducibleComponent) U.2 ⟨x, mem_irreducibleComponent, hxU⟩
      rw [← hcl]
      refine closure_minimal ?_ (τ.ker.support).2
      exact fun y hy => hUsupp hy.2
    · exact orderAt_le_one_of_restrictIdeal_eq_coordIdeal p hU c S j hj τ.ker hD x hxU
  · have h0 : orderAt τ.ker x = 0 := (orderAt_eq_zero_iff_not_mem_support τ.ker x).mpr hx
    rw [h0]
    exact zero_le

theorem krullDimSucc_lt_of_isClosedImmersion_of_nonzeroOnComponents {k : Type u} [Field k]
    {X X' : Scheme.{u}} (p : X' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    (τ : X ⟶ X') [AlgebraicGeometry.IsClosedImmersion τ] [Nonempty ↥X]
    (hker : NonzeroOnComponents τ.ker) :
    krullDimSucc X < krullDimSucc X' := by
  have hfin : topologicalKrullDim ↥X' < ⊤ :=
    topologicalKrullDim_lt_top_of_finiteType p ‹AlgebraicGeometry.LocallyOfFiniteType p›
      ‹AlgebraicGeometry.QuasiCompact p›
  have hemb : Topology.IsClosedEmbedding ⇑τ.base :=
    AlgebraicGeometry.Scheme.Hom.isClosedEmbedding τ
  obtain ⟨z⟩ := ‹Nonempty ↥X›
  refine krullDimSucc_lt_of_homeomorph_isClosed X' X (Set.range ⇑τ.base) hemb.isClosed_range
    ⟨τ.base z, z, rfl⟩ ?_ hfin hemb.toIsEmbedding.toHomeomorph
  intro C hC hsub
  exact hker C hC (hsub.trans τ.range_subset_ker_support)

end FunctorialResolution.EmbeddedResolution
