import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ConstantCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.MaximalContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.DisjointUnionCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem comap_subschemeι_self {W : Scheme.{u}} (J : W.IdealSheafData) :
    J.comap J.subschemeι = ⊥ := by
  simp [Scheme.IdealSheafData.comap]

theorem card_complEmbPreimage (m : ℕ) (S : Finset (Fin m)) (a : Fin m) (ha : a ∈ S) :
    (complEmbPreimage m S a).card = S.card - 1 := by
  classical
  rw [← Finset.card_erase_of_mem ha]
  refine Finset.card_bij (fun t _ => complOrderEmb m ({a} : Finset (Fin m)) t) ?_ ?_ ?_
  · intro t ht
    rw [mem_complEmbPreimage] at ht
    refine Finset.mem_erase.mpr ⟨?_, ht⟩
    intro hcontra
    exact (complOrderEmb_notMem m {a} t) (by rw [hcontra]; exact Finset.mem_singleton_self a)
  · intro t₁ _ t₂ _ hEq
    exact (complOrderEmb m ({a} : Finset (Fin m))).injective hEq
  · intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_erase.mp hb
    obtain ⟨t, ht⟩ := exists_complOrderEmb_eq m ({a} : Finset (Fin m)) (by simpa using hb1)
    exact ⟨t, mem_complEmbPreimage_of_complOrderEmb_eq m S a hb2 ht, ht⟩

namespace MaximalContactCover

variable {X X' : Scheme.{u}} {k : Type u} [Field k] {p : X' ⟶ Spec (CommRingCat.of k)}
  {τ : X ⟶ X'} {I : X.IdealSheafData} {c : ℕ}

theorem comap_iInfImageIdeal_subschemeι_eq_bot (C : MaximalContactCover p τ I c) :
    C.toCoverData.iInfImageIdeal.comap C.toCoverData.iInfImageIdeal.subschemeι = ⊥ :=
  comap_subschemeι_self C.toCoverData.iInfImageIdeal

theorem ker_pullbackFiberToHypersurface (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    Scheme.Hom.ker C.pullbackFiberToHypersurface =
      (Scheme.Hom.ker C.pullbackFiberToTotal).comap C.toCoverData.iInfImageIdeal.subschemeι := by
  have h := Scheme.Hom.ker_comp C.pullbackFiberToHypersurface C.toCoverData.iInfImageIdeal.subschemeι
  rw [C.pullbackFiberToHypersurface_comp_subschemeι] at h
  rw [h, Blowup.comap_map_of_isClosedImmersion]

theorem hasEtaleCoordCodim_pullbackFiberToHypersurface (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    HasEtaleCoordCodim (C.toCoverData.iInfImageIdeal.subschemeι ≫ C.projection ≫ p) C.pullbackFiberToHypersurface
      (c - 1) := by
  intro x
  obtain ⟨i, y, hy⟩ :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.exists_summandι_base_eq C.toCoverData (C.pullbackFiberToTotal.base x)
  have hmemU : C.pullbackFiberToTotal.base x ∈ C.toCoverData.summandOpen i := by
    rw [← hy]
    exact Set.mem_range_self y
  have hprojmem : C.toCoverData.disjointUnionMap.base (C.pullbackFiberToTotal.base x) ∈ C.toCoverData.opens i := by
    rw [← hy]
    exact MaxContactReduction.FiniteOpenCoverWithIdeals.disjointUnionMap_summandι_mem C.toCoverData i y
  have h1 : τ.base (C.pullbackFiberToBase.base x)
      = C.toCoverData.disjointUnionMap.base (C.pullbackFiberToTotal.base x) := by
    have h0 : C.pullbackFiberToBase ≫ τ = C.pullbackFiberToTotal ≫ C.projection := Limits.pullback.condition
    have h2 := congrArg (fun f : C.pullbackFiber ⟶ X' => f.base x) h0
    simpa using h2
  rcases C.adapted i with ⟨-, hfar⟩ | ⟨n, ch, S, j, hcard, hjS, hker, hloc⟩
  · exfalso
    refine hfar (C.pullbackFiberToBase.base x) ?_
    rw [h1]
    exact hprojmem
  · have hUaff : IsAffineOpen (C.toCoverData.summandOpen i) :=
      MaxContactReduction.FiniteOpenCoverWithIdeals.isAffineOpen_summandOpen C.toCoverData i (C.isAffine i)
    have hkse : Scheme.Hom.ker C.pullbackFiberToTotal
        = (Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap := C.ker_pullbackFiberToTotal
    have hH : restrictIdeal C.toCoverData.iInfImageIdeal (C.toCoverData.summandOpen i) =
        (C.toCoverData.summandEtaleChart i ch).coordIdeal {j} := by
      rw [MaxContactReduction.FiniteOpenCoverWithIdeals.restrictIdeal_iInfImageIdeal_summandOpen C.toCoverData i,
        MaxContactReduction.FiniteOpenCoverWithIdeals.summandEtaleChart_coordIdeal C.toCoverData i ch {j}, hloc]
    have h2 := MaxContactReduction.FiniteOpenCoverWithIdeals.restrictIdeal_comap_disjointUnionMap_summandOpen
      C.toCoverData i (Scheme.Hom.ker τ)
    have h3 := MaxContactReduction.FiniteOpenCoverWithIdeals.summandEtaleChart_coordIdeal C.toCoverData i ch S
    have hZ : restrictIdeal (Scheme.Hom.ker C.pullbackFiberToTotal) (C.toCoverData.summandOpen i) =
        (C.toCoverData.summandEtaleChart i ch).coordIdeal S := by
      rw [hkse, h3]
      exact h2.trans (by rw [hker])
    have hb : C.toCoverData.iInfImageIdeal.subschemeι.base (C.pullbackFiberToHypersurface.base x)
        = C.pullbackFiberToTotal.base x := by
      have h4 := congrArg (fun f : C.pullbackFiber ⟶ C.toCoverData.disjointUnion => f.base x)
        C.pullbackFiberToHypersurface_comp_subschemeι
      simpa using h4
    refine ⟨C.toCoverData.iInfImageIdeal.subschemeι ⁻¹ᵁ C.toCoverData.summandOpen i, ?_,
      n - ({j} : Finset (Fin n)).card,
      (C.toCoverData.summandEtaleChart i ch).restrictToSubscheme hUaff C.toCoverData.iInfImageIdeal {j} hH,
      complEmbPreimage n S j, ?_, ?_⟩
    · show C.toCoverData.iInfImageIdeal.subschemeι.base (C.pullbackFiberToHypersurface.base x) ∈
        C.toCoverData.summandOpen i
      rw [hb]
      exact hmemU
    · rw [card_complEmbPreimage n S j hjS, hcard]
    · rw [C.ker_pullbackFiberToHypersurface]
      exact restrictIdeal_comap_subschemeι_eq_coordIdeal (C.toCoverData.summandEtaleChart i ch)
        hUaff (Scheme.Hom.ker C.pullbackFiberToTotal) C.toCoverData.iInfImageIdeal S j hZ hH

theorem isIso_pullbackFiberToHypersurface_of_eq_one (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] (hc : c = 1) :
    IsIso C.pullbackFiberToHypersurface := by
  have hkse : Scheme.Hom.ker C.pullbackFiberToTotal
      = (Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap := C.ker_pullbackFiberToTotal
  have hkey : Scheme.Hom.ker C.pullbackFiberToTotal = C.toCoverData.iInfImageIdeal := by
    rw [hkse]
    refine MaxContactReduction.FiniteOpenCoverWithIdeals.ext_of_comap_summandι C.toCoverData (fun i => ?_)
    have e1 : C.toCoverData.iInfImageIdeal.comap (C.toCoverData.summandι i)
        = C.toCoverData.localIdeal i :=
      MaxContactReduction.FiniteOpenCoverWithIdeals.comap_iInfImageIdeal_summandι C.toCoverData i
    have e2 : ((Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap).comap
          (C.toCoverData.summandι i)
        = restrictIdeal (Scheme.Hom.ker τ) (C.toCoverData.opens i) := by
      rw [← Scheme.IdealSheafData.comap_comp,
        MaxContactReduction.FiniteOpenCoverWithIdeals.summandι_comp_disjointUnionMap C.toCoverData i]
    rw [e1, e2]
    rcases C.adapted i with ⟨hloc, hfar⟩ | ⟨n, ch, S, j, hcard, hjS, hker, hloc⟩
    · rw [hloc]
      exact restrictIdeal_ker_eq_top_of_not_mem τ (C.toCoverData.opens i) hfar
    · have hS : S = {j} := by
        have h1 : S.card = 1 := by rw [hcard, hc]
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
        subst ha
        rw [Finset.mem_singleton] at hjS
        rw [hjS]
      rw [hker, hloc, hS]
  have hker0 : Scheme.Hom.ker C.pullbackFiberToHypersurface = ⊥ := by
    rw [C.ker_pullbackFiberToHypersurface, hkey, C.comap_iInfImageIdeal_subschemeι_eq_bot]
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker0

end MaximalContactCover

end FunctorialResolution.EmbeddedResolution

end
