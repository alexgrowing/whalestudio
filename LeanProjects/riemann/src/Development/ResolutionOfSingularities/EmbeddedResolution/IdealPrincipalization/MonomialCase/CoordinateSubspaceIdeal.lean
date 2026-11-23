import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.CoordinateIdealOrderOne
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u v

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialChart

theorem comap_biSup_finset {X Y : Scheme.{u}} {ι : Type v} (f : X ⟶ Y)
    (I : ι → Y.IdealSheafData) (S : Finset ι) :
    (⨆ j ∈ S, I j).comap f = ⨆ j ∈ S, (I j).comap f := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.iSup_insert, Finset.iSup_insert, Scheme.IdealSheafData.comap_sup, ih]

theorem restrictIdeal_biSup_finset {X : Scheme.{u}} {ι : Type v} (U : X.Opens)
    (I : ι → X.IdealSheafData) (S : Finset ι) :
    restrictIdeal (⨆ j ∈ S, I j) U = ⨆ j ∈ S, restrictIdeal (I j) U :=
  comap_biSup_finset U.ι I S

private theorem ofIdealTop_sup {X : Scheme.{u}} [IsAffine X] (I J : Ideal Γ(X, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (I ⊔ J) =
      Scheme.IdealSheafData.ofIdealTop I ⊔ Scheme.IdealSheafData.ofIdealTop J := by
  ext U : 2
  simp [Scheme.IdealSheafData.ofIdealTop, Ideal.map_sup]

theorem coordSubspaceIdeal_insert (k : Type u) [Field k] (m : ℕ) (j : Fin m)
    (S : Finset (Fin m)) :
    coordSubspaceIdeal k m (insert j S) =
      coordSubspaceIdeal k m {j} ⊔ coordSubspaceIdeal k m S := by
  classical
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, coordSubspaceIdeal_eq_ofIdealTop_span_coord, coordSubspaceIdeal_eq_ofIdealTop_span_coord,
    Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert, Finset.coe_singleton,
    Set.image_singleton, ofIdealTop_sup]

theorem coordSubspaceIdeal_eq_biSup_singleton (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    coordSubspaceIdeal k m S = ⨆ j ∈ S, coordSubspaceIdeal k m {j} := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp [coordSubspaceIdeal_empty]
  · intro a s _ ih
    rw [coordSubspaceIdeal_insert, ih, Finset.iSup_insert]

theorem coordIdeal_eq_biSup_singleton {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (m : ℕ) (c : EtaleChart p U m)
    (S : Finset (Fin m)) :
    c.coordIdeal S = ⨆ j ∈ S, c.coordIdeal {j} := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_biSup_singleton, comap_biSup_finset]
  exact iSup_congr fun j => iSup_congr fun _ => (c.coordIdeal_eq_comap_coordSubspaceIdeal {j}).symm

theorem orderAt_boundary_eq_one : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ D ∈ T.boundary, ∀ x : ↥T.scheme, x ∈ D.support → orderAt D x = 1 := by
  intro T hT D hD x hx
  have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
  obtain ⟨_, hpos⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hT.snc
  obtain ⟨U, hxU, m, c, a, _, hnone, hsome⟩ := (hpos x).exists_etaleChart
  obtain ⟨i, hi, hDi⟩ := List.mem_iff_getElem.1 hD
  cases hai : a i with
  | none =>
      refine absurd hx (notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U ?_ x hxU)
      rw [← hDi]
      exact hnone i hi hai
  | some t =>
      obtain ⟨V, m', hxV, hVU', hV, -⟩ := exists_etaleChart_le T.structMap x U hxU
      have hDU : restrictIdeal D U = c.coordIdeal {t} := by
        rw [← hDi]
        exact hsome i hi t hai
      have hDV : restrictIdeal D V = (c.restrict hVU').coordIdeal {t} :=
        restrictIdeal_eq_restrict_coordIdeal_of_le hVU' c D {t} hDU
      exact orderAt_eq_one_of_restrictIdeal_eq_coordIdeal_singleton T.structMap hV
        (c.restrict hVU') t D hDV x hxV hx

theorem smooth_intersectionIdeal_subscheme : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ J : Finset (Fin T.boundary.length),
      AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap) := by
  classical
  intro T hT J
  refine smooth_subschemeι_comp_of_locally_eq_coordIdeal (p := T.structMap) (intersectionIdeal T.boundary J) ?_
  intro x hx
  obtain ⟨_, hpos⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hT.snc
  obtain ⟨U, hxU, m, c, a, _, hnone, hsome⟩ := (hpos x).exists_etaleChart
  have hle : ∀ j ∈ J, T.boundary.get j ≤ intersectionIdeal T.boundary J := by
    intro j hj
    rw [intersectionIdeal_eq_iSup]
    exact le_iSup₂ (f := fun j (_ : j ∈ J) => T.boundary.get j) j hj
  have hxj : ∀ j ∈ J, x ∈ (T.boundary.get j).support := by
    intro j hj
    rw [mem_support_iff_stalkIdeal_ne_top]
    intro hcon
    have h2 := stalkIdeal_mono (hle j hj) x
    rw [hcon] at h2
    exact (mem_support_iff_stalkIdeal_ne_top _ _).1 hx (top_le_iff.1 h2)
  have hsomej : ∀ j ∈ J, ∃ t : Fin m, a (j : ℕ) = some t := by
    intro j hj
    cases haj : a (j : ℕ) with
    | none =>
        refine absurd (hxj j hj)
          (notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ U ?_ x hxU)
        rw [List.get_eq_getElem]
        exact hnone (j : ℕ) j.isLt haj
    | some t => exact ⟨t, rfl⟩
  refine ⟨U, hxU, m, c, J.biUnion (fun j => (a (j : ℕ)).toFinset), ?_⟩
  have h1 : restrictIdeal (intersectionIdeal T.boundary J) U
      = ⨆ j ∈ J, restrictIdeal (T.boundary.get j) U := by
    rw [intersectionIdeal_eq_iSup]
    exact restrictIdeal_biSup_finset U (fun j => T.boundary.get j) J
  have h2 : c.coordIdeal (J.biUnion (fun j => (a (j : ℕ)).toFinset))
      = ⨆ t ∈ J.biUnion (fun j => (a (j : ℕ)).toFinset), c.coordIdeal {t} :=
    coordIdeal_eq_biSup_singleton T.structMap U m c _
  rw [h1, h2]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun j => iSup_le fun hj => ?_
    obtain ⟨t, ht⟩ := hsomej j hj
    have hres : restrictIdeal (T.boundary.get j) U = c.coordIdeal {t} := by
      rw [List.get_eq_getElem]
      exact hsome (j : ℕ) j.isLt t ht
    have htS : t ∈ J.biUnion (fun j => (a (j : ℕ)).toFinset) :=
      Finset.mem_biUnion.2 ⟨j, hj, by simp [ht]⟩
    rw [hres]
    exact le_iSup₂
      (f := fun t (_ : t ∈ J.biUnion (fun j => (a (j : ℕ)).toFinset)) =>
        c.coordIdeal ({t} : Finset (Fin m))) t htS
  · refine iSup_le fun t => iSup_le fun htS => ?_
    obtain ⟨j, hj, htj⟩ := Finset.mem_biUnion.1 htS
    have ht : a (j : ℕ) = some t := Option.mem_def.1 (Option.mem_toFinset.1 htj)
    have hres : restrictIdeal (T.boundary.get j) U = c.coordIdeal {t} := by
      rw [List.get_eq_getElem]
      exact hsome (j : ℕ) j.isLt t ht
    rw [← hres]
    exact le_iSup₂ (f := fun j (_ : j ∈ J) => restrictIdeal (T.boundary.get j) U) j hj

end MonomialChart

end FunctorialResolution.EmbeddedResolution

end
