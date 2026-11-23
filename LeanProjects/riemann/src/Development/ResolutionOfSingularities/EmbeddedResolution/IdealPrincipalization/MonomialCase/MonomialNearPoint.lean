import Mathlib
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

variable {X : Scheme.{u}}

private theorem foldr_mul_ofFn_eq_prod {Z : Scheme.{u}} {n : ℕ} (f : Fin n → Z.IdealSheafData) :
    (List.ofFn f).foldr (· * ·) ⊤ = ∏ i, f i := by
  rw [← Scheme.IdealSheafData.one_eq_top]
  exact List.prod_ofFn

private theorem image_comap_eq_range_get (E : List X.IdealSheafData) (U : X.Opens) :
    (fun D : X.IdealSheafData => D.comap U.ι) '' {D | D ∈ E} =
      Set.range (fun i : Fin E.length => (E.get i).comap U.ι) := by
  ext w
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨i, hi, hEi⟩ := List.mem_iff_getElem.mp hD
    exact ⟨⟨i, hi⟩, by simp [hEi]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨E.get i, by simp, rfl⟩

private theorem isMonomialNear_iff_exists_pow_prod (E : List X.IdealSheafData) (M : X.IdealSheafData)
    (x : ↥X) :
    IsMonomialNear E M x ↔ ∃ U : X.Opens, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
      M.comap U.ι =
        (List.ofFn (fun i : Fin E.length => (E.get i).comap U.ι ^ a i)).foldr (· * ·) ⊤ :=
  Iff.rfl

theorem isMonomialNear_iff_mem_closure (E : List X.IdealSheafData) (M : X.IdealSheafData)
    (x : ↥X) :
    IsMonomialNear E M x ↔ ∃ U : X.Opens, x ∈ U ∧
      M.comap U.ι ∈
        Submonoid.closure ((fun D : X.IdealSheafData => D.comap U.ι) '' {D | D ∈ E}) := by
  rw [isMonomialNear_iff_exists_pow_prod]
  constructor
  · rintro ⟨U, hxU, a, ha⟩
    refine ⟨U, hxU, ?_⟩
    rw [image_comap_eq_range_get, ha, foldr_mul_ofFn_eq_prod, Submonoid.mem_closure_range_iff_of_fintype]
    exact ⟨a, rfl⟩
  · rintro ⟨U, hxU, hmem⟩
    rw [image_comap_eq_range_get, Submonoid.mem_closure_range_iff_of_fintype] at hmem
    obtain ⟨a, ha⟩ := hmem
    refine ⟨U, hxU, a, ?_⟩
    rw [foldr_mul_ofFn_eq_prod, ha]

theorem IsMonomialNear.mono {E E' : List X.IdealSheafData}
    (h : ∀ D ∈ E, D ≠ ⊤ → D ∈ E') {M : X.IdealSheafData} {x : ↥X}
    (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x := by
  obtain ⟨U, hxU, hmem⟩ := (isMonomialNear_iff_mem_closure E M x).mp hM
  refine (isMonomialNear_iff_mem_closure E' M x).mpr ⟨U, hxU, ?_⟩
  refine Submonoid.closure_le.mpr ?_ hmem
  rintro w hw
  obtain ⟨D, hD, hDw⟩ := hw
  have hDw' : D.comap U.ι = w := hDw
  subst hDw'
  by_cases hDtop : D = ⊤
  · have hone : D.comap U.ι = 1 := by
      simp [hDtop, Scheme.IdealSheafData.one_eq_top]
    rw [hone]
    exact SetLike.mem_coe.mpr (one_mem _)
  · exact Submonoid.subset_closure ⟨D, h D hD hDtop, rfl⟩

theorem IsMonomialNear.congr_setOf {E E' : List X.IdealSheafData}
    (h : {D : X.IdealSheafData | D ∈ E ∧ D ≠ ⊤} = {D : X.IdealSheafData | D ∈ E' ∧ D ≠ ⊤})
    {M : X.IdealSheafData} {x : ↥X} (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x :=
  hM.mono fun D hD hne => (((Set.ext_iff.mp h) D).mp ⟨hD, hne⟩).1

theorem IsMonomialNear.congr_sameNontrivialBoundary {E E' : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary E E') {M : X.IdealSheafData} {x : ↥X}
    (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x :=
  hM.congr_setOf h.setOf_mem_ne_top_eq

theorem isLocallyMonomialTriple_withBoundary (hG : MonomialGeometryHypotheses.{u})
    (T : MarkedIdealWithBoundary.{u}) (hT : IsLocallyMonomialTriple T)
    (E' : List T.scheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary E') :
    IsLocallyMonomialTriple (T.withBoundary E') :=
  { valid := hG.withBoundary_valid T hT.valid E' hE
    monomialNear := fun x hx => (hT.monomialNear x hx).congr_sameNontrivialBoundary hE }

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
