import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.chartAroundUnit (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (s : Sp R) :
    ∃ f : R, s ∈ Set.range (spMap (algebraMap R (Localization.Away f))) ∧ ∃ W : A.left.Opens,
      IsAffineOpen W ∧ ∀ t ∈ Set.range (spMap (algebraMap R (Localization.Away f))),
        ∃ x ∈ W, A.hom x = t := by
  let e : Sp R ⟶ A.left := (η[A]).left
  have he : e ≫ A.hom = 𝟙 (Sp R) := Over.w (η[A])
  have hpt : ∀ t : Sp R, A.hom (e t) = t := by
    intro t
    rw [← Scheme.Hom.comp_apply, he]
    rfl
  obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := e s) trivial
  have hrange : ∀ f : R, Set.range (spMap (algebraMap R (Localization.Away f))) =
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
    intro f
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have hopen : IsOpen (e ⁻¹' (W : Set A.left)) := W.isOpen.preimage e.continuous
  obtain ⟨_, ⟨f, rfl⟩, hsf, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := s) hsW hopen
  refine ⟨f, ?_, W, hW, ?_⟩
  · rw [hrange]; exact hsf
  · intro t ht
    rw [hrange] at ht
    exact ⟨e t, hsub ht, hpt t⟩
