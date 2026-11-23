import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem closure_range_algebraMap_residueField {A : Type} [CommRing A] (p : Ideal A) [p.IsPrime] :
    Subfield.closure (Set.range (algebraMap A p.ResidueField)) = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  have hs : algebraMap A p.ResidueField s ≠ 0 := by
    rw [Ne, IsScalarTower.algebraMap_apply A (Localization.AtPrime p) p.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).mp h
      ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p s).mpr s.2)
  have key : IsLocalRing.residue (Localization.AtPrime p) (IsLocalization.mk' _ a s) =
      algebraMap A p.ResidueField a / algebraMap A p.ResidueField s := by
    rw [eq_div_iff hs]
    simp only [IsScalarTower.algebraMap_apply A (Localization.AtPrime p) p.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq, ← map_mul, IsLocalization.mk'_spec]
  rw [key]
  exact Subfield.div_mem _ (Subfield.subset_closure ⟨a, rfl⟩) (Subfield.subset_closure ⟨s, rfl⟩)

theorem residueField_spMap {A : Type} [CommRing A] (x : Sp A) :
    ∃ φ : A →+* (Sp A).residueField x,
      spMap φ = (Sp A).fromSpecResidueField x ∧ Subfield.closure (Set.range φ) = ⊤ := by
  haveI : x.asIdeal.IsPrime := x.isPrime
  let e : x.asIdeal.ResidueField ≃+* (Sp A).residueField x :=
    (Scheme.Spec.residueFieldIso (CommRingCat.of A) x).symm.commRingCatIsoToRingEquiv
  refine ⟨(e : x.asIdeal.ResidueField →+* (Sp A).residueField x).comp
    (algebraMap A x.asIdeal.ResidueField), ?_, ?_⟩
  · rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp]
    rfl
  · rw [RingHom.coe_comp, Set.range_comp, ← RingHom.map_field_closure, closure_range_algebraMap_residueField]
    exact eq_top_iff.mpr fun y _ => ⟨e.symm y, trivial, by simp⟩

end GlobalTheory
