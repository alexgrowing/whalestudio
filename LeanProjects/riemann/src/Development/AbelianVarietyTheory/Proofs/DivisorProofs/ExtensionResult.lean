import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonObj

namespace GlobalTheory.HalfGeo

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_ext_torsion {S : Scheme.{0}} (G : Over S) [GrpObj G] (q : ℕ) [IsFinite (torsion G q).hom]
    (R K : Type) [CommRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (x₀ : Sp R ⟶ S) (ξ₀ : Sp K ⟶ S) (h : spMap (algebraMap R K) ≫ x₀ = ξ₀) (s : Over.mk ξ₀ ⟶ G) (hs : s ^ q = 1) :
    ∃ s' : Over.mk x₀ ⟶ G, s' ^ q = 1 ∧ spMap (algebraMap R K) ≫ s'.left = s.left := by
  obtain ⟨h1, h2⟩ := GlobalTheory.LamF.torsion_universal G q
  obtain ⟨t, ht⟩ := h2 _ s hs
  obtain ⟨c, ⟨hc1, hc2⟩, -⟩ := GlobalTheory.existsUnique_lift_spec_of_isLocalization (R := R) (R' := K) (nonZeroDivisors R) le_rfl
    (torsion G q).hom t.left x₀ ((Over.w t).trans h.symm)
  refine ⟨(Over.homMk c hc2 : Over.mk x₀ ⟶ torsion G q) ≫ torsion.ι G q, ?_, ?_⟩
  · rw [← MonObj.comp_pow, h1, MonObj.comp_one]
  · rw [← ht, Over.comp_left, Over.comp_left, ← hc1]
    exact (Category.assoc _ _ _).symm

theorem extSt : ExtSt := by
  intro E _ _ _ H Dw l Xo c O _ β Z R K _ _ _ _ _ _ x₀ ξ₀ h q hq s hs
  haveI : IsFinite (torsion Z.oF.t.G q).hom :=
    (GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_torsion _ _ (GlobalTheory.Obj.toPolAV Z.oF).isAb q (Nat.one_le_iff_ne_zero.2 hq)).1
  exact exists_ext_torsion Z.oF.t.G q R K x₀ ξ₀ h s hs

end GlobalTheory.HalfGeo
