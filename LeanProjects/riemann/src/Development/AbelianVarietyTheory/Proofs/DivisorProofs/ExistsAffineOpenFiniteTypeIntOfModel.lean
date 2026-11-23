import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.RatModel.exists_affineOpen_finiteType_int : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), ∃ U : M.Z.Opens, IsAffineOpen U ∧ x ∈ U ∧ Algebra.FiniteType ℤ Γ(M.Z, U) := by
  intro o' Ω _ _ _ hB M x
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp M.Z.isBasis_affineOpens) (show x ∈ (⊤ : M.Z.Opens) from trivial)
  refine ⟨U, hU, hxU, ?_⟩
  have hl := M.lft
  have h1 : (M.s.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType M.s hl ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of o')).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of o')).commRingCatIsoToRingEquiv.symm.surjective
  have h3 : (Int.castRingHom o').FiniteType := by
    have h := hB.ft
    rw [← RingHom.finiteType_algebraMap] at h
    convert h
    exact RingHom.ext_int _ _
  have h4 := (h1.comp h2).comp h3
  have he : algebraMap ℤ Γ(M.Z, U) = ((M.s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of o')).inv.hom).comp (Int.castRingHom o') := RingHom.ext_int _ _
  rw [← RingHom.finiteType_algebraMap, he]
  exact h4
