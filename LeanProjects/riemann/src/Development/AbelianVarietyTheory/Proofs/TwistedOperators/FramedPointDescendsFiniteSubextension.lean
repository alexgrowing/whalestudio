import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem exists_finite_factor {F R K L : Type} [Field F] [CommRing R] [Field K] [Field L] [Algebra F R]
    [Algebra F K] [Algebra F L] [Algebra.FiniteType F R] (φ : K →ₐ[F] L) (hφ : φ.toRingHom.IsIntegral)
    (ψ : R →ₐ[F] L) :
    ∃ (M : Type) (_ : Field M) (_ : Algebra F M) (i : K →ₐ[F] M) (j : M →ₐ[F] L) (χ : R →ₐ[F] M),
      j.comp i = φ ∧ i.toRingHom.Finite ∧ j.comp χ = ψ := by
  classical
  letI : Algebra K L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType F R).out
  let M : IntermediateField K L := IntermediateField.adjoin K ((s.image ψ : Finset L) : Set L)
  haveI hM : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => hφ x
  have hmem : ∀ r : R, ψ r ∈ M.toSubalgebra.restrictScalars F := by
    intro r
    have hr : r ∈ Algebra.adjoin F (s : Set R) := hs ▸ Algebra.mem_top
    have : Algebra.adjoin F (s : Set R) ≤ (M.toSubalgebra.restrictScalars F).comap ψ := by
      refine Algebra.adjoin_le fun x hx => ?_
      exact IntermediateField.subset_adjoin K _ (by simpa using ⟨x, hx, rfl⟩)
    exact this hr
  refine ⟨M, inferInstance, inferInstance, IsScalarTower.toAlgHom F K M, M.val.restrictScalars F,
    ψ.codRestrict (M.toSubalgebra.restrictScalars F) hmem, ?_, ?_, ?_⟩
  · ext a; rfl
  · exact RingHom.finite_algebraMap.2 hM
  · ext a; rfl

theorem frPt_descends_finite :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K L : Type) [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) (z : FrPt Xo c L), φ.toRingHom.IsIntegral → ∃ (M : Type) (_ : Field M) (_ : Algebra c.F M) (i : K →ₐ[c.F] M) (j : M →ₐ[c.F] L) (z₁ : FrPt Xo c M), j.comp i = φ ∧ i.toRingHom.Finite ∧ FrMap j z₁ z := by
  intro E _ _ _ H Dw l Xo c K L _ _ _ _ φ z hφ
  obtain ⟨p, ψ, u, hu⟩ := GlobalTheory.FlagTan.fromTest_of_isLocalRing z
  haveI : Algebra.FiniteType c.F p.R := inferInstance
  obtain ⟨M, _, _, i, j, χ, h1, h2, h3⟩ := exists_finite_factor φ hφ ψ
  obtain ⟨z₁, hz⟩ := GlobalTheory.FlagTan.exists_frMap χ u
  exact ⟨M, inferInstance, inferInstance, i, j, z₁, h1, h2,
    GlobalTheory.FlagTan.frMap_of_comp hz hu fun a => DFunLike.congr_fun h3 a⟩

end GlobalTheory.HkIntegral
