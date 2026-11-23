import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenPullbackLocalizationSpreadsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeSpreadsOutFromLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenInfBasicOpenIsoTensor

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.exists_finite_free_chart_away_of_atPrime : ∀ (R : Type) [CommRing R] (q : PrimeSpectrum R) (T : Scheme.{0}) (π : T ⟶ Sp R)
    [LocallyOfFinitePresentation π] [QuasiCompact π] [QuasiSeparated π]
    (C' : Type) [CommRing C'] [Algebra (Localization.AtPrime q.asIdeal) C']
    [Module.Finite (Localization.AtPrime q.asIdeal) C'] [Module.Free (Localization.AtPrime q.asIdeal) C']
    (U' : (pullback π (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))).Opens) (e' : Sp C' ≅ U'.toScheme),
    e'.hom ≫ U'.ι ≫ pullback.snd π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) =
      spMap (algebraMap (Localization.AtPrime q.asIdeal) C') →
    (∀ t, pullback.snd π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) t =
      IsLocalRing.closedPoint (Localization.AtPrime q.asIdeal) → t ∈ U') →
    ∃ (r : R) (_ : r ∉ q.asIdeal) (C : Type) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra (Localization.Away r) C)
      (_ : IsScalarTower R (Localization.Away r) C) (_ : Module.Finite (Localization.Away r) C)
      (_ : Module.Free (Localization.Away r) C) (U : T.Opens) (e : Sp C ≅ U.toScheme),
      e.hom ≫ U.ι ≫ π = spMap (algebraMap R C) ∧ ∀ t : T, π t = q → t ∈ U := by
  intro R _ q T π _ _ _ C' _ _ _ _ U' e' he' hU'
  obtain ⟨B, _, _, _, U₁, e₁, he₁, hpre, ⟨ψ⟩⟩ := GlobalTheory.T.affine_open_pullback_localization_spreads R q T π C' U' e' he'
  obtain ⟨r, hr, hfin, hfree⟩ := GlobalTheory.T.finite_free_spreads_out_from_localization R q B (Module.Finite.equiv ψ.symm.toLinearEquiv)
    (Module.Free.of_equiv ψ.symm.toLinearEquiv)
  obtain ⟨e, he⟩ := GlobalTheory.affineOpen_inf_basicOpen_iso_tensor R T π B U₁ e₁ he₁ r
  refine ⟨r, hr, Localization.Away r ⊗[R] B, inferInstance, inferInstance, inferInstance, inferInstance, hfin, hfree,
    _, e, he, fun t ht => ⟨?_, ?_⟩⟩
  · have hy : spMap (algebraMap R (Localization.AtPrime q.asIdeal))
        (IsLocalRing.closedPoint (Localization.AtPrime q.asIdeal)) = q :=
      PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := q.asIdeal))
    obtain ⟨z, rfl, hz⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback π (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))) t _ (ht.trans hy.symm)
    have h := hU' z hz
    rw [← hpre] at h
    exact h
  · change π t ∈ (PrimeSpectrum.basicOpen r : (Sp R).Opens)
    rw [ht]
    exact hr
