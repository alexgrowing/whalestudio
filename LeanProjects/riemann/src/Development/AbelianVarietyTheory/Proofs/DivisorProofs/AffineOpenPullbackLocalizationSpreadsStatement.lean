import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenPullbackLocalizationSpreads
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_open_pullback_localization_spreads : ∀ (R : Type) [CommRing R] (q : PrimeSpectrum R) (T : Scheme.{0}) (π : T ⟶ Sp R) [LocallyOfFinitePresentation π] [QuasiCompact π] [QuasiSeparated π] (C' : Type) [CommRing C'] [Algebra (Localization.AtPrime q.asIdeal) C'] (U' : (pullback π (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))).Opens) (e' : Sp C' ≅ U'.toScheme), e'.hom ≫ U'.ι ≫ pullback.snd π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) = spMap (algebraMap (Localization.AtPrime q.asIdeal) C') → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra.FinitePresentation R B) (U₁ : T.Opens) (e₁ : Sp B ≅ U₁.toScheme), e₁.hom ≫ U₁.ι ≫ π = spMap (algebraMap R B) ∧ pullback.fst π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) ⁻¹ᵁ U₁ = U' ∧ Nonempty (((Localization.AtPrime q.asIdeal) ⊗[R] B) ≃ₐ[(Localization.AtPrime q.asIdeal)] C') := by
  first | exact @GlobalTheory.exists_affine_finitePresentation_of_affine_atPrime | exact GlobalTheory.exists_affine_finitePresentation_of_affine_atPrime | (intros; apply GlobalTheory.exists_affine_finitePresentation_of_affine_atPrime <;> assumption)
