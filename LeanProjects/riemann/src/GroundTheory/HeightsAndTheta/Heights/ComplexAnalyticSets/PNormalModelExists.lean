import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelExists
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NonemptyNormalModelOfPresentation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] FractionRing.liftAlgebra

theorem integralClosure_fractionRing_finite (R : Type) [CommRing R] [IsDomain R] [Algebra ℂ R]
    [Algebra.FiniteType ℂ R] : Module.Finite R (integralClosure R (FractionRing R)) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ R
  let _ : Algebra (MvPolynomial (Fin s) ℂ) R := g.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin s) ℂ) R := hfin
  have : FaithfulSMul (MvPolynomial (Fin s) ℂ) R :=
    (faithfulSMul_iff_algebraMap_injective _ R).mpr hinj
  have : Algebra.IsIntegral (MvPolynomial (Fin s) ℂ) R := inferInstance
  have : FiniteDimensional (FractionRing (MvPolynomial (Fin s) ℂ)) (FractionRing R) := inferInstance
  have : CharZero (FractionRing (MvPolynomial (Fin s) ℂ)) :=
    charZero_of_injective_algebraMap (algebraMap ℂ _).injective
  have : Algebra.IsSeparable (FractionRing (MvPolynomial (Fin s) ℂ)) (FractionRing R) := inferInstance
  have : IsIntegralClosure (integralClosure R (FractionRing R)) (MvPolynomial (Fin s) ℂ)
      (FractionRing R) :=
    ⟨Subtype.val_injective, fun {x} =>
      ⟨fun hx => ⟨⟨x, hx.tower_top⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸
        isIntegral_trans (R := MvPolynomial (Fin s) ℂ) (A := R) _ ((integralClosure.isIntegral y).map
          (IsScalarTower.toAlgHom R (integralClosure R (FractionRing R)) (FractionRing R)))⟩⟩
  have := IsIntegralClosure.finite (MvPolynomial (Fin s) ℂ) (FractionRing (MvPolynomial (Fin s) ℂ))
    (FractionRing R) (integralClosure R (FractionRing R))
  exact Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin s) ℂ) R _

theorem nonempty_normalModel_of_presentation {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (R : Type)
    [CommRing R] [IsDomain R] [Algebra ℂ R] (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = J) : Nonempty (NormalModel J) :=
  _root_.UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_presentation J R π hπ hker

theorem NormalModelExists.proof : NormalModelExists.Statement := by
  intro n J hJ
  exact nonempty_normalModel_of_presentation J (MvPolynomial (Fin n) ℂ ⧸ J) (Ideal.Quotient.mkₐ ℂ J)
    (Ideal.Quotient.mkₐ_surjective ℂ J) (Ideal.Quotient.mkₐ_ker ℂ J)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
