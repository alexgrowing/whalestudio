import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveDiscriminant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericPrimitive
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDiscrAdjoin
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFunctionFieldDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n d : ℕ}

def funField (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] : Type :=
  FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)

instance (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] : Field (funField J) :=
  inferInstanceAs (Field (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)))

instance (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] :
    Algebra (MvPolynomial (Fin n) ℂ ⧸ J) (funField J) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin n) ℂ ⧸ J) (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)))

instance (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] :
    IsFractionRing (MvPolynomial (Fin n) ℂ ⧸ J) (funField J) :=
  inferInstanceAs (IsFractionRing (MvPolynomial (Fin n) ℂ ⧸ J) (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)))

theorem aeval_mk_projAlgebra (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (G : Polynomial (MvPolynomial (Fin d) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    letI := projAlgebra J A
    Polynomial.aeval (Ideal.Quotient.mk J p) G =
      Ideal.Quotient.mk J (Polynomial.eval₂ (pullback A).toRingHom p G) := by
  let _ := projAlgebra J A
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
  rfl

set_option synthInstance.maxHeartbeats 400000 in

theorem PrimitiveDiscriminant.proof (hG : GenericPrimitive.Statement) (hD : DiscrAdjoin.Statement)
    (hF : FunctionFieldDegree.Statement) : PrimitiveDiscriminant.Statement := by
  intro n d J A hJ _ hA
  have := hJ
  let := projAlgebra J A
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite

  let iRL : Algebra (MvPolynomial (Fin d) ℂ) (funField J) :=
    ((algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (funField J)).comp
      (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J))).toAlgebra
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ)
      (funField J)) :=
    (IsFractionRing.injective (MvPolynomial (Fin n) ℂ ⧸ J) _).comp (by exact hA.injective)
  let iKL : Algebra (FractionRing (MvPolynomial (Fin d) ℂ)) (funField J) :=
    (IsFractionRing.lift hinj).toAlgebra
  have t1 : IsScalarTower (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
      (funField J) :=
    IsScalarTower.of_algebraMap_eq fun r => (IsFractionRing.lift_algebraMap hinj r).symm
  have t2 : IsScalarTower (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)
      (funField J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let iCL : Algebra ℂ (funField J) :=
    ((algebraMap (FractionRing (MvPolynomial (Fin d) ℂ)) (funField J)).comp
      (algebraMap ℂ (FractionRing (MvPolynomial (Fin d) ℂ)))).toAlgebra
  have t3 : IsScalarTower ℂ (FractionRing (MvPolynomial (Fin d) ℂ))
      (funField J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hfin, hdeg, hgen⟩ := hF n d J A hJ hA (FractionRing (MvPolynomial (Fin d) ℂ))
    (funField J)
  have := hfin
  have : CharZero (FractionRing (MvPolynomial (Fin d) ℂ)) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (FractionRing (MvPolynomial (Fin d) ℂ))).injective
  have : Algebra.IsSeparable (FractionRing (MvPolynomial (Fin d) ℂ))
      (funField J) := inferInstance

  have hC : ∀ a : ℂ, algebraMap ℂ (funField J) a =
      algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) _ (Ideal.Quotient.mk J (C a)) := by
    intro a
    change algebraMap (FractionRing (MvPolynomial (Fin d) ℂ)) _ (algebraMap ℂ _ a) = _
    rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ)),
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) ℂ)
        (MvPolynomial (Fin n) ℂ ⧸ J)]
    congr 1
    change Ideal.Quotient.mk J (pullback A (algebraMap ℂ _ a)) = _
    rw [AlgHom.commutes]
    rfl
  obtain ⟨D, hD0, hDc⟩ := hG ℂ (FractionRing (MvPolynomial (Fin d) ℂ))
    (funField J) n _ hgen
  refine ⟨D, hD0, fun c hc => ?_⟩
  have hprim := hDc c hc
  have hsum : ∑ j, c j • algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (funField J)
      (Ideal.Quotient.mk J (X j)) = algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) _
        (Ideal.Quotient.mk J (sum₂ c)) := by
    simp only [Algebra.smul_def, hC, ← map_mul, ← map_sum, sum₂]
  rw [hsum] at hprim
  have hℓ : IsIntegral (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J (sum₂ c)) :=
    Algebra.IsIntegral.isIntegral _
  obtain ⟨hdeg', hdisc, hmem⟩ := hD (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
    (funField J) _ hℓ.algebraMap hprim
  have hmin : minpoly (MvPolynomial (Fin d) ℂ) (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J)
      (funField J) (Ideal.Quotient.mk J (sum₂ c))) =
        formMinpoly J A c :=
    minpoly.algHom_eq (IsScalarTower.toAlgHom (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) _)
      (IsFractionRing.injective _ _) _
  rw [hmin] at hdeg' hdisc hmem
  refine ⟨minpoly.monic hℓ, hdeg'.trans hdeg, ?_, hdisc, fun j => ?_⟩
  · have h0 := minpoly.aeval (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J (sum₂ c))
    rw [aeval_mk_projAlgebra] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  · have hxj : IsIntegral (MvPolynomial (Fin d) ℂ) (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J)
        (funField J) (Ideal.Quotient.mk J (X j))) :=
      (Algebra.IsIntegral.isIntegral _).algebraMap
    have hm := hmem _ hxj
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨G, hGe⟩ := hm
    refine ⟨G, Ideal.Quotient.eq.1 (IsFractionRing.injective (MvPolynomial (Fin n) ℂ ⧸ J)
      (funField J) ?_)⟩
    rw [← aeval_mk_projAlgebra, ← Polynomial.aeval_algebraMap_apply]
    refine Eq.trans ?_ hGe.symm
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (funField J),
      ← map_mul]
    congr 1

end

end GroundTheory.Heights₂.Heights.ComplexSets
