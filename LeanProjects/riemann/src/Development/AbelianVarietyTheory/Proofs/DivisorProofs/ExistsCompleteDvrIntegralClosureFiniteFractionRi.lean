import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem exists_complete_dvr_of_finite_fractionRing_hom :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
      IsAdicComplete (maximalIdeal V) V → ∀ (K' : Type) [Field K'] (σ : FractionRing V →+* K'),
      σ.Finite → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V')
        (_ : CharZero V') (f : V →+* V') (τ : K' →+* FractionRing V'),
        IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        ∀ a, τ (σ (algebraMap V _ a)) = algebraMap V' _ (f a) := by
  intro V _ _ _ _ hV K' _ σ hσ
  letI : Algebra (FractionRing V) K' := σ.toAlgebra
  letI : Algebra V K' := (σ.comp (algebraMap V (FractionRing V))).toAlgebra
  haveI : IsScalarTower V (FractionRing V) K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional (FractionRing V) K' := hσ
  haveI := hV
  haveI : CharZero (FractionRing V) := IsFractionRing.charZero_of_isFractionRing V
  let B := integralClosure V K'
  haveI : Module.Finite V B := IsIntegralClosure.finite V (FractionRing V) K' B
  haveI hBd : IsDiscreteValuationRing B := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V (FractionRing V) K'
  haveI : IsFractionRing B K' := integralClosure.isFractionRing_of_finite_extension (FractionRing V) K'
  have hinj : Function.Injective (algebraMap V B) := by
    intro x y h
    have h2 := congrArg (algebraMap B K') h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h2
    exact (σ.injective.comp (IsFractionRing.injective V (FractionRing V))) h2
  haveI : CharZero B := charZero_of_injective_algebraMap hinj
  haveI : FaithfulSMul V B := (faithfulSMul_iff_algebraMap_injective V B).2 hinj
  haveI : Algebra.IsIntegral V B := IsIntegralClosure.isIntegral_algebra V K'
  haveI : IsLocalHom (algebraMap V B) := Algebra.IsIntegral.isLocalHom _ _
  let e : FractionRing B ≃ₐ[B] K' := IsLocalization.algEquiv (nonZeroDivisors B) (FractionRing B) K'
  refine ⟨B, inferInstance, inferInstance, hBd, inferInstance, algebraMap V B, e.symm.toRingHom,
    CompleteFiniteExtension.isAdicComplete_of_finite_local V B, hinj, inferInstance, ?_, fun a => ?_⟩
  · exact (inferInstance : Module.Finite V B)
  · change e.symm (algebraMap B K' (algebraMap V B a)) = _
    exact e.symm.commutes _

end GlobalTheory
