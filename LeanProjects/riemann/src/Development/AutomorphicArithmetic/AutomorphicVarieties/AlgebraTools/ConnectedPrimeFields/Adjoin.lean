import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CmFree

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.adjoin :
    ∀ {A R : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [IsDomain R] [Algebra A R] [Module.Finite A R] [FaithfulSMul A R], IsBase A → ∀ f : R,
      ∃ _ : IsLocalRing (Algebra.adjoin A {f}), ReciprocityTheory.CA.IsCM (Algebra.adjoin A {f}) := by
  intro A R _ _ _ _ _ _ _ _ _ hA f
  have hf : IsIntegral A f := Algebra.IsIntegral.isIntegral f
  haveI : IsIntegrallyClosed A := hA.normal
  haveI : Algebra.IsIntegral (Algebra.adjoin A {f}) R := Algebra.IsIntegral.tower_top A
  haveI : IsLocalRing (Algebra.adjoin A {f}) :=
    RingHom.domain_isLocalRing (algebraMap (Algebra.adjoin A {f}) R)
  refine ⟨inferInstance, ?_⟩
  haveI : Module.Free A (Algebra.adjoin A {f}) := .of_basis (Algebra.adjoin.powerBasis' hf).basis
  haveI : Module.Finite A (Algebra.adjoin A {f}) := .of_basis (Algebra.adjoin.powerBasis' hf).basis
  exact cmFree hA.cm
