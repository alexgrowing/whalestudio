import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsTop
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent

namespace GlobalTheory.BplusDescent

theorem exists_pow_mul_mem_of_eq_basicOpen : ∀ (X : Scheme.{0}) [IsIntegral X] (U V : AffOp X) (a : Γ(X, U.1)), V.1 = X.basicOpen a → ∀ x : V.Bp, ∃ (N : ℕ) (r : U.Bp), (r : Kbar X) = algebraMap Γ(X, U.1) (Kbar X) a ^ N * x := by
  intro X _ U V a hV x
  have h : V.1 ≤ U.1 := hV ▸ X.basicOpen_le a
  letI : Algebra Γ(X, U.1) Γ(X, V.1) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  haveI : IsLocalization.Away a Γ(X, V.1) := U.2.1.isLocalization_of_eq_basicOpen a (homOfLE h) hV
  haveI : IsScalarTower Γ(X, U.1) Γ(X, V.1) (Kbar X) := IsScalarTower.of_algebraMap_eq fun b =>
    (congrArg (algebraMap X.functionField (Kbar X)) (X.presheaf.germ_res_apply (homOfLE h) _ _ b)).symm
  obtain ⟨⟨_, N, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers a)
    (Rₘ := Γ(X, V.1)) (x : Kbar X) x.2
  refine ⟨N, ⟨_, hm⟩, ?_⟩
  change a ^ N • (x : Kbar X) = _
  rw [Algebra.smul_def, map_pow]

end GlobalTheory.BplusDescent
