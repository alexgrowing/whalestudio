import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.ExistsInvariantPerfectPairingNablaSqDualWeyl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

private theorem exists_Q {ι : Type} [Fintype ι] [DecidableEq ι] {V U : ι → Type} [∀ τ, AddCommGroup (V τ)]
    [∀ τ, Module ℂ (V τ)] [∀ τ, AddCommGroup (U τ)] [∀ τ, Module ℂ (U τ)] [∀ τ, FiniteDimensional ℂ (V τ)]
    (P : ∀ τ, V τ →ₗ[ℂ] U τ →ₗ[ℂ] ℂ) (hP : ∀ τ, Function.Bijective (P τ).flip) :
    ∃ F : MultilinearMap ℂ V (PiTensorProduct ℂ U →ₗ[ℂ] ℂ), (∀ u, (∀ v, F v u = 0) → u = 0) ∧
      ∀ v u, F v (PiTensorProduct.tprod ℂ u) = ∏ τ, P τ (v τ) (u τ) := by
  let e : ∀ τ, U τ ≃ₗ[ℂ] Module.Dual ℂ (V τ) := fun τ => LinearEquiv.ofBijective (P τ).flip (hP τ)
  let Q : PiTensorProduct ℂ U ≃ₗ[ℂ] Module.Dual ℂ (PiTensorProduct ℂ V) :=
    (PiTensorProduct.congr e).trans PiTensorProduct.dualDistribEquiv
  refine ⟨(LinearMap.flip Q.toLinearMap).compMultilinearMap (PiTensorProduct.tprod ℂ), fun u hu => ?_, fun v u => ?_⟩
  · apply Q.injective
    rw [map_zero]
    apply PiTensorProduct.ext
    ext v
    exact hu v
  · change PiTensorProduct.dualDistrib (PiTensorProduct.congr e (PiTensorProduct.tprod ℂ u))
      (PiTensorProduct.tprod ℂ v) = _
    rw [PiTensorProduct.congr_tprod, PiTensorProduct.dualDistrib_apply]
    rfl

theorem UpperTheory.exists_invariant_nondegenerate_pairing_weightRep_nablaT :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ) (lam : ι → DomWeight n),
        (∀ τ (a : Fin n), (lam τ).w a = (mu τ a : ℤ) + sh τ) →
        ∃ P : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] NablaT ℂ n mu →ₗ[ℂ] ℂ, (∀ u, (∀ v, P v u = 0) → u = 0) ∧
          ∀ (g : ι → GL (Fin n) ℂ) v u, P (Formalism.L2.DIV.rhoK lam g v) (wtOp ℂ n mu sh g u) = P v u := by
  intro n ι _ _ mu sh lam hl
  choose P1 hb hi using fun τ =>
    UpperTheory.exists_invariant_perfect_pairing_nablaSq_dualWeyl n (Formalism.CohomologicalDescent.LD.res n (mu τ)) (sh τ) (lam τ) (fun a => hl τ a)
  obtain ⟨F, hF0, hF⟩ := exists_Q P1 hb
  obtain ⟨P, hP, -⟩ := GlobalTheory.T.dualWeylModule_tensor_coefficient_universal ι n lam (NablaT ℂ n mu →ₗ[ℂ] ℂ) F
  refine ⟨P, fun u hu => hF0 u fun v => by rw [← hP]; exact hu _, fun g v u => ?_⟩
  have key : (P ∘ₗ Formalism.L2.DIV.rhoK lam g).compl₂ (wtOp ℂ n mu sh g) = P := by
    refine (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal ι n lam (NablaT ℂ n mu →ₗ[ℂ] ℂ) F).unique (fun w => ?_) hP
    apply PiTensorProduct.ext
    ext x
    change P (Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam w))
      (wtOp ℂ n mu sh g (PiTensorProduct.tprod ℂ x)) = F w (PiTensorProduct.tprod ℂ x)
    rw [rhoK_tenMul, hP, wtOp_apply, GlobalTheory.SemilinTransport.grp_tprod, map_smul, hF, hF]
    simp only [hi]
    rw [Finset.prod_mul_distrib, smul_eq_mul, ← mul_assoc, ← Units.coe_prod, ← Units.val_mul,
      ← Finset.prod_mul_distrib]
    simp
  exact LinearMap.congr_fun (LinearMap.congr_fun key v) u
