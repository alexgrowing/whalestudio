import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem letter_lift {LL U D N : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D]
    (m : U →+* End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)
    [AddCommGroup N] [Module LL N] [Module F N] [IsScalarTower LL F N] (κ' : D →ₗ[LL] N)
    (hκ : ∀ c x, κ' (m c x) = τ c • κ' x) :
    ∃ j : Letter m F τ →ₗ[F] N, ∀ x, j (letterMk m F τ x) = κ' x := by
  have hk : letterKer m F τ ≤ LinearMap.ker (κ'.liftBaseChange F) := by
    refine iSup_le fun c => ?_
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul z x =>
      simp [LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul, hκ, smul_smul, mul_comm]
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, add_zero]
  refine ⟨(letterKer m F τ).liftQ (κ'.liftBaseChange F) hk, fun x => ?_⟩
  show (letterKer m F τ).liftQ (κ'.liftBaseChange F) hk ((letterKer m F τ).mkQ ((1 : F) ⊗ₜ[LL] x)) = κ' x
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.liftBaseChange_tmul, one_smul]

theorem UpperTheory.Gal.crystallineComparison.detWdLift_of :
    WdLift := by
  intro l _ P ι K LL V _ _ _ _ ρ N _ _ κ hadd hsmul hmul
  letI := algC ι LL
  letI : Module ↥LL.1 N := Module.compHom N (algebraMap ↥LL.1 ℂ)
  haveI : IsScalarTower ↥LL.1 ℂ N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let κ' : ↥(Dpst P ρ) →ₗ[↥LL.1] N :=
    { toFun := κ
      map_add' := hadd
      map_smul' := fun c x => hsmul c x }
  exact letter_lift (mulD P ρ) ℂ (urC ι) κ' (fun c x => hmul c x)
