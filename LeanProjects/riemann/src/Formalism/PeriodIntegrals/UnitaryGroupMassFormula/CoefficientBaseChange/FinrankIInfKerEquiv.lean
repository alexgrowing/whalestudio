import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseCoefCrys
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.InvBaseChange

open TensorProduct

namespace PI.CoefExt

section Transport

variable {R X Y : Type} [Field R] [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y] {ι : Type}

theorem iInf_ker_map_equiv (e : X ≃ₗ[R] Y) (S : ι → X →ₗ[R] X) (S' : ι → Y →ₗ[R] Y)
    (h : ∀ g x, e (S g x) = S' g (e x)) :
    (⨅ g, LinearMap.ker (S' g - LinearMap.id) : Submodule R Y)
      = (⨅ g, LinearMap.ker (S g - LinearMap.id) : Submodule R X).map (e : X →ₗ[R] Y) := by
  ext y
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun g => ?_
  constructor
  · intro hy
    apply e.injective
    rw [h, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hy]
  · intro hy
    have := congrArg e hy
    rwa [h, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this

theorem finrank_iInf_ker_equiv (e : X ≃ₗ[R] Y) (S : ι → X →ₗ[R] X) (S' : ι → Y →ₗ[R] Y)
    (h : ∀ g x, e (S g x) = S' g (e x)) :
    Module.finrank R (⨅ g, LinearMap.ker (S' g - LinearMap.id) : Submodule R Y)
      = Module.finrank R (⨅ g, LinearMap.ker (S g - LinearMap.id) : Submodule R X) := by
  rw [iInf_ker_map_equiv e S S' h, LinearEquiv.finrank_map_eq]

end Transport

section Coef

variable {Qp LL LL' BB : Type} [Field Qp] [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL']
  [Algebra LL LL'] [IsScalarTower Qp LL LL'] [AddCommGroup BB] [Module Qp BB] {k : ℕ}

noncomputable def coefEquiv : LL' ⊗[LL] ((Fin k → LL) ⊗[Qp] BB) ≃ₗ[LL'] (Fin k → LL') ⊗[Qp] BB :=
  (AlgebraTensorModule.assoc Qp LL LL' LL' (Fin k → LL) BB).symm ≪≫ₗ
    AlgebraTensorModule.congr (piScalarRight LL LL' LL' (Fin k)) (LinearEquiv.refl Qp BB)

theorem coefEquiv_tmul (c : LL') (v : Fin k → LL) (b : BB) :
    coefEquiv (c ⊗ₜ[LL] (v ⊗ₜ[Qp] b)) = (fun i => v i • c) ⊗ₜ[Qp] b := by
  simp [coefEquiv, piScalarRightHom_tmul]

theorem mulVec_map_smul (A : Matrix (Fin k) (Fin k) LL) (v : Fin k → LL) (c : LL') :
    (A.map (algebraMap LL LL')).mulVec (fun i => v i • c) = fun i => (A.mulVec v) i • c := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

noncomputable def actT (A : Matrix (Fin k) (Fin k) LL) (β : BB →ₗ[Qp] BB) :
    (Fin k → LL) ⊗[Qp] BB →ₗ[LL] (Fin k → LL) ⊗[Qp] BB :=
  AlgebraTensorModule.map (Matrix.toLin' A) β

theorem coefEquiv_comm (A : Matrix (Fin k) (Fin k) LL) (β : BB →ₗ[Qp] BB)
    (x : LL' ⊗[LL] ((Fin k → LL) ⊗[Qp] BB)) :
    coefEquiv ((actT A β).baseChange LL' x) = actT (A.map (algebraMap LL LL')) β (coefEquiv x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
    | tmul v b =>
      rw [LinearMap.baseChange_tmul]
      simp only [actT, AlgebraTensorModule.map_tmul, coefEquiv_tmul, Matrix.toLin'_apply]
      rw [mulVec_map_smul]

theorem finrank_fix_coef (hI : InvBaseChange) {G : Type} (M : G → Matrix (Fin k) (Fin k) LL)
    (β : G → BB →ₗ[Qp] BB) :
    Module.finrank LL' (⨅ g, LinearMap.ker (actT ((M g).map (algebraMap LL LL')) (β g) - LinearMap.id) :
        Submodule LL' ((Fin k → LL') ⊗[Qp] BB))
      = Module.finrank LL (⨅ g, LinearMap.ker (actT (M g) (β g) - LinearMap.id) :
        Submodule LL ((Fin k → LL) ⊗[Qp] BB)) := by
  rw [finrank_iInf_ker_equiv coefEquiv (fun g => (actT (M g) (β g)).baseChange LL')
    (fun g => actT ((M g).map (algebraMap LL LL')) (β g)) (fun g x => coefEquiv_comm _ _ x)]
  exact hI LL LL' _ G (fun g => actT (M g) (β g))

end Coef

theorem coefCrysGen_of (hI : InvBaseChange) : Formalism.MainNotions.N.GlobalTheory.CoefCrysGen := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL LL' _ _ _ _ f k M hM
  letI : Algebra LL LL' := f.toRingHom.toAlgebra
  haveI : IsScalarTower Qp LL LL' := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  have key := finrank_fix_coef (LL' := LL') (BB := B) hI (fun g => M g)
    (fun g => ((PD.actB g).toAlgHom.toLinearMap).restrictScalars Qp)
  unfold Formalism.WeaklyAdmissibleFiltrations.IsCrys at hM ⊢
  rw [Module.finrank_fin_fun] at hM ⊢
  rw [← hM]
  exact key

end PI.CoefExt
