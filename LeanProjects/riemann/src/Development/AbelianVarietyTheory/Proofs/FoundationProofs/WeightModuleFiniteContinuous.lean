import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfColW
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.WtCont

theorem continuous_functional_dwAct (n : ℕ) (f : MvPolynomial (Fin n × Fin n) ℂ) :
    ∀ ψ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ,
      Continuous fun g : GL (Fin n) ℂ => ψ (Formalism.UG.dwAct ℂ n n g f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro ψ
    have e : ∀ g : GL (Fin n) ℂ, Formalism.UG.dwAct ℂ n n g (C a) = C a := fun g => by
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    simp_rw [e]
    exact continuous_const
  | add p q hp hq => intro ψ; simp only [map_add]; exact (hp ψ).add (hq ψ)
  | mul_X p v hp =>
    intro ψ
    have e : ∀ g : GL (Fin n) ℂ, ψ (Formalism.UG.dwAct ℂ n n g (p * X v)) =
        ∑ b : Fin n, (((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) v.1 b) *
          (ψ.comp (LinearMap.mulRight ℂ (X (b, v.2)))) (Formalism.UG.dwAct ℂ n n g p) := by
      intro g
      simp only [map_mul, Formalism.UG.dwAct, Formalism.GradedWeylDivisibility.rowAct, aeval_X, Finset.mul_sum, map_sum, LinearMap.comp_apply,
        LinearMap.mulRight_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← smul_eq_C_mul, mul_smul_comm, map_smul, smul_eq_mul]
    simp_rw [e]
    refine continuous_finset_sum _ fun b _ => ?_
    refine Continuous.mul ?_ (hp _)
    exact ((Units.continuous_coe_inv).matrix_elem v.1 b)

theorem continuous_dual_dualWeylRep (n : ℕ) (ν : Fin n → ℕ) (x : Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν)
    (φ : Module.Dual ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν)) :
    Continuous fun g : GL (Fin n) ℂ => φ (Formalism.UG.dualWeylRep ℂ n n ν g x) := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ
  have e : ∀ g : GL (Fin n) ℂ, φ (Formalism.UG.dualWeylRep ℂ n n ν g x) = ψ (Formalism.UG.dwAct ℂ n n g x) := fun g => by
    rw [← hψ, LinearMap.comp_apply, Submodule.subtype_apply, Formalism.UG.dualWeylRep_apply]
  simp_rw [e]
  exact continuous_functional_dwAct n _ ψ

theorem continuous_det_units (n : ℕ) : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) ℂ → ℂˣ) := by
  rw [Units.continuous_iff]
  constructor
  · simp only [Function.comp_def, Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.continuous_val.matrix_det
  · have e : ∀ g : GL (Fin n) ℂ, ((Matrix.GeneralLinearGroup.det g)⁻¹ : ℂˣ) = Matrix.GeneralLinearGroup.det g⁻¹ :=
      fun g => (map_inv _ g).symm
    simp only [Function.comp_def, e, Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.continuous_coe_inv.matrix_det

theorem grp_tprod' (n : ℕ) {ι : Type} [DecidableEq ι] (mu : ι → ℕ → ℕ) (h : ι → GL (Fin n) ℂ)
    (x : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) :
    grp ℂ n mu h (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (fun τ => Formalism.UG.dualWeylRep ℂ n n _ (h τ) (x τ)) := by
  simp [grp, Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep, PiTensorProduct.mapMonoidHom, PiTensorProduct.map_tprod]

theorem finite_continuous_wtOp : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ), (∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)))) ∧ FiniteDimensional ℂ (NablaT ℂ n mu) ∧ ∀ (u : NablaT ℂ n mu) (ℓ : Module.Dual ℂ (NablaT ℂ n mu)), Continuous fun g : ι → GL (Fin n) ℂ => ℓ (wtOp ℂ n mu sh g u) := by
  intro n ι _ _ mu sh
  haveI hfin : ∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) :=
    fun τ => GlobalTheory.NablaFin.dualWeyl_finite ℂ n _
  refine ⟨hfin, GlobalTheory.NablaFin.nablaT_finite ℂ n ι mu, ?_⟩
  have hd : Continuous fun g : ι → GL (Fin n) ℂ =>
      ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : ℂˣ) : ℂ) := by
    refine Units.continuous_val.comp (continuous_finset_prod _ fun τ _ => ?_)
    exact ((continuous_det_units n).comp (continuous_apply τ)).zpow _
  intro u ℓ
  induction u using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    let b := fun τ => Module.finBasis ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)))
    let M := ℓ.compMultilinearMap (PiTensorProduct.tprod ℂ)
    have e : ∀ g : ι → GL (Fin n) ℂ, ℓ (wtOp ℂ n mu sh g (c • PiTensorProduct.tprod ℂ x)) =
        c * (((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : ℂˣ) : ℂ) *
          ∑ p : ∀ τ, Fin (Module.finrank ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)))),
            (∏ τ, (b τ).repr (Formalism.UG.dualWeylRep ℂ n n _ (g τ) (x τ)) (p τ)) * M (fun τ => b τ (p τ))) := by
      intro g
      rw [map_smul, map_smul, smul_eq_mul, wtOp_apply, map_smul, smul_eq_mul, grp_tprod']
      congr 2
      have h1 : (fun τ => Formalism.UG.dualWeylRep ℂ n n _ (g τ) (x τ)) = fun τ =>
          ∑ i, (b τ).repr (Formalism.UG.dualWeylRep ℂ n n _ (g τ) (x τ)) i • b τ i :=
        funext fun τ => ((b τ).sum_repr _).symm
      change M _ = _
      rw [h1, MultilinearMap.map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [MultilinearMap.map_smul_univ, smul_eq_mul]
    simp_rw [e]
    refine continuous_const.mul (hd.mul (continuous_finset_sum _ fun p _ => ?_))
    refine Continuous.mul (continuous_finset_prod _ fun τ _ => ?_) continuous_const
    exact (continuous_dual_dualWeylRep n _ (x τ) ((b τ).coord (p τ))).comp (continuous_apply τ)
  | add a a' ha ha' =>
    simp only [map_add]
    exact ha.add ha'

end GlobalTheory.WtCont
