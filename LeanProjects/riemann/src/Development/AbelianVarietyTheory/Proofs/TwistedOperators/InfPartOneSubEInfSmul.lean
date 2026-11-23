import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaClosed

open GlobalTheory.FinTranslate

variable {D : D7}

theorem finPart_eInf_smul (a : Formalism.L2.Theta.AE D) : finPart D (eInf D • a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero]
  | tmul x y =>
    rw [TensorProduct.smul_tmul']
    simp only [finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
      id_eq]
    have h0 : sndA D.host.F (eInf D) = 0 := rfl
    rw [smul_eq_mul, map_mul, h0, zero_mul, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, add_zero]

theorem infPart_one_sub_eInf_smul (a : Formalism.L2.Theta.AE D) : infPart D ((1 - eInf D) • a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero]
  | tmul x y =>
    rw [TensorProduct.smul_tmul']
    simp only [infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
      id_eq]
    have h1 : fstA D.host.F (eInf D) = 1 := rfl
    rw [smul_eq_mul, map_mul, map_sub, map_one, h1, sub_self, zero_mul, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, add_zero]

theorem isThetaFunO_heisO_all {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (u : WO S T) : IsThetaFunO ψ S T (heisO ψ S T u f) := by

  have hre : (eInf D • u).map (finPart D) = 0 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, finPart_eInf_smul]
  have hfin : ((1 - eInf D) • u).map (infPart D) = 0 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, infPart_one_sub_eInf_smul]
  have hsplit : (1 - eInf D) • u + eInf D • u = u := by
    rw [sub_smul, one_smul, sub_add_cancel]

  have hcomp : heisO ψ S T ((1 - eInf D) • u) (heisO ψ S T (eInf D • u) f) = heisO ψ S T u f := by
    rw [GlobalTheory.FinTranslate.heisO_heisO, GlobalTheory.FinTranslate.symplOH_fin_real hfin hre, AddChar.map_zero_eq_one, one_smul,
      hsplit]
  rw [← hcomp]
  exact GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 (GlobalTheory.WeilVacMove.isTheta_heisO_real hψ hre hf) hfin

theorem thetaClosed : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ u, IsThetaFunO ψ S T (heisO ψ S T u f)) ∧ ∀ τ z, IsThetaFunO ψ S T (Datum.dRho (heisO ψ S T) θ τ z f) := by
  intro D ψ θ hψ hθ S T f hf
  exact ⟨fun u => isThetaFunO_heisO_all hψ hf u, fun τ z => GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hf⟩

end GlobalTheory.ThetaClosed
