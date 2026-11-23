import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalRingCardinality.DataKerI
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX

open MvPolynomial Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.BranchFormula

open Formalism.L2.Col.Br

theorem brEquiv_all : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n), Br.BrEquiv K hN lam sg := by
  intro K _ _ ι _ N n hN lam sg hS g g' h G
  have hB : ∀ τ, IsBlock hN (g' τ : Matrix (Fin N) (Fin N) K) (g τ : Matrix (Fin n) (Fin n) K) 1 := h
  apply Subtype.ext
  have hd : detTwK lam g' = detTwK sg g := by
    rw [detTwK, detTwK]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [detPow, detPow, hS τ, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, (hB τ).det, mul_one]
  simp only [brStd, brStdP, LinearMap.comp_apply, Submodule.subtype_apply, rhoK_coe, LinearMap.smul_apply, actP, trAct,
    AlgHom.toLinearMap_apply, map_smul, Submodule.coe_smul]
  rw [coefLast_blockAct K ι hN _ _ _ (fun _ => 1) fun τ => (hB τ).transpose, map_smul, Submodule.coe_smul, projVV_blockAct]
  simp only [smul_smul, one_pow, Finset.prod_const_one, mul_one]
  rw [hd]
  congr 1
  ring

end GlobalTheory.BranchFormula
