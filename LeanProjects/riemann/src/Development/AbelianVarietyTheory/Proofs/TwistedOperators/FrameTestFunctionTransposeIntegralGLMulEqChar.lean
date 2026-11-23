import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.FFunLeftInv
open GlobalTheory.SplitFlip

theorem fFun_transpose_mul_of_mem_KO : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (u : GL A k), u ∈ KO k A → ∀ h : GL D k,
      (ν (gdet u) : ℂ) * fFun μ σ ν Ψ (u.valᵀ * (X0 k σ * (invT h).val)) = fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  intro k _ _ _ _ _ _ A A' D _ _ _ _ _ _ μ _ σ ν Ψ u hu h
  classical
  let P : Matrix A A k → Matrix D D k := fun X => (fromBlocks X 0 0 (1 : Matrix A' A' k)).submatrix σ.symm σ.symm
  have hP : ∀ X Y, P X * P Y = P (X * Y) := fun X Y => by
    simp only [P, Matrix.submatrix_mul_equiv, fromBlocks_multiply]; simp
  have hP1 : P 1 = 1 := by simp [P, fromBlocks_one]
  let m : GL D k := ⟨P u.valᵀ, P (u⁻¹).valᵀ, by rw [hP, ← transpose_mul, Units.inv_mul, transpose_one, hP1],
    by rw [hP, ← transpose_mul, Units.mul_inv, transpose_one, hP1]⟩
  set h' : GL D k := invT m * h with hh'
  have e1 : u.valᵀ * (X0 k σ * (invT h).val) = X0 k σ * (invT h').val := by
    rw [hh', map_mul, invT_invT, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    congr 1
    ext i j
    rw [frameMatrixFirstColumnBlock_mul_apply]
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [m, P, X0, Matrix.mul_apply, eq_comm]
  have e2 : Y0 k σ * h'.val = Y0 k σ * h.val := by
    rw [hh', Units.val_mul, ← Matrix.mul_assoc]
    congr 1
    ext i j
    rw [invT_val]
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [m, P, Y0, Matrix.mul_apply, one_apply, eq_comm]
  have e3 : gdet h' = (gdet u)⁻¹ * gdet h := by
    rw [hh', gdet_mul, gdet_invT]
    congr 2
    ext
    simp [m, P, Matrix.GeneralLinearGroup.val_det_apply, det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
  have hv : valuation k ((gdet u)⁻¹ : kˣ) = 1 := by
    rw [← map_inv]; exact valuation_gdet_of_mem_KO (inv_mem hu)
  rw [e1, splitTheta_fFun_frameFirstBlock_mul, splitTheta_fFun_frameFirstBlock_mul, e2, e3, apow_mul, apow_of_valuation_eq_one hv, map_mul, Units.val_mul, map_inv]
  have : (ν (gdet u) : ℂ) * ((ν (gdet u))⁻¹ : ℂˣ) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  linear_combination ((ν (gdet h) : ℂ) * apow (gdet h) ((Fintype.card D : ℂ) / 2) * smallF μ ν Ψ (Y0 k σ * h.val)) * this

end GlobalTheory.FFunLeftInv
