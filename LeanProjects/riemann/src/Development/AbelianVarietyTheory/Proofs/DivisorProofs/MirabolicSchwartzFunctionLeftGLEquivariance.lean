import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory

theorem fFun_mul_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ) (g : GL (Fin a) k) (h : GL C k),
    fFun μ σ ν Ψ (g.val * (X0 k σ * (invT h).val)) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card C : ℂ) / 2) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν Ψ g h
  let f : Matrix (Fin a) (Fin a) k →* Matrix C C k :=
    { toFun := fun M => (Matrix.fromBlocks M (0 : Matrix (Fin a) A' k) 0 (1 : Matrix A' A' k)).submatrix σ.symm σ.symm
      map_one' := by rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
      map_mul' := fun M N => by
        rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp }
  let E : GL C k := Units.map f g
  have hE : ∀ M : Matrix (Fin a) (Fin a) k, f M = (Matrix.fromBlocks M (0 : Matrix (Fin a) A' k) 0 (1 : Matrix A' A' k)).submatrix σ.symm σ.symm := fun _ => rfl
  have hX : g.val * X0 k σ = X0 k σ * E.val := by
    ext i j
    rw [frameMatrixFirstColumnBlock_mul_apply]
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [X0, E, hE, Matrix.mul_apply]
  have hY : Y0 k σ * (invT E).val = Y0 k σ := by
    ext i j
    rw [frameMatrixSecondColumnBlock_mul_apply, invT_val]
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [Y0, E, hE, ← map_inv, Matrix.one_apply, eq_comm]
  have hdet : gdet E = gdet g := by
    ext
    simp [E, hE, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  have h1 : g.val * (X0 k σ * (invT h).val) = X0 k σ * (invT (invT E * h)).val := by
    rw [map_mul, invT_invT, Units.val_mul, ← Matrix.mul_assoc, hX, Matrix.mul_assoc]
  have h2 : Y0 k σ * (invT E * h).val = Y0 k σ * h.val := by
    rw [Units.val_mul, ← Matrix.mul_assoc, hY]
  have h3 : gdet (invT E * h) = (gdet g)⁻¹ * gdet h := by rw [gdet_mul, gdet_invT, hdet]
  rw [h1, splitTheta_fFun_frameFirstBlock_mul μ σ ν Ψ, splitTheta_fFun_frameFirstBlock_mul μ σ ν Ψ, h2, h3, map_mul, map_inv, apow_mul, apow_inv, apow_neg,
    Units.val_mul, Units.val_inv_eq_inv_val]
  have hν : ((ν (gdet g) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have ha : apow (gdet g) ((Fintype.card C : ℂ) / 2) ≠ 0 := apow_ne_zero _ _
  field_simp

end GlobalTheory
