import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPairLat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

namespace GlobalTheory.SigBlockSum

lemma cT_eq_conjTranspose {m p : Type} (M : Matrix m p ℂ) :
    Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose]

def sgn (p q : ℕ) : Fin p ⊕ Fin q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

lemma fromBlocks_one_neg_one (p q : ℕ) :
    (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Matrix.diagonal (sgn p q) := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;>
    simp [sgn, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp

lemma rows_reindex {n : Type} [Fintype n] [DecidableEq n] {p q : ℕ} (G : Matrix n n ℂ) (e : n ≃ Fin p ⊕ Fin q)
    (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (h : Pᴴ * G.reindex e e * P = Matrix.fromBlocks 1 0 0 (-1)) :
    (P.submatrix e id)ᴴ * G * P.submatrix e id = Matrix.diagonal (sgn p q) := by
  have hG : G = (G.reindex e e).submatrix e e := by ext i j; simp
  rw [hG, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h,
    fromBlocks_one_neg_one]
  simp

def sortCols (pa qa pb qb : ℕ) :
    Fin (pa + pb) ⊕ Fin (qa + qb) ≃ (Fin pa ⊕ Fin qa) ⊕ (Fin pb ⊕ Fin qb) :=
  (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans (Equiv.sumSumSumComm _ _ _ _)

lemma sgn_sortCols (pa qa pb qb : ℕ) :
    Sum.elim (sgn pa qa) (sgn pb qb) ∘ sortCols pa qa pb qb = sgn (pa + pb) (qa + qb) := by
  funext x
  rcases x with i | i
  · rcases h : (finSumFinEquiv.symm i : Fin pa ⊕ Fin pb) with k | k <;>
      simp [sortCols, sgn, h]
  · rcases h : (finSumFinEquiv.symm i : Fin qa ⊕ Fin qb) with k | k <;>
      simp [sortCols, sgn, h]

theorem hasSig_smul_blk : ∀ {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) (GA : Matrix (Fin a) (Fin a) ℂ) (GB : Matrix (Fin b) (Fin b) ℂ) {pa qa pb qb : ℕ} {κ : ℝ},
    0 < κ → Formalism.UG.HasSignature GA pa qa → Formalism.UG.HasSignature GB pb qb →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig ((κ : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB) (pa + pb) (qa + qb) := by
  intro a b d e GA GB pa qa pb qb κ hκ hA hB
  obtain ⟨eA, PA, hPA⟩ := hA
  obtain ⟨eB, PB, hPB⟩ := hB
  rw [cT_eq_conjTranspose] at hPA hPB
  have hQA := rows_reindex GA eA _ hPA
  have hQB := rows_reindex GB eB _ hPB
  set QA := (PA : Matrix (Fin pa ⊕ Fin qa) (Fin pa ⊕ Fin qa) ℂ).submatrix eA id
  set QB := (PB : Matrix (Fin pb ⊕ Fin qb) (Fin pb ⊕ Fin qb) ℂ).submatrix eB id
  have hca : a = pa + qa := by simpa using Fintype.card_congr eA
  have hcb : b = pb + qb := by simpa using Fintype.card_congr eB
  have hcd : a + b = d := by simpa using Fintype.card_congr e
  let τ := sortCols pa qa pb qb
  let Q0 : Matrix (Fin a ⊕ Fin b) ((Fin pa ⊕ Fin qa) ⊕ (Fin pb ⊕ Fin qb)) ℂ := Matrix.fromBlocks QA 0 0 QB
  let Q : Matrix (Fin d) (Fin (pa + pb) ⊕ Fin (qa + qb)) ℂ := Q0.submatrix e.symm τ
  have hQ : Qᴴ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB * Q = Matrix.fromBlocks 1 0 0 (-1) := by
    have h0 : Q0ᴴ * Matrix.fromBlocks GA 0 0 GB * Q0 =
        Matrix.diagonal (Sum.elim (sgn pa qa) (sgn pb qb)) := by
      simp only [Q0, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
      simp [hQA, hQB, Matrix.fromBlocks_diagonal]
    have hb : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB = (Matrix.fromBlocks GA 0 0 GB).submatrix e.symm e.symm := rfl
    rw [hb, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h0,
      Matrix.submatrix_diagonal_equiv, sgn_sortCols, fromBlocks_one_neg_one]
  refine ⟨by omega, ((((Real.sqrt κ)⁻¹ : ℝ) : ℂ)) • Q.map star, ?_⟩
  set c : ℂ := (((Real.sqrt κ)⁻¹ : ℝ) : ℂ)
  have h1 : (c • Q.map star)ᵀ = c • Qᴴ := by
    ext i j; simp [Matrix.conjTranspose]
  have h2 : (c • Q.map star).map star = c • Q := by
    ext i j; simp [c, Complex.conj_ofReal]
  have h3 : c * (κ : ℂ) * c = 1 := by
    have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
    have : (Real.sqrt κ)⁻¹ * κ * (Real.sqrt κ)⁻¹ = 1 := by
      field_simp; nlinarith [Real.mul_self_sqrt hκ.le, Real.sq_sqrt hκ.le]
    simp only [c]; exact_mod_cast this
  rw [h1, h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hQ]
  convert one_smul ℂ (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin (pa + pb) ⊕ Fin (qa + qb)) (Fin (pa + pb) ⊕ Fin (qa + qb)) ℂ) using 2
  linear_combination h3

end GlobalTheory.SigBlockSum
