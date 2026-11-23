import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKOOfIsGLO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallFStdB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

namespace GlobalTheory.StdZetaAgree
open GlobalTheory.StdPairCone

theorem jacobi_blocks {k m n : Type} [Field k] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (H G : Matrix (m ⊕ n) (m ⊕ n) k) (e : H * G = 1) :
    H.det * G.toBlocks₁₁.det = H.toBlocks₂₂.det ∧
      H.toBlocks₂₁ * G.toBlocks₁₁ + H.toBlocks₂₂ * G.toBlocks₂₁ = 0 := by
  rw [← Matrix.fromBlocks_toBlocks H, ← Matrix.fromBlocks_toBlocks G, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at e
  obtain ⟨e1, -, e3, -⟩ := e
  refine ⟨?_, e3⟩
  have e4 : H * Matrix.fromBlocks G.toBlocks₁₁ 0 G.toBlocks₂₁ 1 =
      Matrix.fromBlocks 1 H.toBlocks₁₂ 0 H.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks H]
    rw [Matrix.fromBlocks_multiply, e1, e3]
    simp
  have := congrArg Matrix.det e4
  rwa [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    Matrix.det_one, mul_one, one_mul] at this

theorem blocks_rel {k : Type} [Field k] {a a' : ℕ} (h : GL (Fin (a + a')) k) :
    h.val.det * (blk₁ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val)).det = (blk₂ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val)).det ∧
      blk₁ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val) * (blk₁ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val))ᵀ +
        blk₂ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val) * (blk₂ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val))ᵀ = 0 := by
  set H : Matrix (Fin a ⊕ Fin a') (Fin a ⊕ Fin a') k := h.val.submatrix finSumFinEquiv finSumFinEquiv with hH
  set G : Matrix (Fin a ⊕ Fin a') (Fin a ⊕ Fin a') k := (h⁻¹).val.submatrix finSumFinEquiv finSumFinEquiv with hG
  have e : H * G = 1 := by
    rw [hH, hG, Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  obtain ⟨e1, e2⟩ := jacobi_blocks H G e
  have x1 : (blk₁ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val))ᵀ = G.toBlocks₁₁ := by
    ext i j; exact frameMatrixFirstColumnBlock_mul_apply (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) (invT h).val j (Fin.castAdd a' i)
  have x2 : (blk₂ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val))ᵀ = G.toBlocks₂₁ := by
    ext i j; exact frameMatrixFirstColumnBlock_mul_apply (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) (invT h).val j (Fin.natAdd a i)
  have y1 : blk₁ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val) = H.toBlocks₂₁ := by
    ext i j; exact frameMatrixSecondColumnBlock_mul_apply (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) h.val i (Fin.castAdd a' j)
  have y2 : blk₂ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val) = H.toBlocks₂₂ := by
    ext i j; exact frameMatrixSecondColumnBlock_mul_apply (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) h.val i (Fin.natAdd a j)
  have hd : H.det = h.val.det := Matrix.det_submatrix_equiv_self _ _
  refine ⟨?_, by rw [x1, x2, y1, y2]; exact e2⟩
  rw [← Matrix.det_transpose (blk₁ _), x1, y2, ← hd]; exact e1

end GlobalTheory.StdZetaAgree

open GlobalTheory.StdPairCone GlobalTheory.StdZetaAgree in

theorem GlobalTheory.StdZetaAgree.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ), IsUnif ϖ →
      bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (GlobalTheory.StdPairCone.stdA ν ϖ c a a') =
        smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν (ν * β) (GlobalTheory.StdPairCone.stdB ν ϖ c a a') := by
  intro k _ _ _ _ _ _ ν β ϖ c a a' hϖ
  funext h
  obtain ⟨hA0, hA⟩ := GlobalTheory.StdPairZeta.bigF_stdA ν ϖ c a a' hϖ
  obtain ⟨hB0, hB⟩ := GlobalTheory.StdPairZetaB.smallF_stdB ν ϖ c a a'
  obtain ⟨e1, e2⟩ := blocks_rel h
  rw [bigZetaIntegral_eq, smallP]
  set X : Matrix (Fin a) (Fin (a + a')) k := X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val with hX
  set Y : Matrix (Fin a') (Fin (a + a')) k := Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val with hY
  by_cases h0 : (blk₁ X).det = 0
  · rw [hA0 X h0, hB0 Y (by rw [← e1, h0, mul_zero]), mul_zero, mul_zero]
  have h1 : (blk₂ Y).det ≠ 0 := by rw [← e1]; exact mul_ne_zero h.det_ne_zero h0
  set g₁ : GL (Fin a) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ h0 with hg₁
  set g₂ : GL (Fin a') k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ h1 with hg₂
  have v₁ : g₁.val = blk₁ X := rfl
  have v₂ : g₂.val = blk₂ Y := rfl
  rw [hA X g₁ v₁, hB Y g₂ v₂]
  have hd : gdet g₂ = gdet h * gdet g₁ := Units.ext (by
    rw [Units.val_mul, GlobalTheory.StdPairZeta.val_gdet, GlobalTheory.StdPairZeta.val_gdet, GlobalTheory.StdPairZeta.val_gdet, v₁, v₂, e1])
  have hm : (g₂⁻¹).val * blk₁ Y = -((g₁⁻¹).val * blk₂ X)ᵀ := by
    rw [← v₁, ← v₂] at e2
    have e3 : blk₁ Y = -(g₂.val * (blk₂ X)ᵀ * (g₁⁻¹).valᵀ) := by
      rw [← Matrix.neg_mul, ← eq_neg_of_add_eq_zero_left e2, Matrix.mul_assoc, ← Matrix.transpose_mul,
        Units.inv_mul, Matrix.transpose_one, Matrix.mul_one]
    rw [e3, Matrix.mul_neg, Matrix.mul_assoc g₂.val, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
      Matrix.transpose_mul]
  have hi : Set.indicator {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} (1 : Matrix (Fin a') (Fin a) k → ℂ)
      ((g₂⁻¹).val * blk₁ Y) = Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1
        ((g₁⁻¹).val * blk₂ X) := by
    rw [hm]
    generalize (g₁⁻¹).val * blk₂ X = Z
    have hiff : (-Zᵀ) ∈ {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} ↔
        Z ∈ {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} := by
      simp only [Set.mem_setOf_eq, GlobalTheory.SplitWeil.cball, Matrix.neg_apply, Matrix.transpose_apply, Valuation.map_neg]
      exact forall_comm
    by_cases hZ : Z ∈ {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)}
    · rw [Set.indicator_of_mem hZ, Set.indicator_of_mem (hiff.2 hZ)]; rfl
    · rw [Set.indicator_of_notMem hZ, Set.indicator_of_notMem (fun h => hZ (hiff.1 h))]
  have hp : apow (gdet h) (-(a : ℂ) / 2) = apow (gdet h) ((Fintype.card (Fin a') : ℂ) / 2) *
      apow (gdet h) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) := by
    rw [← apow_add]; congr 1; simp only [Fintype.card_fin]; push_cast; ring
  rw [hi, hd, apow_mul, hp, map_mul, mul_inv, MonoidHom.mul_apply]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  have h3 := (ν (gdet h)).ne_zero
  field_simp
