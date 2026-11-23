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

open scoped ComplexOrder

namespace GlobalTheory.CartanBlocks

theorem posDef_fromBlocks_diag {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℂ} {D : Matrix n n ℂ} (hA : A.PosDef) (hD : D.PosDef) :
    (Matrix.fromBlocks A 0 0 D).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose, hA.1.eq, hD.1.eq, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero]
  · have key : star x ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ x) =
        star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
      simp [dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec, Function.comp_def, Matrix.mulVec,
        Pi.star_apply]
    rw [key]
    by_cases h1 : x ∘ Sum.inl = 0
    · have h2 : x ∘ Sum.inr ≠ 0 := by
        intro h2; apply hx; funext i; rcases i with i | i
        · exact congrFun h1 i
        · exact congrFun h2 i
      rw [h1]; simpa using hD.dotProduct_mulVec_pos h2
    · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos h1) (hD.posSemidef.dotProduct_mulVec_nonneg _)

theorem posDef_blk {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) {A : Matrix (Fin p) (Fin p) ℂ}
    {D : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) (hD : D.PosDef) : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A D).PosDef := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk
  rw [Matrix.reindex_apply]
  exact (posDef_fromBlocks_diag hA hD).submatrix e.symm.injective

theorem blk_conjTranspose {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A : Matrix (Fin p) (Fin p) ℂ)
    (D : Matrix (Fin q) (Fin q) ℂ) : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A D)ᴴ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e Aᴴ Dᴴ := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose]

theorem isCartan_blk : ∀ {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) (GA sA : Matrix (Fin a) (Fin a) ℂ) (GB sB : Matrix (Fin b) (Fin b) ℂ) {κ : ℝ},
    0 < κ → Formalism.IndefR.Datum.IsCartanInv GA sA → Formalism.IndefR.Datum.IsCartanInv GB sB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan ((κ : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB) ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e sA sB).map (starRingEnd ℂ)) := by
  intro a b d e GA sA GB sB κ hκ hA hB
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  set S := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e sA sB with hS
  set G := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB with hG
  have hSS : S * S = 1 := by rw [hS, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, hA1, hB1, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_one]
  have hSGS : Sᴴ * G * S = G := by
    rw [hS, hG, blk_conjTranspose, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, hA2, hB2]
  have hGS : (G * S).PosDef := by
    rw [hS, hG, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul]; exact posDef_blk e hA3 hB3

  have hGH : Gᴴ = G := by
    have h4 : Sᴴ * Gᴴ = G * S := by rw [← Matrix.conjTranspose_mul]; exact hGS.1.eq
    have h5 : Sᴴ * Sᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hSS, Matrix.conjTranspose_one]
    calc Gᴴ = Sᴴ * (Sᴴ * Gᴴ) := by rw [← Matrix.mul_assoc, h5, Matrix.one_mul]
      _ = G := by rw [h4, ← Matrix.mul_assoc, hSGS]
  have hSG : Sᴴ * G = G * S := by
    have := hGS.1.eq
    rw [Matrix.conjTranspose_mul, hGH] at this
    exact this
  have hT : (S.map (starRingEnd ℂ))ᵀ = Sᴴ := by
    ext i j; simp [Matrix.conjTranspose_apply]
  have hMM : (S.map (starRingEnd ℂ)).map star = S := by
    ext i j; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, hSS, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [hT, hMM, Matrix.mul_smul, Matrix.smul_mul, hSGS]
  · intro x hx
    have hy : star x ≠ 0 := by simpa using hx
    have hv : S.map (starRingEnd ℂ) *ᵥ x = star (S *ᵥ star x) := by
      ext i; simp [Matrix.mulVec, dotProduct, star_sum, Pi.star_apply, mul_comm]
    have hpos : ((κ : ℂ) • (G * S)).PosDef := hGS.smul (by exact_mod_cast hκ)
    have key : (S.map (starRingEnd ℂ) *ᵥ x) ⬝ᵥ ((κ : ℂ) • G) *ᵥ star x =
        star (star x) ⬝ᵥ (((κ : ℂ) • (G * S)) *ᵥ star x) := by
      rw [hv, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_smul, hSG]
    rw [key]
    have := hpos.dotProduct_mulVec_pos hy
    exact (Complex.lt_def.1 this).1

end GlobalTheory.CartanBlocks
