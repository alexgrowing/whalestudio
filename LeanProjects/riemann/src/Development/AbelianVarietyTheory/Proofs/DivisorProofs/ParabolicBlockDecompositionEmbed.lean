import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PutLinPack
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdSumSymmLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixValuesUnipotentDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentDetOneAndTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockConjUnipotentStatement
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.BlockId

theorem dg_dg {R : Type} [CommRing R] (n m o p : ℕ) (hm : m ≤ n) (hp : o + p ≤ m) (g : GL (Fin p) R) :
    dg n 0 (dg m o g) = dg n o g := by
  apply Units.ext
  obtain ⟨-, h2, -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R n 0 0 m m
  obtain ⟨-, h2', -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R m o o p p
  obtain ⟨-, h2'', -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R n o o p p
  rw [(h2 _ (by omega)).1, (h2' g hp).1, (h2'' g (by omega)).1]
  obtain ⟨hadd, hneg, -, -, -, -, -, -⟩ := put_lin_pack R n 0 0 m m
  have hsub : ∀ X Y : Matrix (Fin m) (Fin m) R, put n 0 0 (X - Y) = put n 0 0 X - put n 0 0 Y := by
    intro X Y; rw [sub_eq_add_neg, hadd, hneg, ← sub_eq_add_neg]
  have hn1 := (PutNest.main R n m 0 0 o o p p 0 0).1
  have he1 : put n 0 0 (1 : Matrix (Fin m) (Fin m) R) = eye R n 0 0 m := rfl
  have he2 : put n 0 0 (eye R m o o p) = eye R n o o p := by
    simp only [eye]; rw [hn1 _ hp hp, zero_add]
  rw [hadd, hsub, he1, he2, hn1 _ hp hp, zero_add]
  abel

theorem dg_uni {R : Type} [CommRing R] (n m o₁ o₂ p q : ℕ) (hm : m ≤ n) (h1 : o₁ + p ≤ m) (h2 : o₂ + q ≤ m)
    (hd : o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) (X : Matrix (Fin p) (Fin q) R) :
    dg n 0 (uni m o₁ o₂ X) = uni n o₁ o₂ X := by
  apply Units.ext
  obtain ⟨-, h2d, -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R n 0 0 m m
  obtain ⟨h1u, -, -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R m o₁ o₂ p q
  obtain ⟨h1u', -, -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R n o₁ o₂ p q
  rw [(h2d _ (by omega)).1, (h1u X hd).1, (h1u' X hd).1]
  obtain ⟨hadd, -, -, -, -, -, -, -⟩ := put_lin_pack R n 0 0 m m
  have hn1 := (PutNest.main R n m 0 0 o₁ o₂ p q 0 0).1
  have he1 : put n 0 0 (1 : Matrix (Fin m) (Fin m) R) = eye R n 0 0 m := rfl
  rw [hadd, hn1 _ h1 h2, he1, zero_add, zero_add]
  abel

theorem main : ∀ (R : Type) [CommRing R] (n m m₁ m₂ : ℕ), m₁ + m₂ = m → m ≤ n → ∀ (a : GL (Fin m₁) R) (b : GL (Fin m₂) R) (x : Matrix (Fin m₂) (Fin m₁) R), dg n 0 (dg m 0 a * dg m m₁ b * uni m m₁ 0 x) = dg n 0 a * uni n m₁ 0 (b.val * x) * dg n m₁ b := by
  intro R _ n m m₁ m₂ hm hmn a b x
  have hmul := ((GlobalTheory.T.block_unipotent_det_one_and_trivial R n 0 0 m m).2.2.2.2.1 (by omega)).1
  rw [hmul, hmul, dg_dg n m 0 m₁ hmn (by omega), dg_dg n m m₁ m₂ hmn (by omega),
    dg_uni n m m₁ 0 m₂ m₁ hmn (by omega) (by omega) (Or.inr (by omega))]
  have hc := ((GlobalTheory.T.diagonal_block_conj_unipotent R n m₁ 0 m₂ m₁ (Or.inr (by omega)) (by omega) (by omega)).1 b x)
  rw [mul_assoc, hc, ← mul_assoc]

end GlobalTheory.GamMul.BlockId
