import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

variable {P Q : ℕ}

theorem act_sum_blocks (Z : Mat P Q) (A E : Matrix (Fin P) (Fin Q) ℂ) (x d : Ix P Q → ℂ) (t : ℂ) :
    (∑ i, ∑ k, Z (.inl k) (.inl i) * (x (.inl i) * d (.inl k) + ∑ j, A i j * E k j + if i = k then t / 2 else 0) -
      ∑ i, ∑ j, Z (.inr j) (.inl i) * (x (.inl i) * (x (.inr j) * t + ∑ m, A m j * d (.inl m)) +
        (∑ k, A i k * (x (.inr j) * d (.inr k) + ∑ m, A m j * E m k) + A i j * t))) +
    (∑ j, ∑ i, Z (.inl i) (.inr j) * E i j -
      ∑ j, ∑ k, Z (.inr k) (.inr j) * (x (.inr k) * d (.inr j) + ∑ i, A i k * E i j + if j = k then t / 2 else 0)) =
    (Z.trace / 2 + dS Z A x) * t + (∑ i, ∑ j, dA Z A i j * E i j + ∑ l, dX Z A x l * d l) := by
  induction Z using Matrix.induction_on' with
  | h_zero =>
    have h11 : (0 : Mat P Q).toBlocks₁₁ = 0 := rfl
    have h12 : (0 : Mat P Q).toBlocks₁₂ = 0 := rfl
    have h21 : (0 : Mat P Q).toBlocks₂₁ = 0 := rfl
    have h22 : (0 : Mat P Q).toBlocks₂₂ = 0 := rfl
    simp [dS, dA, dX, h11, h12, h21, h22]
  | h_add Z W hZ hW =>
    have h11 : (Z + W).toBlocks₁₁ = Z.toBlocks₁₁ + W.toBlocks₁₁ := rfl
    have h12 : (Z + W).toBlocks₁₂ = Z.toBlocks₁₂ + W.toBlocks₁₂ := rfl
    have h21 : (Z + W).toBlocks₂₁ = Z.toBlocks₂₁ + W.toBlocks₂₁ := rfl
    have h22 : (Z + W).toBlocks₂₂ = Z.toBlocks₂₂ + W.toBlocks₂₂ := rfl
    have hS : dS (Z + W) A x = dS Z A x + dS W A x := by
      simp only [dS, h21, h22, Matrix.add_mul, Matrix.trace_add, Matrix.add_mulVec, dotProduct_add]; ring
    have hA : dA (Z + W) A = dA Z A + dA W A := by
      simp only [dA, h11, h12, h21, h22, Matrix.add_mul, Matrix.mul_add]; abel
    have hX : dX (Z + W) A x = dX Z A x + dX W A x := by
      simp only [dX, h11, h21, h22, Matrix.add_mul, Matrix.mul_add, Matrix.add_mulVec, Matrix.sub_mulVec,
        Matrix.vecMul_add]
      ext (i | j) <;> simp <;> ring
    simp only [hS, hA, hX, Matrix.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib, Matrix.trace_add]
    simp only [add_mul] at hZ hW
    linear_combination hZ + hW
  | h_std_basis a b c =>
    rcases a with a | a <;> rcases b with b | b <;>
    simp [dS, dA, dX, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.single_apply, Matrix.mul_apply, Matrix.trace, Matrix.mulVec, Matrix.vecMul, dotProduct, ite_and,
      Fintype.sum_sum_type]
    · simp only [mul_add, Finset.mul_sum, mul_assoc]
      split_ifs <;> ring
    · rw [Finset.sum_comm (f := fun i k => A i a * (c * A b k) * E i k)]
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc, mul_left_comm]
      ring
    · simp only [mul_add, Finset.mul_sum, mul_assoc, mul_left_comm]
      split_ifs <;> ring

open MvPolynomial GlobalTheory.Oscillator in

theorem inner_omAct0_adjZ : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H), (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v = x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) → (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v = x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) → ∀ (Z : Mat P Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (omAct0 P Q (adjZ Z) f)) v = (Z.trace / 2 + dS Z A x) * inner ℂ (F.ι f) v + (∑ i, ∑ j, dA Z A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) v + ∑ l, dX Z A x l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) v) := by
  intro P Q F A x v h1 h2 Z f
  have hh : ∀ (p : Prop) [Decidable p], inner ℂ (F.ι (if p then (1 / 2 : ℂ) • f else 0)) v =
      if p then inner ℂ (F.ι f) v / 2 else 0 := by
    intro p _
    split_ifs
    · rw [map_smul, inner_smul_left]; simp [map_ofNat]; ring
    · simp
  have hd : ∀ k j : Fin Q, inner ℂ (F.ι (pderiv (Sum.inr k) (X (Sum.inr j) * f))) v =
      x (.inr j) * inner ℂ (F.ι (pderiv (.inr k) f)) v +
        ∑ m, A m j * inner ℂ (F.ι (pderiv (.inl m) (pderiv (.inr k) f))) v +
        if k = j then inner ℂ (F.ι f) v else 0 := by
    intro k j
    rw [← h2, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, inner_add_left, pderiv_X]
    by_cases h : k = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← act_sum_blocks Z A (fun i j => inner ℂ (F.ι (pderiv (Sum.inl i) (pderiv (Sum.inr j) f))) v) x
    (fun l => inner ℂ (F.ι (pderiv l f)) v) (inner ℂ (F.ι f) v), omAct0_eq, oscAct_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sum_inner, inner_smul_left,
    adjZ_apply, Fintype.sum_sum_type, Finset.sum_add_distrib, LinearMap.add_apply, map_add, inner_add_left]
  simp only [unitOp_inl_inl, unitOp_inl_inr, unitOp_inr_inl, unitOp_inr_inr, map_add, map_sub, map_neg,
    inner_add_left, inner_sub_left, inner_neg_left, hh, h1, h2, hd, sgn, map_mul, Complex.conj_conj,
    Int.cast_one, Int.cast_neg, map_one, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  have hc : ∀ (j : Fin Q) (i : Fin P), pderiv (Sum.inr j) (pderiv (Sum.inl i) f) =
      pderiv (Sum.inl i) (pderiv (Sum.inr j) f) := fun j i => pderiv_pderiv_comm _ _ _
  rw [add_add_add_comm]
  simp only [hc, mul_add (A _ _), Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 2 <;> refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_ <;> ring

end GlobalTheory.OscGauss
