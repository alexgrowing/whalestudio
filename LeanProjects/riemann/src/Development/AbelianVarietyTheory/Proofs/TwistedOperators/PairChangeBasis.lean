import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement

namespace GlobalTheory.TracePairingBasisChange

open Matrix

theorem pair_eq_trace {K : Type} [Field K] {n d : ℕ} (X Y : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM X Y = Matrix.trace (Xᵀ * Y) := by
  unfold GlobalTheory.FlipMatch.pairM
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem pair_change_basis {K : Type} [Field K] {n d : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin d) (Fin d) K) (b : GL (Fin n) K) (c : GL (Fin d) K)
    (P Q : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM
                 ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * Matrix.transpose (↑c⁻¹ : Matrix (Fin d) (Fin d) K))
                 (-(Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) * A * Q * Matrix.transpose B *
                   (↑c : Matrix (Fin d) (Fin d) K))) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  rw [pair_eq_trace, Matrix.mul_neg, Matrix.trace_neg, neg_inj]
  have hb : Matrix.transpose (↑b⁻¹ : Matrix (Fin n) (Fin n) K) * Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hc : (↑c : Matrix (Fin d) (Fin d) K) * (↑c⁻¹ : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv c

  have key : Matrix.transpose ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * Matrix.transpose (↑c⁻¹ : Matrix (Fin d) (Fin d) K)) *
      (Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) * A * Q * Matrix.transpose B * (↑c : Matrix (Fin d) (Fin d) K)) =
      (↑c⁻¹ : Matrix (Fin d) (Fin d) K) * ((Matrix.transpose P * (A * (Q * Matrix.transpose B))) * (↑c : Matrix (Fin d) (Fin d) K)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.transpose (↑b⁻¹ : Matrix (Fin n) (Fin n) K)), hb, Matrix.one_mul]
  rw [key, Matrix.trace_mul_comm, Matrix.mul_assoc, hc, Matrix.mul_one]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.TracePairingBasisChange
