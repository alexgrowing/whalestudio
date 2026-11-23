import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatA
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlkB

noncomputable section

open Matrix ComplexConjugate

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem jj_mul_jj : JJ n * JJ n = -1 := by
  unfold JJ
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem inG_mul {g h : M2 n} (hg : InG g) (hh : InG h) : InG (g * h) := by
  unfold InG at *
  rw [conjTranspose_mul, show hᴴ * gᴴ * JJ n * (g * h) = hᴴ * (gᴴ * JJ n * g) * h by simp only [Matrix.mul_assoc], hg, hh]

theorem inG_left_inv {g : M2 n} (hg : InG g) : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
  unfold InG at hg
  rw [show -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) by simp only [Matrix.mul_assoc], hg, neg_mul, jj_mul_jj,
    neg_neg]

theorem inG_mul_inv {g : M2 n} (hg : InG g) : g * g⁻¹ = 1 := by
  rw [Matrix.inv_eq_left_inv (inG_left_inv hg)]
  exact mul_eq_one_comm.1 (inG_left_inv hg)

theorem inG_inv {g : M2 n} (hg : InG g) : InG g⁻¹ := by
  have h1 := inG_mul_inv hg
  unfold InG at *
  calc (g⁻¹)ᴴ * JJ n * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * JJ n * g) * g⁻¹ := by rw [hg]
    _ = (g * g⁻¹)ᴴ * JJ n * (g * g⁻¹) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [h1]; simp

theorem mul_compl_zero (j : ℕ) (Q S : Matrix (Fin n) (Fin n) ℂ) (hQ : ∀ a b, Q a b ≠ 0 → b ∈ blkA j)
    (hS : ∀ a b, S a b ≠ 0 → a ∈ blkB j) : Q * S = 0 :=
  _root_.UpperTheory.Reformulated.B.Yha8.main j Q S hQ hS

theorem mX_factor (j : ℕ) (P Q R S : Matrix (Fin n) (Fin n) ℂ) (hP : ∀ a b, P a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j)
    (hS : ∀ a b, S a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) (hQ : ∀ a b, Q a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkA j)
    (hR : ∀ a b, R a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkB j) :
    mX (1 + P) Q R (1 + S) = mX 1 Q R 1 * mX (1 + P) 0 0 (1 + S) := by
  have hQS : Q * S = 0 := mul_compl_zero j Q S (fun a b h => (hQ a b h).2) (fun a b h => (hS a b h).1)
  have hRP : R * P = 0 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hr : R a k = 0
    · simp [hr]
    by_cases hp : P k b = 0
    · simp [hp]
    exact absurd (hP k b hp).1 (by have := (hR a k hr).2; simp [blkB] at this; exact this)
  unfold mX
  rw [cm_inv, show Cm n * fromBlocks 1 Q R 1 * CmI n * (Cm n * fromBlocks (1 + P) 0 0 (1 + S) * CmI n) =
      Cm n * (fromBlocks 1 Q R 1 * (CmI n * Cm n) * fromBlocks (1 + P) 0 0 (1 + S)) * CmI n by
        simp only [Matrix.mul_assoc], cmI_mul_cm, Matrix.mul_one, fromBlocks_multiply]
  simp [Matrix.mul_add, hQS, hRP]

end PositivityTheory.Rg.Sw.LVs.TC
