import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions

open Finset Filter Topology ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.P.JacobiSumIdentities

private def jHom (q : ℕ) : ℤ →* ℤ where
  toFun a := jacobiSym a q
  map_one' := jacobiSym.one_left q
  map_mul' a b := jacobiSym.mul_left a b q

private lemma cn_nonneg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ Formalism.HermitianLattices.GL2PrimeSums.cn x n := by
  unfold Formalism.HermitianLattices.GL2PrimeSums.cn
  exact mul_nonneg vonMangoldt_nonneg (le_min zero_le_one (div_nonneg hx (Nat.cast_nonneg n)))

private lemma sP_nonneg (x : ℝ) (hx : 0 ≤ x) (p : ℕ) : 0 ≤ Formalism.HermitianLattices.GL2a2.sP x p := by
  unfold Formalism.HermitianLattices.GL2a2.sP
  exact Finset.sum_nonneg (fun i _ => cn_nonneg x hx _)

end Formalism.HermitianLattices.P.JacobiSumIdentities
