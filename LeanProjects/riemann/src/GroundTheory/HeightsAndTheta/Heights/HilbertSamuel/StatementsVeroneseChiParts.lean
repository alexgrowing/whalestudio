import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeroneseParts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStA
import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.MonoNormSq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

open Veronese

def VeroneseMonoBasis.Statement : Prop :=
  ∀ D n : ℕ, ∃ b : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card → MvPolynomial (Ix (Idx D)) ℚ,
    IsSecBasis (Veronese.x D) n b ∧
      ∀ k, aeval (Veronese.x D) (b k) = ∏ i, Veronese.t D i ^ adtEnum D (2 * n) k i

def VeroneseGramMono.Statement : Prop :=
  ∀ (D n r : ℕ) (b : Fin r → MvPolynomial (Ix (Idx D)) ℚ)
    (A : Matrix (Fin r) (Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) ℤ),
    (∀ k, aeval (Veronese.x D) (b k) =
      ∑ l, (A k l : Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D (2 * n) l i) →
    Veronese.gram D n b = A.map (Int.cast : ℤ → ℝ) *
      Matrix.diagonal (fun l => monoNormSq (adtEnum D (2 * n) l)) * (A.map (Int.cast : ℤ → ℝ)).transpose

theorem adtEnum_zero_eq (D : ℕ) (l : Fin (Finset.Nat.antidiagonalTuple (D + 1) 0).card) :
    adtEnum D 0 l = 0 := by
  have h := Finset.Nat.mem_antidiagonalTuple.mp
    (((Finset.Nat.antidiagonalTuple (D + 1) 0).equivFin.symm l).2)
  funext i
  exact (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)

example (D : ℕ) : ∀ k, aeval (Veronese.x D) ((fun _ : Fin 1 => (1 : MvPolynomial (Ix (Idx D)) ℚ)) k) =
    ∑ l : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * 0)).card,
      (((fun _ _ => 1 : Matrix (Fin 1) (Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * 0)).card) ℤ) k l : ℤ) :
        Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D (2 * 0) l i := by
  intro k
  have hc : (Finset.Nat.antidiagonalTuple (D + 1) (2 * 0)).card = 1 := by
    rw [Nat.mul_zero, Finset.Nat.antidiagonalTuple_zero_right, Finset.card_singleton]
  rw [map_one]
  have : ∀ l : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * 0)).card,
      (((1 : ℤ) : Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D (2 * 0) l i) = 1 := fun l => by
    simp [adtEnum_zero_eq D l]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hc, one_smul]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
