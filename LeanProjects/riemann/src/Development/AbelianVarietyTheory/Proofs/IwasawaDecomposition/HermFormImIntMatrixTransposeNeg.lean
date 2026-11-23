import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hermForm_swap_of_isHermitian {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) : hermForm Hm w z = star (hermForm Hm z w) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, star_sum, star_mul', Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (congrFun hH i) j
  simp only [Matrix.conjTranspose_apply] at h
  rw [← h, star_star]
  ring

theorem hermForm_im_antisymm : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ)
    (M : Matrix (Fin r) (Fin r) ℤ), Hm.IsHermitian →
    (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → Mᵀ = -M := by
  intro g r Hm l M hH hM
  ext i j
  have h1 := hM j i
  rw [hermForm_swap_of_isHermitian Hm hH] at h1
  have h2 := hM i j
  simp only [Complex.star_def, Complex.conj_im] at h1
  have : ((M j i : ℤ) : ℝ) = ((-M i j : ℤ) : ℝ) := by push_cast; linarith
  simpa [Matrix.transpose_apply] using Int.cast_injective this

example : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), Hm.IsHermitian → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → Mᵀ = -M := hermForm_im_antisymm

end GlobalTheory
