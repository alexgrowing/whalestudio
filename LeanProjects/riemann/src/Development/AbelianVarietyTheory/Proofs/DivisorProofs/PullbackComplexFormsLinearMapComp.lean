import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm

theorem pull_comp_entry {k m n : ℕ} (L : V n →L[ℂ] V m) (L' : V m →L[ℂ] V k) (b : Fin n) (a : Fin k) :
    (L' (L (coordVec b))).ofLp a = ∑ c, (L (coordVec b)).ofLp c * (L' (coordVec c)).ofLp a := by
  have hx : L (coordVec b) = ∑ c, (L (coordVec b)).ofLp c • (coordVec c : V m) := by
    simpa [coordVec] using (EuclideanSpace.basisFun (Fin m) ℂ).sum_repr (L (coordVec b)) |>.symm
  rw [hx, map_sum]
  simp [map_smul, PiLp.smul_apply]
  simp [Pi.single_apply]

theorem pull_comp (k m n : ℕ) (L : V n →L[ℂ] V m) (L' : V m →L[ℂ] V k) (γ : Alt k) :
    pull (L'.comp L) γ = pull L (pull L' γ) := by
  have hM : (Matrix.fromBlocks (Matrix.of fun b a => ((L'.comp L) (coordVec b)).ofLp a) 0 0
        (Matrix.of fun b a => conj (((L'.comp L) (coordVec b)).ofLp a)) : Matrix (Fin n ⊕ Fin n) (Fin k ⊕ Fin k) ℂ) =
      Matrix.fromBlocks (Matrix.of fun b a => (L (coordVec b)).ofLp a) 0 0
        (Matrix.of fun b a => conj ((L (coordVec b)).ofLp a)) *
      Matrix.fromBlocks (Matrix.of fun b a => (L' (coordVec b)).ofLp a) 0 0
        (Matrix.of fun b a => conj ((L' (coordVec b)).ofLp a)) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · ext b a; simp only [Matrix.of_apply, ContinuousLinearMap.comp_apply, pull_comp_entry]
      simp [Matrix.mul_apply]
    · simp
    · simp
    · ext b a
      simp only [Matrix.mul_apply, Matrix.of_apply, ContinuousLinearMap.comp_apply, pull_comp_entry, map_sum, map_mul]
      simp [Matrix.mul_apply]
  simp only [pull]
  rw [hM, Matrix.toLin'_mul, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]

end GlobalTheory.CxForm
