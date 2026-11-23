import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerPullbackHolomorphicStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

noncomputable section
namespace GlobalTheory.ChernCalc

theorem eq_sum_ofLp_smul_complexCoordinateVector {n : ℕ} (w : V n) : w = ∑ a, w a • coordVec a := by
  ext i
  simp [coordVec, EuclideanSpace.single_apply, Pi.single_apply]

theorem trace_mul_constMatrix_mul_evenForms_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (P Q : Matrix r r (Ev n)) (C : Matrix r r ℂ) :
    (((P * C.map (algebraMap ℂ (Ev n)) * Q).trace : Ev n) : Alt n) = ∑ p, ∑ q, C p q • (((Q * P) q p : Ev n) : Alt n) := by
  rw [Matrix.trace_mul_cycle, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply (M := Q * P), Matrix.map_apply, AddSubmonoidClass.coe_finset_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [mul_comm, ← Algebra.smul_def, Subalgebra.coe_smul]

def connectionMatrixDifferenceLinearMap {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n) :
    V n →ₗ[ℂ] Matrix r r ℂ where
  toFun ξ := conn G v ξ - conn G' v ξ
  map_add' ξ ξ' := by rw [conn_add_vec, conn_add_vec]; abel
  map_smul' c ξ := by rw [conn_smul_vec, conn_smul_vec, smul_sub]; rfl

theorem transAt_comp_holo : ∀ (n n' : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (φ : V n' → V n) (w : V n'), ContDiffAt ℂ 2 φ w → MContDiffAt ∞ G (φ w) → IsUnit (G (φ w)).det → MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det → ∀ k, transAt (fun x => G (φ x)) (fun x => G' (φ x)) w k = pull (fderiv ℂ φ w) (transAt G G' (φ w) k) := by
  intro n n' r _ _ G G' φ w hφ hG hGu hG' hG'u k
  have hI := (GlobalTheory.T.curvature_power_pullback_holomorphic n n' r G' φ w hφ hG' hG'u).1
  have hφ1 : DifferentiableAt ℂ φ w := hφ.differentiableAt two_ne_zero
  have h1 : MContDiffAt 1 G (φ w) := hG.of_le (by exact_mod_cast le_top)
  have h1' : MContDiffAt 1 G' (φ w) := hG'.of_le (by exact_mod_cast le_top)
  have hc : ∀ ξ, conn (fun x => G (φ x)) w ξ - conn (fun x => G' (φ x)) w ξ =
      ∑ b, fderiv ℂ φ w ξ b • connectionMatrixDifferenceLinearMap G G' (φ w) (coordVec b) := by
    intro ξ
    rw [conn_comp_holo h1 hφ1, conn_comp_holo h1' hφ1]
    show connectionMatrixDifferenceLinearMap G G' (φ w) (fderiv ℂ φ w ξ) = _
    conv_lhs => rw [eq_sum_ofLp_smul_complexCoordinateVector (fderiv ℂ φ w ξ)]
    rw [map_sum]
    simp only [map_smul]
  have hd : ∀ b, conn G (φ w) (coordVec b) - conn G' (φ w) (coordVec b) = connectionMatrixDifferenceLinearMap G G' (φ w) (coordVec b) :=
    fun _ => rfl
  simp only [transAt, hc, hd, map_sum, map_mul, (pull_dz _ _).1, trace_mul_constMatrix_mul_evenForms_sum, AlgHom.map_smul_of_tower]
  simp only [hI _ _ _ _ G hG hGu, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_smul, Finset.sum_mul,
    Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul, Finset.smul_sum]
  conv_lhs => enter [2, a, 2, i, 2, p]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, b]; rw [Finset.sum_comm]

end GlobalTheory.ChernCalc
end
