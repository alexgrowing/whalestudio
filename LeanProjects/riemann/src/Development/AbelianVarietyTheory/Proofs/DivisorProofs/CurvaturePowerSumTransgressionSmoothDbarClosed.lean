import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureMatrixPowProductEntrySmoothDbarClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoefficientFormsClosedUnderOperationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarOperatorLocalCalculusComplexFormsStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernCalc

theorem powAt_coe_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (x : V n) (k : ℕ) :
    ((powAt G x k : Ev n) : Alt n) = ∑ i, (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) := by
  simp [powAt, Matrix.trace]

theorem transAt_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (x : V n) (k : ℕ) :
    transAt G G' x k = ∑ a, ∑ i ∈ Finset.range k, ∑ p, ∑ q,
      (conn G x (coordVec a) - conn G' x (coordVec a)) p q •
        ((((curvEv G' x ^ (k - 1 - i) * curvEv G x ^ i) q p : Ev n) : Alt n) * dz a) := by
  unfold transAt
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, AddSubmonoidClass.coe_finset_sum,
    Finset.sum_mul, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Algebra.smul_def, mul_assoc]

theorem powAt_transAt_smooth : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ k, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((powAt G x k : Alt n)) S) v) ∧ dbarAt (fun x => (powAt G x k : Alt n)) v = 0 ∧ (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (transAt G G' x k) S) v) := by
  intro n r _ _ G G' v hG hGu hG' hG'u k
  obtain ⟨hconst, hsum, hsmul, hmul⟩ := GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v
  obtain ⟨_, hdsum, _, _, _⟩ := GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v
  have hpe : ∀ i, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr
      (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) S) v) ∧
      dbarAt (fun x => (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n)) v = 0 :=
    fun i => GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed n r G G' v hG hGu hG' hG'u k 0 i i
  have hpf : (fun x => ((powAt G x k : Ev n) : Alt n)) =
      fun x => ∑ i ∈ Finset.univ, (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) :=
    funext fun x => powAt_coe_eq_sum G G' x k
  refine ⟨?_, ?_, ?_⟩
  · simp only [powAt_coe_eq_sum G G']
    exact hsum r Finset.univ _ fun i _ => (hpe i).1
  · rw [hpf, hdsum r Finset.univ _ fun i _ S => ((hpe i).1 S).differentiableAt (by simp)]
    exact Finset.sum_eq_zero fun i _ => (hpe i).2
  · have hη : ∀ a p q, ContDiffAt ℝ ∞
        (fun x => (conn G x (coordVec a) - conn G' x (coordVec a)) p q) v := fun a p q =>
      ((hG.conn hGu (j := ∞) (by simp) (coordVec a)).sub
        (hG'.conn hG'u (j := ∞) (by simp) (coordVec a))) p q
    simp only [transAt_eq_sum]
    refine hsum _ Finset.univ _ fun a _ => hsum _ _ _ fun i _ => hsum _ Finset.univ _ fun p _ =>
      hsum _ Finset.univ _ fun q _ => hsmul _ _ (hη a p q) ?_
    exact hmul _ _ (GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed n r G' G v hG' hG'u hG hGu (k - 1 - i) i q p).1 (hconst (dz a))

end GlobalTheory.ChernCalc
