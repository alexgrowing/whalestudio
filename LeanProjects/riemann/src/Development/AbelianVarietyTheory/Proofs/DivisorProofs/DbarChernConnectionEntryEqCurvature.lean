import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem coefwise_dbar_sum_smul_bas {n : ℕ} {J : Type} [Fintype J] (u : J → V n → ℂ) (S : J → Finset (Fin (n + n)))
    (v η : V n) (hu : ∀ a, DifferentiableAt ℝ (u a) v) :
    coefwise (fun f => GlobalTheory.dbar f v η) (fun x => ∑ a, u a x • bas n (S a)) =
      ∑ a, GlobalTheory.dbar (u a) v η • bas n (S a) := by
  refine (bas n).ext_elem fun S' => ?_
  simp only [coefwise, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finset_sum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hd (a : J) : DifferentiableAt ℝ (fun x => if S a = S' then u a x else 0) v := by
    split_ifs
    exacts [hu a, differentiableAt_const _]
  rw [GlobalTheory.dbar_sum fun a _ => hd a, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp

theorem dbarAt_conn : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, dbarAt (fun x => ∑ a, conn G x (coordVec a) i j • dz a) v = (curvEv G v i j : Alt n) := by
  intro n r _ _ G v hG hu i j
  have hc (a : Fin n) : DifferentiableAt ℝ (fun x => conn G x (coordVec a) i j) v :=
    (hG.conn hu (j := 1) (by norm_cast) (coordVec a)).diff i j
  have h (b : Fin n) := coefwise_dbar_sum_smul_bas (fun a x => conn G x (coordVec a) i j)
    (fun a => {finSumFinEquiv (.inl a)}) v (coordVec b) hc
  simp only [bas_singleton] at h
  have e : (curvEv G v i j : Alt n) = ∑ a, ∑ b, curv G v (coordVec a) (coordVec b) i j • (dz a * dzb b) := by
    simp only [curvEv, curvPoly, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, aeval_C, aeval_X,
      ← Algebra.smul_def, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym]
  rw [e, Finset.sum_comm]
  simp only [dbarAt, dz, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_smul_comm, dzb, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _), smul_neg, ← neg_smul]
  rfl

end GlobalTheory.ChernCalc
