import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem coefwise_dbar_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {c : ι → V n → ℂ} {F : ι → V n → Alt n} {v : V n}
    (hc : ∀ i, DifferentiableAt ℝ (c i) v)
    (hF : ∀ i S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) (w : V n) :
    coefwise (fun f => GlobalTheory.dbar f v w) (fun x => ∑ i, c i x • F i x) =
      ∑ i, (GlobalTheory.dbar (c i) v w • F i v + c i v • coefwise (fun f => GlobalTheory.dbar f v w) (F i)) := by
  have h (S : Finset (Fin (n + n))) :
      GlobalTheory.dbar (fun x => (bas n).repr (∑ i, c i x • F i x) S) v w =
        ∑ i, (c i v * GlobalTheory.dbar (fun x => (bas n).repr (F i x) S) v w +
          GlobalTheory.dbar (c i) v w * (bas n).repr (F i v) S) := by
    have e : (fun x => (bas n).repr (∑ i, c i x • F i x) S) =
        fun x => ∑ i, c i x * (bas n).repr (F i x) S := by
      funext x
      simp [map_sum, Finsupp.finset_sum_apply]
    rw [e, GlobalTheory.dbar_sum (A := fun i x => c i x * (bas n).repr (F i x) S) (fun i _ => (hc i).mul (hF i S)),
      ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => GlobalTheory.dbar_mul (hc i) (hF i S) w
  simp only [coefwise, h, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← (bas n).sum_repr (F i v)]
  simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  rw [add_comm]

theorem dbarAt_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {c : ι → V n → ℂ} {F : ι → V n → Alt n} {v : V n}
    (hc : ∀ i, DifferentiableAt ℝ (c i) v)
    (hF : ∀ i S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) :
    dbarAt (fun x => ∑ i, c i x • F i x) v =
      ∑ i, ((∑ a, GlobalTheory.dbar (c i) v (coordVec a) • dzb a) * F i v + c i v • dbarAt (F i) v) := by
  simp only [dbarAt, coefwise_dbar_sum_smul hc hF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_add, mul_smul_comm, smul_mul_assoc, Finset.sum_mul, Finset.sum_add_distrib, Finset.smul_sum]

end GlobalTheory.CxForm
