import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem contDiffOn_dbar_const_dir {n : ℕ} {f : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (w : V n) : ContDiffOn ℝ ∞ (fun v => GlobalTheory.dbar f v w) U := by
  have h : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  simp only [GlobalTheory.dbar_apply]
  exact ContDiffOn.const_smul _ ((h.clm_apply contDiffOn_const).add
    (ContDiffOn.const_smul _ (h.clm_apply contDiffOn_const)))

theorem contDiffOn_repr_dbarAt {n : ℕ} {γ : V n → Alt n} {U : Set (V n)} (hU : IsOpen U)
    (hγ : ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (γ v) S) U) (T : Finset (Fin (n + n))) :
    ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt γ v) T) U := by
  have key : (fun v => (bas n).repr (dbarAt γ v) T) = fun v => ∑ a, ∑ S,
      GlobalTheory.dbar (fun x => (bas n).repr (γ x) S) v (coordVec a) * (bas n).repr (dzb a * bas n S) T := by
    funext v
    simp only [dbarAt, coefwise, map_sum, Finset.mul_sum, mul_smul_comm, map_smul,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [key]
  exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ =>
    (contDiffOn_dbar_const_dir hU (hγ S) _).mul contDiffOn_const

end GlobalTheory.CxForm
