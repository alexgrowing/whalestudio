import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem smooth_coeff_closure : ∀ (n : ℕ) (v : V n), (∀ γ : Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((fun _ : V n => γ) x) S) v)) ∧ (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α j x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ j ∈ s, α j x) S) v)) ∧ (∀ (g : V n → ℂ) (α : V n → Alt n), ContDiffAt ℝ ∞ g v → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (g x • α x) S) v)) ∧ (∀ α β : V n → Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (β x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x * β x) S) v)) := by
  intro n v
  have hc : ∀ γ : Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((fun _ : V n => γ) x) S) v) :=
    fun γ S => contDiffAt_const
  have hs : ∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α j x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ j ∈ s, α j x) S) v) := by
    intro J s α h S
    simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    exact ContDiffAt.sum fun j hj => h j hj S
  have hg : ∀ (g : V n → ℂ) (α : V n → Alt n), ContDiffAt ℝ ∞ g v → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (g x • α x) S) v) := by
    intro g α h1 h2 S
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact h1.mul (h2 S)
  refine ⟨hc, hs, hg, ?_⟩
  intro α β ha hb U
  have key : ∀ x, α x * β x = ∑ S, (bas n).repr (α x) S • ∑ T, (bas n).repr (β x) T • (bas n S * bas n T) := by
    intro x
    conv_lhs => rw [← (bas n).sum_repr (α x), ← (bas n).sum_repr (β x)]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [smul_mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [mul_smul_comm]
  simp only [key]
  refine hs _ Finset.univ (fun S x => (bas n).repr (α x) S • ∑ T, (bas n).repr (β x) T • (bas n S * bas n T)) (fun S _ => ?_) U
  refine hg _ _ (ha S) ?_
  refine hs _ Finset.univ (fun T x => (bas n).repr (β x) T • (bas n S * bas n T)) (fun T _ => ?_)
  exact hg _ (fun _ => bas n S * bas n T) (hb T) (hc _)

end GlobalTheory.ChernCalc
