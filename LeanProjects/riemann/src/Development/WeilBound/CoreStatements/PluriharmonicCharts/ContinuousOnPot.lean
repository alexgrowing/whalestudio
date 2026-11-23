import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsMultiHomogMapConj

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder ContDiff

namespace PositivityTheory.Xgp.c_bm_exists_boundary

open MvPolynomial Filter Topology

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem contDiff_nd (a : K → ℕ) : ContDiff ℝ ∞ (nd (J := J) a) := by
  unfold nd
  refine contDiff_prod fun k _ => ?_
  refine (ContDiff.sum fun i _ => ?_).pow _
  exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ _)

variable {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)

theorem smoothOn_pot {V : Set X} {ι' : Type} [Fintype ι'] (f : ι' → X → ℂ) (hf : ∀ j, A.HoloOn V (f j))
    (g : X → (Σ k, J k) → ℂ) (hg : ∀ p, A.HoloOn V (fun y => g y p)) (a : ι' → K → ℕ)
    (hnd : ∀ y ∈ V, ∀ j, 0 < nd (a j) (g y)) (hpos : ∀ y ∈ V, 0 < ∑ j, ‖f j y‖ ^ 2 / nd (a j) (g y)) (c : ℝ) :
    A.SmoothOn V (fun y => c - (1 / 2) * Real.log (∑ j, ‖f j y‖ ^ 2 / nd (a j) (g y))) := by
  intro ch t ht
  apply ContDiffAt.contDiffWithinAt
  have h1 : ∀ j, ContDiffAt ℝ ∞ (fun s => ‖f j ((A.chart ch).symm s)‖ ^ 2) t := fun j =>
    (contDiff_norm_sq ℝ).contDiffAt.comp t (((hf j ch t ht).contDiffAt).restrict_scalars ℝ)
  have h2 : ContDiffAt ℝ ∞ (fun s => g ((A.chart ch).symm s)) t :=
    contDiffAt_pi.2 fun p => ((hg p ch t ht).contDiffAt).restrict_scalars ℝ
  have h3 : ∀ j, ContDiffAt ℝ ∞ (fun s => nd (a j) (g ((A.chart ch).symm s))) t := fun j =>
    (contDiff_nd (a j)).contDiffAt.comp t h2
  have hsum : ContDiffAt ℝ ∞ (fun s => ∑ j, ‖f j ((A.chart ch).symm s)‖ ^ 2 / nd (a j) (g ((A.chart ch).symm s))) t :=
    ContDiffAt.sum fun j _ => (h1 j).div (h3 j) (ne_of_gt (hnd _ ht.2 j))
  exact contDiffAt_const.sub (contDiffAt_const.mul (hsum.log (ne_of_gt (hpos _ ht.2))))

end PositivityTheory.Xgp.c_bm_exists_boundary
