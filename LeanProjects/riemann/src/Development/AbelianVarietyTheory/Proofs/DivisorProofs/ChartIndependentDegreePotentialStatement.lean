import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartIndependentDegreePotential
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_independent_degree_potential : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ} {Z : Type} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] (A : FinHolAtlas Y.dim Z) (h : Z ≃ₜ Pts Y σ), (∀ j, ∃ c : GlobalTheory.AlgChart Y.str σ Y.dim, A.chart j = h.transOpenPartialHomeomorph c.finChart) → ∀ (Φ : Fin Y.dim → LocPot Z), (∀ i, IsPotential A (Φ i)) → ∀ (d : GlobalTheory.AlgChart Y.str σ Y.dim → Pts Y σ → ℝ), (∀ c c' y, y ∈ c.e.source → y ∈ c'.e.source → d c y = ‖transDet c.e c'.e y‖ ^ 2 * d c' y) → (∀ j (c : GlobalTheory.AlgChart Y.str σ Y.dim), A.chart j = h.transOpenPartialHomeomorph c.finChart → ∀ z ∈ (A.chart j).target, locDens A Φ j z = d c (c.finChart.symm z)) → (glueMeas (fun c : GlobalTheory.AlgChart Y.str σ Y.dim => c.e) fun c y => ENNReal.ofReal (((1 : ℤˣ) : ℤ) * d c y)).real Set.univ - (glueMeas (fun c : GlobalTheory.AlgChart Y.str σ Y.dim => c.e) fun c y => ENNReal.ofReal (((-1 : ℤˣ) : ℤ) * d c y)).real Set.univ = mInt A Φ (fun _ => 1) := by
  first | exact @GlobalTheory.ChernWeilLine.glueMeas_real_sub_eq_mInt | exact GlobalTheory.ChernWeilLine.glueMeas_real_sub_eq_mInt | (intros; apply GlobalTheory.ChernWeilLine.glueMeas_real_sub_eq_mInt <;> assumption)
