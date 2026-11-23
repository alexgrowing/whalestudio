import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellChart
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isCell_chart_of_bijective_eval₂ : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (σ : k →+* ℂ) (c : AlgChart q σ 1) (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ c.U), IsAffineOpen W → ∀ n : (Σ a, Low (r a)) → Γ(Y, W), Function.Bijective (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom n) → c.e.source.Nonempty → ∃ c' : AlgChart p σ (d + 1), IsCell e π w c c' ∧ c'.e.source ⊆ ptsIn p σ W ∧ ∀ y ∈ c'.e.source, ∀ a s, fib e (c'.e y) a s = ev p σ W (n ⟨a, s⟩) y := by
  first | exact @GlobalTheory.cell_chart | exact GlobalTheory.cell_chart | (intros; apply GlobalTheory.cell_chart <;> assumption)
