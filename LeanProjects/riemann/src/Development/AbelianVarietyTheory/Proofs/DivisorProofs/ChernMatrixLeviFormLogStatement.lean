import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixLeviFormLog
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_matrix_levi_form_log : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : X.Modules) (g : Met p σ L 1), g.IsCInf → ∀ (U : X.Opens) (t : Γ(L, U)), IsFrame (fun _ : Fin 1 => t) → ∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → ∀ ξ : V D, (∑ j, ∑ l, ξ j * chernMat g.detWeight c y j l * starRingEnd ℂ (ξ l)).re = -(leviForm (fun v => Real.log (g.form t t (c.e.symm v)).re) (c.e y) ξ ξ).re := by
  first | exact @GlobalTheory.MixDens.chernMat_eq_neg_leviForm | exact GlobalTheory.MixDens.chernMat_eq_neg_leviForm | (intros; apply GlobalTheory.MixDens.chernMat_eq_neg_leviForm <;> assumption)
