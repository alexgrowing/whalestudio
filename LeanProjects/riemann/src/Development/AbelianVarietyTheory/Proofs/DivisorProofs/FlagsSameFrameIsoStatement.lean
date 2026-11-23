import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsSameFrameIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flags_same_frame_iso : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (fl₁ fl₂ : Vert.Flag F m) (v : Fin m → Γ(F, ⊤)), Spans fl₁ ⊤ v → Spans fl₂ ⊤ v → ∀ i, ∃ e : fl₁.F i ≅ fl₂.F i, e.hom ≫ fl₂.ι i = fl₁.ι i := by
  first | exact @GlobalTheory.FlagCell.steps_iso_of_spans_top | exact GlobalTheory.FlagCell.steps_iso_of_spans_top | (intros; apply GlobalTheory.FlagCell.steps_iso_of_spans_top <;> assumption)
