import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagSpannedFrame
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
theorem _root_.GlobalTheory.T.exists_flag_spanned_frame : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (v : Fin m → Γ(F, ⊤)), IsFrame v → ∃ fl : Vert.Flag F m, Spans fl ⊤ v := by
  first | exact @GlobalTheory.FlagCell.exists_flag_spans_of_frame | exact GlobalTheory.FlagCell.exists_flag_spans_of_frame | (intros; apply GlobalTheory.FlagCell.exists_flag_spans_of_frame <;> assumption)
