import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFramesTriangularChange
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
theorem _root_.GlobalTheory.T.flag_frames_triangular_change : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (fl : Vert.Flag F m) (V : X.Opens) (v v' : Fin m → Γ(F, V)), Spans fl V v → Spans fl V v' → ∃ M : Matrix (Fin m) (Fin m) Γ(X, V), M.BlockTriangular id ∧ IsUnit M.det ∧ ∀ j, v' j = ∑ k, M k j • v k := by
  first | exact @GlobalTheory.FlagCell.spans_change | exact GlobalTheory.FlagCell.spans_change | (intros; apply GlobalTheory.FlagCell.spans_change <;> assumption)
