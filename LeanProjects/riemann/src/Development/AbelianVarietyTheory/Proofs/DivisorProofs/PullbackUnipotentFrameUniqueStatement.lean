import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUnipotentFrameUnique
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
theorem _root_.GlobalTheory.T.pullback_unipotent_frame_unique : ∀ (X B : Scheme.{0}) (g : X ⟶ B) (E : B.Modules) (m : ℕ), IsVB E m → ∀ (U : B.Opens) (e : Fin m → Γ(E, U)), IsFrame e → ∀ (fl : Vert.Flag ((Scheme.Modules.pullback g).obj E) m) (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) (n n' : Low m → Γ(X, V)), Spans fl V (pullCol g e hV (uniR n)) → Spans fl V (pullCol g e hV (uniR n')) → n = n' := by
  first | exact @GlobalTheory.FlagCell.low_eq_of_spans_pullCol | exact GlobalTheory.FlagCell.low_eq_of_spans_pullCol | (intros; apply GlobalTheory.FlagCell.low_eq_of_spans_pullCol <;> assumption)
