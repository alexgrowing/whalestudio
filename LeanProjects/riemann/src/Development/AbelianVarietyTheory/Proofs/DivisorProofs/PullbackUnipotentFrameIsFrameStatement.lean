import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUnipotentFrameIsFrame
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
theorem _root_.GlobalTheory.T.pullback_unipotent_frame_isFrame : ∀ (X B : Scheme.{0}) (g : X ⟶ B) (E : B.Modules) (m : ℕ), IsVB E m → ∀ (U : B.Opens) (e : Fin m → Γ(E, U)), IsFrame e → ∀ (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) (n : Low m → Γ(X, V)), IsFrame (pullCol g e hV (uniR n)) := by
  first | exact @GlobalTheory.UniColFrame.isFrame_pullCol_uniR | exact GlobalTheory.UniColFrame.isFrame_pullCol_uniR | (intros; apply GlobalTheory.UniColFrame.isFrame_pullCol_uniR <;> assumption)
