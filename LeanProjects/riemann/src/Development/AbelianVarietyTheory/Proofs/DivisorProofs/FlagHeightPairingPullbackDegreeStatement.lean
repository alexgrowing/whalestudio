import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagHeightPairingPullbackDegree
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
theorem _root_.GlobalTheory.T.flag_height_pairing_pullback_degree : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (d : ℕ) (ρ : Y ⟶ X), IsArithVar p (d + 1) → FlagChain.IsCov p (d + 1) ρ → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r), h.IsCInf → ∀ (fl : Vert.Flag E r) (N : HermLB p), bcPair (h.pull ρ rfl) (fl.pull ρ) (N.pull ρ rfl) d = (ρ.residueDegree (genericPoint Y) : ℝ) * bcPair h fl N d := by
  first | exact @GlobalTheory.MixDensPull.bcPair_pull | exact GlobalTheory.MixDensPull.bcPair_pull | (intros; apply GlobalTheory.MixDensPull.bcPair_pull <;> assumption)
