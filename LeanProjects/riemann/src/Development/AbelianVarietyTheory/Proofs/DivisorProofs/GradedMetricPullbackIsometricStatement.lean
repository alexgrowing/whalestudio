import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_metric_pullback_isometric : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r) (π : Y ⟶ X) (hπ : π ≫ p = q) (i : Fin r), (VMetric.grLB (fl.pull π) i (H.pull π hπ)).Isometric ((VMetric.grLB fl i H).pull π hπ) := by
  first | exact @GlobalTheory.VMetric.isometric_grLB_pull | exact GlobalTheory.VMetric.isometric_grLB_pull | (intros; apply GlobalTheory.VMetric.isometric_grLB_pull <;> assumption)
