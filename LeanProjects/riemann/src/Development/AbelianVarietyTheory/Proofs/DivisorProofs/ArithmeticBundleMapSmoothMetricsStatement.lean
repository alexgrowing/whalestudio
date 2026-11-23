import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleMapSmoothMetrics
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSectionLiftsMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineBundleInducedArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleMetricSetupStatement
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TwoLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_bundle_map_smooth_metrics : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration → ∀ (D : D7) (O : Setup D), O.Core → ∀ R : ℝ, 2 ≤ R → ∀ (c : O.s.Comp) (B : Scheme.{0}) [IsIntegral B] (q : B ⟶ Sp (𝓞 D.what₂.LL)) (E E' : (D.host.E →+* ℂ) → B.Modules) (h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ)) (h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)) (H : ∀ σ, (h σ).IsCInf) (H' : ∀ σ, (h' σ).IsCInf) (u : ∀ σ, E σ ⟶ E' σ), IsArithVar q (dimGr D.what₂.Tau O.N O.j) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B → (∀ σ, IsoHom (h σ) (h' σ) (u σ)) → PairBase O R c q E E' h h' u → PairCover O R c q E E' H H' u := by
  first | exact @GlobalTheory.PairCov.pairCover | exact GlobalTheory.PairCov.pairCover | (intros; apply GlobalTheory.PairCov.pairCover <;> assumption)
