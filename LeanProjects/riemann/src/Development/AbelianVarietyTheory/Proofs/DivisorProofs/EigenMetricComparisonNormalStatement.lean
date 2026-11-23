import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenMetricComparisonNormal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_metric_comparison_normal : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration →
  ∀ (D : D7) (O : Setup D), O.Core → ∀ R : ℝ, 2 ≤ R → ∀ (c : O.s.Comp) (B : Scheme.{0}) [IsIntegral B]
    (q : B ⟶ Sp (𝓞 D.what₂.LL)) (E E' : (D.host.E →+* ℂ) → B.Modules) (h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ))
    (h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)) (u : ∀ σ, E σ ⟶ E' σ),
    IsArithVar q (dimGr D.what₂.Tau O.N O.j) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B →
    (∀ σ, IsoHom (h σ) (h' σ) (u σ)) →
    ∀ (Bg : Scheme.{0}) (jB : Bg ⟶ B) (πB : Bg ⟶ gen O.s.T.Z) (t : ∀ σ, FrAssign O.s.T.Z (E σ) (O.S.Dw.mult σ) jB)
      (t' : ∀ σ, FrAssign O.s.T.Z (E' σ) (O.S.Dw.mult σ) jB) (G : ∀ σ', EigMet O.s.T.Z σ'),
    GlobalTheory.PairCov.PairWit O R c q E E' h h' u jB πB t t' G →
    ∀ (Y : Scheme.{0}) [IsIntegral Y] (π : Y ⟶ B)
      (fl : ∀ σ, Vert.Flag ((Scheme.Modules.pullback π).obj (E σ)) (O.S.Dw.mult σ)),
    IsFlagBundle π E O.S.Dw.mult fl → IsArithVar (π ≫ q) (O.var c).dim → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y →
    ∀ (X Gs : Scheme.{0}) [IsIntegral X] [IsIntegral Gs] (ρ : X ⟶ Y) (j : Gs ⟶ X) (s : Gs ⟶ Sp D.what₂.LL),
      IsPullback (j ≫ ρ) s (π ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) →
      IsPullback j s (ρ ≫ π ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) →
    ∃ (πG : Gs ⟶ (O.var c).X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg)
      (r : ∀ σ i, ((((fl σ).pull ρ).root i).pull j).ι → Gs.functionFieldˣ),
      GlobalTheory.PairCov.CovCommon O R c q jB πB G π ρ j πG φ jG ∧
      ∀ σ i, GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ (h σ).isVB jB πB (t σ) π ρ ((fl σ).pull ρ) j φ jG i (r σ i) := by
  first | exact @GlobalTheory.PairCovGen.exists_genericFibre | exact GlobalTheory.PairCovGen.exists_genericFibre | (intros; apply GlobalTheory.PairCovGen.exists_genericFibre <;> assumption)
