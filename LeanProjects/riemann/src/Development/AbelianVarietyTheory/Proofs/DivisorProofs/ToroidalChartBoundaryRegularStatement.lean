import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartBoundaryRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_chart_boundary_regular : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (σ : c.F →+* ℂ) (Y : Scheme.{0}) (q : Y ⟶ Sp (𝓞 c.F)) (jm : Y ⟶ Z.X) (hq : jm ≫ Z.s = q) (n : ℕ) (ch : AlgChart q (σ.comp (algebraMap (𝓞 c.F) c.F)) n) (W : (gen Z).Opens) (f : Γ(gen Z, W)), DifferentiableOn ℂ (ev (genStr Z) σ W f ∘ up jm hq σ ∘ ch.e.symm) (ch.e.target ∩ ch.e.symm ⁻¹' (up jm hq σ ⁻¹' ptsIn (genStr Z) σ W)) := by
  first | exact @GlobalTheory.ArchLim.differentiableOn_ev_up | exact GlobalTheory.ArchLim.differentiableOn_ev_up | (intros; apply GlobalTheory.ArchLim.differentiableOn_ev_up <;> assumption)
