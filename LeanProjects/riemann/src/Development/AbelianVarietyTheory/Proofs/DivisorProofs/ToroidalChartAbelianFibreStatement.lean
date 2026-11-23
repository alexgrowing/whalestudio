import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartAbelianFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialLogGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparableHermitianFormsDetBounds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
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
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.QCoh (pullbackSections)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_chart_abelian_fibre : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {T : Scheme.{0}} (j : T ⟶ Z.X) {q : T ⟶ Sp Oz} {g : ℕ} (ρ : Oz →+* ℂ) (y : CxPts q ρ) (ch : Chart ((Scheme.Modules.pullback j).obj (omega Z.t.G)) g), y ∈ ptsIn q ρ ch.U → ∃ (U : Z.X.Opens) (W : Z.t.G.left.Opens) (hU : U ≤ unitSec Z.t.G ⁻¹ᵁ W), y ∈ ptsIn q ρ (j ⁻¹ᵁ U) ∧ Submodule.span ℂ (Set.range fun f : Γ(Z.t.G.left, W) => ch.crd q ρ (pullbackSections j _ (le_refl (j ⁻¹ᵁ U)) (dUnit Z.t.G hU f)) y) = ⊤ := by
  first | exact @GlobalTheory.UnitDiffSpan.span_crd_dUnit_model | exact GlobalTheory.UnitDiffSpan.span_crd_dUnit_model | (intros; apply GlobalTheory.UnitDiffSpan.span_crd_dUnit_model <;> assumption)
