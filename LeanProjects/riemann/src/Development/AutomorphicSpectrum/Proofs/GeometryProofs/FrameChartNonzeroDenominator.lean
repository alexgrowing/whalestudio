import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntMemModelSmall
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdZpowLe
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AllWeightSectionsCompat
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Definitions.RegularCharts.NotFamConstZero
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.RegularChartNonzeroDenominator
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.frame_chart_nonzero_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (h : GenFrEx Xo c) (C : GlobalTheory.Reg.FChart h), ∃ g₀ : C.R, g₀ ≠ 0 ∧ ∀ (A : Subring (Om C.Z)) (hA : ∀ r : C.R, (r : Om C.Z) ∈ A), (g₀ : Om C.Z)⁻¹ ∈ A → ∀ (L : Type) [Field L] (io : c.F →+* L) (ev : A →+* L), letI := io.toAlgebra; ∀ (ψ : C.R →ₐ[c.F] L), (∀ r : C.R, ψ r = ev ⟨r, hA r⟩) → ∀ (z y : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrBor t z y → FinTr.RegAt h C.Z io A ev y := by
  first | exact @ModelDimension.regular_chart_nonzero_denominator | exact ModelDimension.regular_chart_nonzero_denominator
