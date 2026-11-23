import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetSubPf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBMapPf
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeExists
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralFramesTransportToFramedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem chartTransport_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], ChartTransportSt Xo c := by
  intro E _ _ _ H Dw l Xo c _
  have hJ : ChartJetTrSt Xo c := chartJetTr_of Xo c (chartJetTan_holds Xo c)
    (chartJetBasis_holds Xo c (fun S _ _ y w hw =>
      FrameTangent.frame_tangent_basis E H Dw l Xo c S y w hw))
  have hF : ChartFrameTrSt Xo c := GlobalTheory.T.integral_frames_transport_to_framed_point E H Dw l Xo c
  have hM : FBMapSt := fbMap_holds
  intro hstar T io y I d B tgT uvecT xT eT wPT hbas hch hdir hfr hpr htr hrig
  obtain ⟨B', hF1, hA1, hp1, hp2, hsy, had⟩ := hM T.V T.Fr (algebraMap T.V T.Fr) d (𝓞 E) B
  obtain ⟨x, x', hchx, hj2, hj1⟩ := hJ T io y I d B.G.F B.A.act tgT uvecT xT hbas hch hdir
  obtain ⟨e, wP, hfrx, hprx, hrx, hfe, hwp⟩ :=
    hF hstar T io y I d B B' tgT xT eT wPT hF1 hA1 hp1 hp2 hsy had hch hfr hpr htr hrig x x' hj2 hj1
  obtain ⟨h, hh⟩ := canonGauge_exists T.Fr d (𝓞 E) T.Fr B'
  letI := io.toAlgebra
  have hchx' : IsChart y.1 d B'.G.F B'.A.act (fun ℓ i => algebraMap T.V T.Fr (uvecT ℓ i)) x := by
    have eF : B'.G.F = fun j => MvPowerSeries.map (algebraMap T.V T.Fr) (B.G.F j) := funext hF1
    have eA : B'.A.act = fun a j => MvPowerSeries.map (algebraMap T.V T.Fr) (B.A.act a j) :=
      funext fun a => funext (hA1 a)
    rw [eF, eA]
    exact hchx
  exact ⟨B', fun ℓ i => algebraMap T.V T.Fr (uvecT ℓ i), x, e, wP, h, hchx', hfrx, hprx, hh, hrx,
    ⟨hF1, hA1, hp1, hp2, hsy, had, fun ℓ i => rfl⟩, x', hj2, hj1, hfe, hwp⟩

end GlobalTheory
