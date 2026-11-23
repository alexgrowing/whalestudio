import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LineOfLargeDegreeOfMoriwaki
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GivenOfAllInputs
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodTowerVolumeTheoremAlt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeepStROfVolume
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Statements.GeometryStatements.GlobalModelExists
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoTheta
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NormSSqFrameOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrasadVolumeSU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import Development.WeilBound.CoreStatements.ArcCellEmbeddings.TraceVolumeDimensionStandard
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PrincipalDatumFgPerfectTracePairingStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIntegralLevelMulKappa
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SumExtendByZeroLeSum
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogCardCompUnfLe
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.WeightEqZeroOfOneIsSec
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree Formalism.IndefR.Obj
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem deepStR_of_hodgeTate : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → HT.FarguesHodgeTate → Flat.GagaSections → GR.QuotientByFiniteFlatStatement → GR.ZarhinStatement → Pub.NefRR → Plug.DeepStR := by
  intro hAIS hMHS hMB hResK hSA hFHT hGaga hQ hZ hNef
  have hLLD := GlobalTheory.CompanionTheory.Ar.Giv.lineOfLargeDegree_of_moriwaki hAIS hMHS hMB hResK
  have hG : Top.Given := GlobalTheory.CompanionTheory.Ar.Link.given_of_moriwaki hAIS hMHS hMB hResK hSA hFHT hGaga hLLD
  have hTC := GlobalTheory.CompanionTheory.Ar.Link.good_tower_and_volume_final hAIS hMHS hMB hResK hSA hFHT hGaga hLLD hQ hZ
  have hHS : Prov.HS := by
    unfold Top.Given at hG
    exact hG.2.2.2.2.2.2.2.2.2.2.1
  have hG6 : ReciprocityTheory.ChartRestriction.G.Geo.BirationalPullbackPushforwardFormula := by
    unfold Prov.HS at hHS
    exact hHS.2.2.2.2.1
  exact GlobalTheory.CompanionTheory.Ar.Plug.deepStR_of_volume hNef hG hAIS hG6 hTC.1 hTC.2

end GlobalTheory.CompanionTheory.Ar.Plug
