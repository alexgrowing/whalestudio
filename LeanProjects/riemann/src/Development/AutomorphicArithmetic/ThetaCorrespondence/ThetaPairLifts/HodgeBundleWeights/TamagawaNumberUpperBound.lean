import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ExponentialThreeBound.LeExpThree
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ArchimedeanTamagawaUpperBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LevelSubgroupIndexBounded

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace MainStatements.Tam.A
end MainStatements.Tam.A
namespace MainStatements.Tam
theorem tamagawa_number_upper_bound : VolSt → StabSt → NumSt → _root_.MainStatements.Tam.ArchimedeanTamagawaUpperBound := fun hV hS hN hP D Tu C t0 hC i P μ 𝓕 hF L hL =>
  MainStatements.Tam.A.up_core hV hS hN D Tu C t0 hC i P μ 𝓕 hF L hL (_root_.GlobalTheory.T.level_subgroup_index_bounded hP D Tu C t0 hC i P)
end MainStatements.Tam
end
end
