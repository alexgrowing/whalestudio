import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelGrowthOffHypersurfacePolynomial
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRC3ResidualContractionComponent
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOnChart
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocalize
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocResidue
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreNonempty
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalResidueLength
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIrreducibleConnected
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Assembly
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDescendHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFreeSheafBasis
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadBundleNbhd
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_FibreNonempty.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.FibreNonempty.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.FibreNonempty.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocalRing

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalResidueLength.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalResidueLength.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalResidueLength.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocResidue.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocLocalize.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadBundle : GroundTheory.Heights₂.Heights.Model.SpreadBundle.Statement :=
  @GroundTheory.Heights₂.Heights.Model.SpreadBundle.of_open GroundTheory.Heights₂.Heights.Model.FreeSheafBasis.proof GroundTheory.Heights₂.Heights.AutoClose.Model_BasisIsoFree GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadStep

theorem GroundTheory.Heights₂.Heights.AutoClose.Model_GlueBundles : GroundTheory.Heights₂.Heights.Model.GlueBundles.Statement :=
  @GroundTheory.Heights₂.Heights.Model.GlueBundles.of_open GroundTheory.Heights₂.Heights.Model.FreeSheafBasis.proof GroundTheory.Heights₂.Heights.AutoClose.Model_BasisIsoFree GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadStep GroundTheory.Heights₂.Heights.Model.DescendHom.proof GroundTheory.Heights₂.Heights.AutoClose.Model_GenericPullInj GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadHomSections

theorem GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadBundleNbhd : GroundTheory.Heights₂.Heights.Model.SpreadBundleNbhd.Statement :=
  @GroundTheory.Heights₂.Heights.Model.SpreadBundleNbhd.proof GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadLocal GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadStep

theorem GroundTheory.Heights₂.Heights.AutoClose.spread_vector_bundle_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.SpreadBundle.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.SpreadBundle.of_open GroundTheory.Heights₂.Heights.Model.FreeSheafBasis.proof GroundTheory.Heights₂.Heights.AutoClose.Model_BasisIsoFree GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadStep

theorem GroundTheory.Heights₂.Heights.AutoClose.StokesOnChart : GroundTheory.Heights₂.Heights.StokesOnChart.Statement :=
  @GroundTheory.Heights₂.Heights.StokesOnChart.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover GroundTheory.Heights₂.Heights.AutoClose.CutOffLimit
