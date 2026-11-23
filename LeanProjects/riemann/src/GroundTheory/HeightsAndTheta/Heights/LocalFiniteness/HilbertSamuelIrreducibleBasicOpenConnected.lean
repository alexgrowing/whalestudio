import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelGrowthOffHypersurfacePolynomial
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelUnbranchedPartConnected
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PHeightRecR
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDivVertical
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffTube
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeLocalLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocFrac
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PLocalizedQuotientLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFiniteRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.PIrreducibleBasicOpenConnected
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadStep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ZeroLeDivCycle
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalLength.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalLength.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.LocalizedQuotientLength.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalFlat

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFiniteRank.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFiniteRank.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.FibreFinite.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFinite GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocFrac.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpExcessDrop.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpExcessDecreases.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpExcessDecreases.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.ExcessPositive.full GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualCompare GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ExceptionalCompare

theorem GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadStep : GroundTheory.Heights₂.Heights.Model.SpreadStep.Statement :=
  @GroundTheory.Heights₂.Heights.Model.SpreadStep.proof GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadIsoLoc GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadGlue

theorem GroundTheory.Heights₂.Heights.AutoClose.CutOffLimit : GroundTheory.Heights₂.Heights.CutOffLimit.Statement :=
  @GroundTheory.Heights₂.Heights.CutOffLimit.of_open GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SheetImageAreaSet GroundTheory.Heights₂.Heights.AutoClose.TubeEuclMass

theorem GroundTheory.Heights₂.Heights.AutoClose.StokesOnVariety : GroundTheory.Heights₂.Heights.StokesOnVariety.Statement :=
  @GroundTheory.Heights₂.Heights.StokesOnVariety.of_open GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SheetImageAreaSet GroundTheory.Heights₂.Heights.AutoClose.TubeEuclMass
