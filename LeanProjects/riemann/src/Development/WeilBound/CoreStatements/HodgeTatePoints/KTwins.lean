import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNefF
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfIsSubvarAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfIsSubvar
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem
import Development.WeilBound.CoreStatements.HodgeTatePoints.A28
import Development.WeilBound.CoreStatements.HodgeTatePoints.A53

namespace PositivityTheory.HtPt.Ktw

theorem a64 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.NefProductNonneg.Statement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.NefProductNonneg.unfolding_matrix_of_form a28 (a63 hR)

theorem a73 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.VeryAmpleNefPlusAmple.Statement :=
  (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.VeryAmpleNefPlusAmple.equiv
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BundleOfDeg.full a65 a71
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelDimEq.full).mp (a72 hR)

theorem a77 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.SectionCount.Statement := (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SectionCount.equiv
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.GraphModel.full
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BundleOfDeg.full
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelDim.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BaseRealises.proof a66
    (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.VeryAmpleModel.proof
      PositivityTheory.HtPt.KtwS.SectionsOverLocalization.VeryAmpleEq.full a69) a18).mp
    (GroundTheory.Heights₂.Heights.Kleiman.SectionCount.assembled a39 a43 a48 a51 hR)

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 in
theorem k_twins : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0} → NefProductNonneg.Statement ∧ VeryAmpleNefPlusAmple.Statement ∧ SectionCount.Statement :=
  fun hR => ⟨a64 hR, a73 hR, a77 hR⟩

end PositivityTheory.HtPt.Ktw
