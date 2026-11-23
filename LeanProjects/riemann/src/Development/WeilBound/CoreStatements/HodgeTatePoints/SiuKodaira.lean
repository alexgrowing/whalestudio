import Development.WeilBound.CoreStatements.HodgeTatePoints.SiuaKodOf
import Development.WeilBound.CoreStatements.HodgeTatePoints.SiuSegre

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace PositivityTheory.HtPt.Siua

theorem siu_kodaira : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement →
    GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaGeneric.Statement :=
  siu_kodaira_of PositivityTheory.HtPt.Siub.siu_segre

end PositivityTheory.HtPt.Siua
