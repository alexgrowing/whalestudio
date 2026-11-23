import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltMore
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PGradedCech
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVanishingCechResidue
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrLenRestrict
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictQuotX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PInterNumRestrict

namespace PositivityTheory.HtPt.Ktw

theorem a1 :
    GroundTheory.Heights₂.Heights.Kleiman.SerreVanish.Statement.{0, 0} :=
  (GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.SerreVanish.equiv
    GroundTheory.Heights₂.Heights.Swarm.GradedCech.proof).mpr
    GroundTheory.Heights₂.Heights.KeyFormula.serreVanishing_graded_holds

theorem a2 :
    GroundTheory.Heights₂.Heights.Kleiman.TildeVanish.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.TildeVanish.proof a1

theorem a3 :
    GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed.proof
    GroundTheory.Heights₂.Heights.Kleiman.Extension.proof
    GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily.proof a2

theorem a4 :
    GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict.proof a3
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof

theorem a5 :
    GroundTheory.Heights₂.Heights.Kleiman.InterNumRestrict.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.InterNumRestrict.proof a4

end PositivityTheory.HtPt.Ktw
