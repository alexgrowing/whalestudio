import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RieszHermitianHolds
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummandLocalization

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.LocalSpans

theorem summand_localization : SummandLoc :=
  _root_.UpperTheory.Reformulated.B.SummandLocalization.summand_localization

end Formalism.L2.SG.Pf.G6
