import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bridge
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.BrExistsSqInv
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.LeadingConstantNeZero
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.LatITopBasis
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.IdealBasis
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.UniqInvHolds
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFixJ
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ConjugateSets.Record

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (jL)

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ComplexMultiplicationLFunction

open Formalism.BasicNotions (D7)

theorem cmConjSetF_proved [h : Fact CMConjSetF] : CMConjSetF := h.out

theorem cmConjSet_holds [h : Fact CMConjSetF] (D : D7) : CMConjSet D := conjSet_of_F h.out D

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ComplexMultiplicationLFunction

end
