import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.LeadingConstantNeZero
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bridge
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ConjugateSets.ConjKQ

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (jL)

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ComplexMultiplicationLFunction

open Formalism.BasicNotions (D7)

theorem conjSet_of_F (hF : CMConjSetF) (D : D7) : CMConjSet D :=
  hF D.host.K D.host.d (discriminant_mod_four D) _ (br_sqrt_sq D) (br_finrank_K D) (brPhi D)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ComplexMultiplicationLFunction

end
