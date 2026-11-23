import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FromBlocksMapIntCastMemSymplecticGroup

open ReciprocityTheory.ChartRestriction.G.Key

namespace GlobalTheory.ThetaInversion

theorem inversion : Chi.InversionStatement := GlobalTheory.inversionStatement_holds

theorem chi : Chi.ChiStatement := Chi.chi_of inversion Chi.spGen

end GlobalTheory.ThetaInversion
