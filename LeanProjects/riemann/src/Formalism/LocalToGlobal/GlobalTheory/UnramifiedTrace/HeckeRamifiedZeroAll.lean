import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.MulLatticeOne
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiamondSamePlaceMatchings

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

theorem hecke_ramified_zero_all : ∀ (D : D7) (u : D.what₂.Word), HidaSetting D u → RT.ConcreteFormsLevelZero D u → HeckeRamifiedLevelZero D u :=
  Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.hecke_ramified_zero_of_matchings_and_du SameDiaZero.diamond_same_place_matchings dUAll_holds

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
