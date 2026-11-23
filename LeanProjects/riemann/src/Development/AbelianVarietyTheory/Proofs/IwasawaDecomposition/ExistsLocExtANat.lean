import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem exists_loc_extA_nat :
    ∀ (D : D7) (N j p : ℕ), ∃ L : ModuliIntegralCharts.Loc D N j p, Nonempty (ModuliIntegralCharts.ExtA D L) :=
  fun D N j p =>
    ⟨Formalism.MainNotions.DIV.Inh.LocalProvisionModel.locM D N j p (Formalism.MainNotions.DIV.Inh.LocalProvisionModel.mpTrivialAb D p (Formalism.MainNotions.DIV.Inh.nonempty_coefficient_field p).some),
      ⟨Formalism.MainNotions.DIV.Inh.LocalProvisionModel.extM D N j p (Formalism.MainNotions.DIV.Inh.LocalProvisionModel.mpTrivialAb D p (Formalism.MainNotions.DIV.Inh.nonempty_coefficient_field p).some)⟩⟩

end GlobalTheory.LocM
