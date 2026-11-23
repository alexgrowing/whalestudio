import Mathlib
import Development.AutomorphicSpectrum.Definitions.JetCones.KTypePosCone
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.TopUniq

open GroundTheory.Automorphic.HarishChandra Finset GlobalTheory.CompanionTheory.DS
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DS

theorem dsUnique : GlobalTheory.CompanionTheory.DS.DSUnique :=
  fun n ε lam H H' _ _ _ _ σ σ' a b c =>
    CompanionTheory.D.LK.discrete_series_unique_of n ε lam H' H σ' σ a c b

end GlobalTheory.CompanionTheory.DS
