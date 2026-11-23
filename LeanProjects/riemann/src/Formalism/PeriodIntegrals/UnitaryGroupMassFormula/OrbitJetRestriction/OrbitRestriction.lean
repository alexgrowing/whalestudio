import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetRestriction.RestrictedJetEquation

noncomputable section

open Classical

namespace PI.OrbJet.OrbW

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries Finsupp PI.OrbJet PI.OrbShared

theorem orbitRestriction : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitRestriction E := by
  intro D E
  unfold PI.OrbJet.OrbitRestriction
  intro p _ h u i R hR ep sg be hbe Th hB r hr
  obtain ⟨U, hU, hEq⟩ := hB
  obtain ⟨-, -, hb⟩ := hbe
  haveI : NeZero (nP D p) := ⟨by have := h.two; omega⟩

  have hcc : ∀ r ∈ R, MvPowerSeries.constantCoeff (be r) = 0 := fun r hr =>
    constant_coeff_zero_of_vanishing_alt p (nP D p) (be r) (hb r hr).2.2.1
  have key := restricted_jet_equation D p R hR ep sg be hcc Th U hEq hr
  unfold PI.OrbJet.OrbitThetaExpansion
  refine ⟨_, ?_, key⟩
  intro m
  exact hU _

end PI.OrbJet.OrbW
