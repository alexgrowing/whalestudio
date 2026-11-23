import Mathlib
import Formalism.LocalRingCardinality.DataParams
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlace
import Development.AbelianVarietyTheory.BlockTheory.GoodPlaces.ShortAtLevelPrime
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.OwnPrimeIntegralOfBqd

noncomputable section

namespace GlobalTheory.ShortOwnCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.ShortPlaceDegreesAtLevelPrime ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {D : D7}

theorem level_ne_q (D : D7) (i : Fin 2) : D.host.g i ≠ D.host.q := by
  intro e
  have hc := D.ntypes.g_cond i
  have hq := D.host.hyp.1
  have h1 : D.host.g i % D.host.q = 1 % D.host.q := by
    rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
      ⟨D.host.QS * D.host.d, by ring⟩), hc]
  rw [e, Nat.mod_self, Nat.mod_eq_of_lt hq.one_lt] at h1
  exact zero_ne_one h1

end GlobalTheory.ShortOwnCompare
