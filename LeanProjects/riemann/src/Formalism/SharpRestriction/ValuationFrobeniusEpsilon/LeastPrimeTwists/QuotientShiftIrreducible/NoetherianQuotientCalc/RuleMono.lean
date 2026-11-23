import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RulePos

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

open E4 in

theorem ruleMono : RuleMono := by
  intro k X ts F' F F'' hv hF' hF hF'' S hA
  have hle : F.Ann ≤ F'.Ann := by
    intro a ha
    refine Module.mem_annihilator.mpr fun x => S.inj ?_
    rw [map_smul, map_zero]
    exact Module.mem_annihilator.mp ha _
  have h1 := Pos.e1 k X ts F' F F'' hv hF' hF hF'' S hA
  have h2 := rulePos k X ts F' hv hF' (admissible_mono_ideal X.𝒜 hle hA)
  filter_upwards [h1, h2] with m a b
  rw [a]
  linarith

end Formalism.MainNotions.V.Pf.V2.Calc
