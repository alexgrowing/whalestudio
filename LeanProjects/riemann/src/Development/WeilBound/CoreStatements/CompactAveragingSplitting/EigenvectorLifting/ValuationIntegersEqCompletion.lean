import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitFin

noncomputable section

namespace PositivityTheory.ThK.SplitAsm

open NumberField IsDedekindDomain ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem valuation_integers_eq_completion : IntEq := by
  intro F _ _ v x
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h := (ValuativeRel.isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one (x := x)
  exact h

end PositivityTheory.ThK.SplitAsm
