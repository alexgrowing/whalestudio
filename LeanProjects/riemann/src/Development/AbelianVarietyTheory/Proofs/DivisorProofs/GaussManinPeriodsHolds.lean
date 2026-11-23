import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfSpanAndTaylorClauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSpanTopAndFinrankFromCechPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallinePeriodEqCechDeRhamPeriod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PTaylor0

open GlobalTheory.AnPer

namespace GlobalTheory.PeriodFamily

theorem gaussManinPeriods_holds : GlobalTheory.Published.GaussManinPeriods := by
  refine gaussManinPeriods_of_span_taylor ?_ GlobalTheory.AnPer.TaylorClause.pTaylor0
  intro A _ g hA _ L u P hP
  refine GlobalTheory.CechPer.span_periods_eq_top_and_finrank A g L u hA P fun c => ?_
  exact GlobalTheory.PerLink.main A g L u c.1
    { toFun := fun l => P l c, map_zero' := by simp, map_add' := fun x y => by simp }
    _ (fun _ => rfl) (hP c)

end GlobalTheory.PeriodFamily
