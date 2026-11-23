import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityDegreeZero
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleGr
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleFin
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleIrr
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleIso
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleShift
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleNzd
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityExactSequence
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleDev
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.VanishingBelowDimensionRule

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

theorem Pos.e1 : EulerAdditivityExactSequence := euler_additivity_of_rules ruleGr ruleFin ruleIso

theorem Pos.dev : RuleDev := ruleDev ruleGr

open E4 in

theorem rulePos : RulePos := by
  intro k X ts
  induction ts with
  | nil =>
    intro F _ _ _
    exact Eventually.of_forall fun m => Int.natCast_nonneg _
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F hv hF hA
    refine dev_reduce ruleGr ruleIrr ruleIso ruleShift Pos.e1 Pos.dev (P := fun a => 0 ≤ a) le_rfl
      (fun a b ha hb => add_nonneg ha hb) X _ F hv hF hA fun 𝔮 hq hle => ?_
    obtain ⟨σ, hσ, hn, hAσ, hev⟩ :=
      prime_step ruleGr ruleIso ruleNzd Pos.e1 X 𝔮 hq d s ts hv (admissible_mono_ideal X.𝒜 hle hA)
    have g0 : ((GMod.self X.𝒜).quo 𝔮).IsGr X.𝒜 :=
      ((ruleGr k X _ (self_isGr X.𝒜)).1 𝔮 (isHomSub_of_hom X.𝒜 hq.hom)).2
    have hle' : 𝔮 ⊔ Ideal.span {σ} ≤ (((GMod.self X.𝒜).quo 𝔮).quot σ).Ann :=
      (sup_le_sup_right (le_ann_quo X.𝒜 𝔮) _).trans (ann_sup_le_quot _ σ)
    have := ih (((GMod.self X.𝒜).quo 𝔮).quot σ) (fun p hp => hv p (List.mem_cons_of_mem _ hp))
      ((ruleGr k X _ g0).2.2 d σ hσ).1 (admissible_mono_ideal X.𝒜 hle' hAσ)
    filter_upwards [hev, this] with m a b
    rw [a]
    exact b

end Formalism.MainNotions.V.Pf.V2.Calc
