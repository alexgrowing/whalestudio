import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityDegreeZero
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleGr
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleFin
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleIso
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleShift
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityExactSequence
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityInSection

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

open E7 in

theorem euler_char_product_eventually_add (hE1 : EulerAdditivityExactSequence) (hGr : RuleGr) {k : ℕ} (X : HidaSetting k)
    (ts : List (Deg k × X.R)) (F : X.Mod) (d d' : Deg k) (s s' : X.R)
    (hV : Valid X.𝒜 ((d, s) :: (d', s') :: ts)) (hF : F.IsGr X.𝒜)
    (hA : admitted X.𝒜 ((d + d', s * s') :: ts) F.Ann) :
    ∀ᶠ m in atTop, chi ((d + d', s * s') :: ts) F m =
      chi ((d, s) :: ts) F m + chi ((d', s') :: ts) (F.shift d) m := by
  have hs : 0 ≤ d ∧ s ∈ X.𝒜 d := hV (d, s) List.mem_cons_self
  have hs' : 0 ≤ d' ∧ s' ∈ X.𝒜 d' := hV (d', s') (List.mem_cons_of_mem _ List.mem_cons_self)
  have hVt : Valid X.𝒜 ts :=
    fun p hp => hV p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
  have hss : s * s' ∈ X.𝒜 (d + d') := SetLike.mul_mem_graded hs.2 hs'.2
  have hFd := (hGr k X F hF).2.1 d
  have hP14 := (hGr k X _ hFd).2.2 d' s' hs'.2
  have hP25 := (hGr k X F hF).2.2 (d + d') (s * s') hss
  have hP36 := (hGr k X F hF).2.2 d s hs.2
  have g2 := product_kernel_to_kernel_isGraded X.𝒜 F s s' d d' hF hs'.2
  have g3 := kernel_to_shift_quotient_isGraded F s s' d
  have g4 := quotient_to_product_quotient_isGraded X.𝒜 F s s' d hF hs.2
  have hI2 := ((hGr k X _ hP36.2).1 _ (g2.range_hom hP25.2.internal)).1
  have hI3 := ((hGr k X _ hP14.1).1 _ (g3.range_hom hP36.2.internal)).1
  have hI4 := ((hGr k X _ hP25.1).1 _ (g4.range_hom hP14.1.internal)).1
  have a2 : admitted X.𝒜 ts (F.ann (s * s') (d + d')).Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_sub F _) (mul_mem_annihilator_product_kernel F s s' d d')
  have a3 : admitted X.𝒜 ts (F.ann s d).Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_sub F _) (mul_mem_annihilator_kernel F s s' d)
  have a4 : admitted X.𝒜 ts ((F.shift d).quot s').Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_quo (F.shift d) _) (mul_mem_annihilator_shift_quotient F s s' d)
  have a5 : admitted X.𝒜 ts (F.quot (s * s')).Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_quo F _) (mul_mem_annihilator_product_quotient F s s')
  have e2 := hE1 k X ts _ _ _ hVt hP14.2 hP25.2 hI2
    (sesOfExact (phi1 F s s' d d') (phi2 F s s' d d') (kernel_inclusion_product_injective F s s' d d')
      (kernel_inclusion_product_exact F s s' d d') (kernel_inclusion_grading_comap F s s' d d') g2 hP25.2.internal hP36.2.internal) a2
  have e3 := hE1 k X ts _ _ _ hVt hI2 hP36.2 hI3
    (sesOfKer _ (phi3 F s s' d) (ker3 F s s' d d') g3 hP36.2.internal hP14.1.internal) a3
  have e4 := hE1 k X ts _ _ _ hVt hI3 hP14.1 hI4
    (sesOfKer _ (phi4 F s s' d) (ker4 F s s' d) g4 hP14.1.internal hP25.1.internal) a4
  have e5 := hE1 k X ts _ _ _ hVt hI4 hP25.1 hP36.1 (ses5 F s s' d) a5
  filter_upwards [e2, e3, e4, e5] with m h2 h3 h4 h5
  show chi ts (F.quot (s * s')) m - chi ts (F.ann (s * s') (d + d')) m =
    (chi ts (F.quot s) m - chi ts (F.ann s d) m) +
      (chi ts ((F.shift d).quot s') m - chi ts ((F.shift d).ann s' d') m)
  linarith

theorem euler_rule_product_zero : EulerAdditivityDegreeZero := by
  intro k X ts F d s s' hV hF hA
  have hA' : admitted X.𝒜 ((0 + d, s * s') :: ts) F.Ann := by rwa [zero_add]
  have h := euler_char_product_eventually_add (euler_additivity_of_rules ruleGr ruleFin ruleIso) ruleGr X ts F 0 d s s' hV hF hA'
  rw [zero_add] at h
  filter_upwards [h] with m hm
  rw [hm, chi_shift, sub_zero]

end Formalism.MainNotions.V.Pf.V2.Calc
