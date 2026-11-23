import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnLat
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnEndo
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgTorInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormSqrtNegPowPrimeSqSub

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem end_not_dvd (d : ℕ) (hd : d % 4 = 3) (l : ℕ) [Fact l.Prime]
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) : ¬ l ∣ (d + 1) / 4 := by
  intro h
  apply hin
  refine ⟨1, ?_⟩
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have h0 : ((d + 1 : ℕ) : ZMod l) = 0 := by
    rw [← h4, ZMod.natCast_eq_zero_iff]
    exact Dvd.dvd.mul_left h 4
  push_cast at h0
  linear_combination h0

theorem end_unit (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : ¬ l ∣ n) (a : ℂ_[l]) (ha : ‖a‖ ≤ 1)
    (hq : a ^ 2 - a + (n : ℂ_[l]) = 0) : ‖a‖ = 1 := by
  have hnn : ‖(n : ℂ_[l])‖ = 1 := by
    simpa using kq_int_unit l (n : ℤ) (by exact_mod_cast hn)
  have hprod : a * (1 - a) = n := by linear_combination -hq
  have hb : ‖1 - a‖ ≤ 1 := by
    have e : 1 - a = 1 + -a := by ring
    rw [e]
    exact kq_add_le l _ _ 1 (by simp) (by rwa [norm_neg])
  refine le_antisymm ha ?_
  rw [← hnn, ← hprod, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hb

theorem end_card (d : ℕ) (hd : d % 4 = 3) (L : PeriodPair) (hCM : HasCMBy d L) (S : Finset ℂ)
    (h0 : omegaK d ≠ 0) (hS : Formalism.L2.Th1.F.IsKerReps L (omegaK d) S) :
    S.card + 1 = (d + 1) / 4 := by
  have h1 := Formalism.L2.Th1.F.kerRepsCard L (omegaK d) S h0 hCM hS
  have h2 := (Formalism.L2.Th1.F.hasCMByStable d L hCM 0 1).2
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have h4' : (4 : ℝ) * (((d + 1) / 4 : ℕ) : ℝ) = (d : ℝ) + 1 := by exact_mod_cast h4
  have e : ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * omegaK d = omegaK d := by simp
  rw [e] at h2
  have h3 : ((S.card + 1 : ℕ) : ℝ) = (((d + 1) / 4 : ℕ) : ℝ) := by
    push_cast
    rw [h1, h2]
    push_cast
    linarith
  exact_mod_cast h3

theorem end_integral (d : ℕ) (L : PeriodPair) (hd : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    [Fact l.Prime] (hl : 5 ≤ l) (hld : ¬ l ∣ d) (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l))
    (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]) (hg : IsGoodModel l L ι g2 g3) :
    IntegralPS ((uSer g2 g3).subst (C (ι (omegaK d)) * lgS g2 g3)) := by
  obtain ⟨L', hM, hCM'⟩ := good_lattice l L ι g2 g3 hg
  have hCM1 : HasCMBy d L' := hCM' d hCM
  have hl2 : l ≠ 2 := by omega
  have hquadC := omegaK_quad d hd
  have hquad : (ι (omegaK d)) ^ 2 - ι (omegaK d) + (((d + 1) / 4 : ℕ) : ℂ_[l]) = 0 := by
    have := congrArg ι hquadC
    simpa using this
  have hln := end_not_dvd d hd l hin
  have hn0 : 0 < (d + 1) / 4 := by omega
  obtain ⟨ha1, -, -⟩ := kur_quad l d hd hl2 hld hin _ hquad
  have hau : ‖ι (omegaK d)‖ = 1 := end_unit l _ hln _ ha1 hquad
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := kq_int_unit l 2 (by
      intro h
      have h' : l ∣ 2 := by exact_mod_cast h
      exact hl2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h'))
    simpa using this
  have hα : omegaK d ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hau
    exact zero_ne_one hau
  obtain ⟨S, hS⟩ := Formalism.L2.Th1.F.kerRepsExist L' (omegaK d) hα hCM1
  have hcard := end_card d hd L' hCM1 S hα hS
  obtain ⟨neg, hE⟩ := endo_curve l L' ι (omegaK d) S hα hCM1 hS
  rw [← hM.eq2, ← hM.eq3] at hE
  have htor : ∀ P : S, ‖ι (L'.weierstrassP (P : ℂ))‖ ≤ 1 ∧ ‖ι (L'.derivWeierstrassP (P : ℂ))‖ ≤ 1 := by
    intro P
    obtain ⟨hP1, hP2⟩ := hS.1 P P.2
    refine tor_integral l hl2 L' ι g2 g3 hM _ hn0 hln P ?_ hP2
    have e : (((d + 1) / 4 : ℕ) : ℂ) * (P : ℂ) = omegaK d * (P : ℂ) - omegaK d * (omegaK d * (P : ℂ)) := by
      linear_combination (P : ℂ) * hquadC
    rw [e]
    exact sub_mem hP1 (hCM1 _ hP1)
  have hc : Formalism.L2.Th1.C.CoeffIn (unitBall ℂ_[l]) (Formalism.L2.Th1.A.shortW g2 g3) :=
    shortW_intModel g2 g3 hM.n2 hM.n3 h2
  have h2R : (2 : ℂ_[l])⁻¹ ∈ unitBall ℂ_[l] := Formalism.L2.Th1.C.inv_mem_unitBall h2
  obtain ⟨hlp, hwp, hAx, -, -⟩ := Formalism.L2.Th1.C.curveFrame ℂ_[l] (unitBall ℂ_[l]) _ hc
  have hDat := Formalism.L2.Th1.C.curveEndoR ℂ_[l] (unitBall ℂ_[l]) _ hc S neg _ _ (ι (omegaK d))
    (1 - ι (omegaK d)) hE (fun P => (htor P).1)
    (fun P => by
      change ‖ι (L'.derivWeierstrassP (P : ℂ)) / 2‖ ≤ 1
      rw [norm_div, h2, div_one]
      exact (htor P).2)
    (by
      rw [Fintype.card_coe]
      have : ((S.card : ℂ_[l]) + 1) = (((d + 1) / 4 : ℕ) : ℂ_[l]) := by exact_mod_cast hcard
      rw [this]
      linear_combination -hquad)
    hau.le (Formalism.L2.Th1.C.inv_mem_unitBall hau)
    (by
      have : (Formalism.L2.Th1.A.shortW g2 g3).b₂ = 0 := by
        simp [Formalism.L2.Th1.A.shortW, WeierstrassCurve.b₂]
      rw [this]
      simp)
  have hEnd := Formalism.L2.Th1.C.endIntFromDatum ℂ_[l] (unitBall ℂ_[l]) _ _ _ _ _ S neg _ _ _ _ _
    hlp hwp hAx h2R hDat
  rw [lgS_eq_logSer, Formalism.L2.Th1.A.uSerEq]
  exact hEnd

end ReciprocityTheory.ChartRestriction.L1
