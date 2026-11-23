import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalD
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementE

noncomputable section

namespace Formalism.L2.Th1.B.BeE

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst)

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem cob_sub {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f g : PowerSeries K) : cob F (f - g) = cob F f - cob F g := by
  have h0 := PowerSeries.HasSubst.of_constantCoeff_zero hF
  simp only [cob, at1, PowerSeries.subst_sub h0, PowerSeries.subst_sub (PowerSeries.HasSubst.X (0 : Fin 2)),
    PowerSeries.subst_sub (PowerSeries.HasSubst.X (1 : Fin 2))]
  ring

theorem cob_add {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f g : PowerSeries K) : cob F (f + g) = cob F f + cob F g := by
  have h0 := PowerSeries.HasSubst.of_constantCoeff_zero hF
  simp only [cob, at1, PowerSeries.subst_add h0, PowerSeries.subst_add (PowerSeries.HasSubst.X (0 : Fin 2)),
    PowerSeries.subst_add (PowerSeries.HasSubst.X (1 : Fin 2))]
  ring

theorem cob_zero {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0) :
    cob F (0 : PowerSeries K) = 0 := by
  simpa using cob_sub hF (0 : PowerSeries K) 0

theorem cob_neg {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) : cob F (-f) = -cob F f := by
  have h := cob_sub hF (0 : PowerSeries K) f
  rwa [zero_sub, cob_zero hF, zero_sub] at h

theorem psubst_fLog {ι : Type} {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0)
    {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.subst U (fLog g) = fLog (PowerSeries.subst U g) := by
  have hg1 : PowerSeries.constantCoeff (g - 1) = 0 := by simp [hg]
  have hU' := PowerSeries.HasSubst.of_constantCoeff_zero hU
  unfold fLog
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hg1) hU',
    PowerSeries.subst_sub hU']
  congr 2
  rw [← map_one (PowerSeries.C (R := K)), PowerSeries.subst_C, map_one]

theorem cc_psubst {ι : Type} {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0)
    {g : PowerSeries K} {c : K} (hg : PowerSeries.constantCoeff g = c) :
    MvPowerSeries.constantCoeff (PowerSeries.subst U g) = c := by
  have hU' := PowerSeries.HasSubst.of_constantCoeff_zero hU
  have hgc : PowerSeries.constantCoeff (g - PowerSeries.C c) = 0 := by simp [hg]
  have e : g = PowerSeries.C c + (g - PowerSeries.C c) := by ring
  rw [e, PowerSeries.subst_add hU', PowerSeries.subst_C, map_add,
    PowerSeries.constantCoeff_subst_eq_zero hU _ hgc]
  simp

theorem cob_fLog {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 1) :
    cob F (fLog g) = fLog (PowerSeries.subst F g) - fLog (at1 0 g) - fLog (at1 1 g) := by
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  simp only [cob, at1]
  rw [psubst_fLog hF hg, psubst_fLog (hX 0) hg, psubst_fLog (hX 1) hg]

theorem two_ne {ι : Type} : (2 : MvPowerSeries ι K) ≠ 0 := by
  intro h
  have h2 := congrArg MvPowerSeries.constantCoeff h
  have e2 : MvPowerSeries.constantCoeff (2 : MvPowerSeries ι K) = 2 := map_ofNat _ 2
  rw [e2, map_zero] at h2
  exact two_ne_zero h2

end Alg

theorem BeESim_of (hG : GCob) (hL : LDiv) : BeESim := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 xT yT P l i ep F hP hF hi hC hC3 hT
  obtain ⟨nu, hnuI, hnu0, hLT⟩ := hL K g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hi hC hC3 hT
  obtain ⟨hy, hcub, hx, -, -, hk⟩ := hT
  have hGC := hG K g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hC hC3 hy hcub
  have hF0 := hF.1
  have hce : c0 - (xT + c0) = -xT := by ring
  have hn : ‖c0 - (xT + c0)‖ ≤ 1 := by rw [hce, norm_neg]; exact hx
  have hg : ep + PowerSeries.C (c0 - (xT + c0)) * PowerSeries.X ^ 2 = gT ep xT := by
    rw [hce, map_neg, gT]; ring
  have hD := (diffPh K g2 g3 s2 c0 (xT + c0) P l i ep F hP hcub hF hC).1
  obtain ⟨hw, hwI⟩ := wIntegral K c0 (xT + c0) P l i ep F hF hC hn
  rw [hg] at hD hw
  have hg0 : PowerSeries.constantCoeff (gT ep xT) = 1 := by
    rw [gT, map_sub, hC.2.1]; simp
  have hw0 : PowerSeries.constantCoeff (PowerSeries.subst l (wOf (xT + c0) P)) = 0 := by
    have := congrArg PowerSeries.constantCoeff hw
    rw [map_mul, hg0, mul_one] at this
    rw [this]; simp
  generalize PowerSeries.subst l (wOf (xT + c0) P) = wl at hGC hwI hw0
  generalize phE s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l = ph' at hD ⊢
  generalize 3 * (xT + c0) ^ 2 - g2 / 4 = kap at hGC hk
  generalize phO s2 P l = ph at hD ⊢
  generalize gT ep xT = g at hGC hD hg0
  obtain ⟨d, hd⟩ : ∃ d : MvPowerSeries (Fin 2) K,
      d = 1 - MvPowerSeries.C kap * at1 0 wl * at1 1 wl := ⟨_, rfl⟩
  rw [← hd, hLT] at hGC
  have hdI : Integral d := by
    rw [hd]
    exact ParE.integral_sub' Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_one'
      (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (ParE.integral_C' hk)
        (integral_series_at_variable 0 wl hwI)) (integral_series_at_variable 1 wl hwI))
  have hd0 : MvPowerSeries.constantCoeff d = 1 := by
    rw [hd, map_sub, map_mul, map_mul, constantCoeff_series_at_variable 0 wl hw0]; simp
  have hFne : F ≠ 0 := by
    intro h
    have := law_coeff_single hF 0
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hmain : PowerSeries.subst F g * (nu * nu) = at1 0 g * at1 1 g * (d * d) := by
    refine mul_right_cancel₀ (pow_ne_zero 2 hFne) ?_
    linear_combination hGC
  have cF := cc_psubst hF0 hg0
  have cA : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) g) = 1 := cc_psubst (by simp) hg0
  have cB : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) g) = 1 := cc_psubst (by simp) hg0
  have hlog := congrArg fLog hmain
  rw [ParO.fLog_mul cF (by rw [map_mul, hnu0, mul_one]), ParO.fLog_mul hnu0 hnu0,
    ParO.fLog_mul (by rw [map_mul, cA, cB, mul_one]) (by rw [map_mul, hd0, mul_one]),
    ParO.fLog_mul cA cB, ParO.fLog_mul hd0 hd0] at hlog
  have h2 : cob F (2 * (ph' - ph)) = 2 * (cob F ph' - cob F ph) := by
    rw [two_mul, cob_add hF0, cob_sub hF0]; ring
  have h3 := congrArg (cob F) hD
  rw [h2, cob_neg hF0, cob_fLog hF0 hg0] at h3
  have e : cob F ph' - cob F ph = fLog nu - fLog d := by
    refine mul_left_cancel₀ (two_ne (K := K)) ?_
    linear_combination h3 - hlog
  have s := (simeqInt K (Fin 2) _ _ _ _ (simeqLog K (Fin 2) nu hnu0 hnuI).1
    (simeqLog K (Fin 2) d hd0 hdI).1).1
  unfold Simeq at s ⊢
  rw [e]
  simpa using s

theorem cocycle_diff_exp_equiv : CocycleDiffExpEquiv := by
  intro K _ _ _ F H H' hF0 hFi hHH'
  obtain ⟨-, -, -, -, hsub⟩ := equivalence_rules K (Fin 2)
  obtain ⟨hrefl, hsymm, -, hadd, -⟩ := equivalence_rules K (Fin 3)
  have hneg : ∀ a b : MvPowerSeries (Fin 3) K, Simeq a b → Simeq (-a) (-b) := by
    intro a b h
    have h' := hadd b a (-a - b) (-a - b) (hsymm a b h) (hrefl _)
    have e1 : b + (-a - b) = -a := by ring
    have e2 : a + (-a - b) = -b := by ring
    rwa [e1, e2] at h'
  have hsub' : ∀ a b c d : MvPowerSeries (Fin 3) K, Simeq a b → Simeq c d → Simeq (a - c) (b - d) := by
    intro a b c d h1 h2
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact hadd _ _ _ _ h1 (hneg _ _ h2)
  have hX : ∀ j : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) = 0 :=
    fun j => MvPowerSeries.constantCoeff_X j
  have iX : ∀ j : Fin 3, Integral (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) :=
    fun j => integral_mvPowerSeries_X j
  have c3 : MvPowerSeries.constantCoeff (in3 F) = 0 := Formalism.L2.Th1.B.E2.constantCoeff_law_first_two_of_three hF0
  have i3 : Integral (in3 F) := integral_subst_two_variables hFi _ _ (hX 0) (hX 1) (iX 0) (iX 1)
  unfold d1
  refine hsub' _ _ _ _ (hsub' _ _ _ _ ?_ ?_) ?_
  · refine hsub (Fin 3) H H' _ ?_ ?_ hHH' <;> intro j <;> fin_cases j <;> simp [c3, i3, hX, iX]
  · refine hsub (Fin 3) H H' _ ?_ ?_ hHH' <;> intro j <;> fin_cases j <;> simp [hX, iX]
  · refine hsub (Fin 3) H H' _ ?_ ?_ hHH' <;> intro j <;> fin_cases j <;> simp [hX, iX]

theorem CubeE_of (hB : BeESim) (hD : CocycleDiffExpEquiv) : CubeE := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 xT yT P l i ep F hW hLaw hI hC hC3 hT
  intro ph'
  have hl0 : PowerSeries.constantCoeff l = 0 := hLaw.2.2.1
  have hcc : PowerSeries.constantCoeff ph' = 0 :=
    (phEDef K s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l hl0).1
  obtain ⟨hdiv, hsw⟩ := cobRules K F l ph' hLaw hcc
  have hO := (first_level_all_formal_groups K g2 g3 s2 c0 a1 a3 P l i ep F hW hLaw hI hC hC3).2.2.1
  have hBE := hB K g2 g3 s2 c0 a1 a3 xT yT P l i ep F hW hLaw hI hC hC3 hT
  have hDD := hD K F _ _ hLaw.1 hLaw.2.1 hBE
  obtain ⟨-, -, htrans, -, -⟩ := equivalence_rules K (Fin 3)
  have h3 : Simeq (d1 F (cob F ph')) 0 := htrans _ _ _ hDD hO
  exact ⟨hdiv, hsw, h3, by rw [hsw]; exact h3⟩

end Formalism.L2.Th1.B.BeE
