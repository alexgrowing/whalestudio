import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp

noncomputable section

namespace GlobalTheory.ShortModelTheta

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC wToC LTIso epOf)
open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.L2.KerInert.BeCob (eLT vLT ThetaTie ShortIso)
open GlobalTheory.CurveDictionary (cc_lgF' lgF_eq_logF)

section IntPS

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem integral_ps' {K : Type} [NormedField K] {f : PowerSeries K}
    (h : ∀ k, ‖PowerSeries.coeff k f‖ ≤ 1) : Integral (f : MvPowerSeries Unit K) := by
  intro n
  have e : n = Finsupp.single () (n ()) := Finsupp.ext fun u => by rcases u with ⟨⟩; simp
  rw [e]
  exact h (n ())

theorem ips' {f : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K)) (k : ℕ) :
    ‖PowerSeries.coeff k f‖ ≤ 1 := hf _

theorem ips_add' {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f + g : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ips' hf k) (ips' hg k))

theorem ips_sub' {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f - g : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [map_sub, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ips' hf k) (by rw [norm_neg]; exact ips' hg k))

theorem ips_Cmul' {c : K} (hc : ‖c‖ ≤ 1) {f : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K)) :
    Integral ((PowerSeries.C c * f : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [PowerSeries.coeff_C_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (ips' hf k)

theorem ips_X' : Integral ((PowerSeries.X : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [PowerSeries.coeff_X]
  split_ifs <;> simp

theorem ips_mul' {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f * g : PowerSeries K) : MvPowerSeries Unit K) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hf hg

end IntPS

theorem shortIso_holds : ShortIso := by
  intro K _ _ _ h2 h3 W hW
  obtain ⟨hxI, hx1, hA, -⟩ := Formalism.L2.Th1.A.bridgeCurve K W hW
  obtain ⟨hB, -⟩ := Formalism.L2.Th1.A.bridgeCurve3 K W hW
  obtain ⟨hnum, hden⟩ := Formalism.L2.Th1.A.wpNumEq K W
  rw [← Formalism.L2.Th1.A.uSerEq K _ _]
  obtain ⟨hl0, hl1, -, -⟩ := Formalism.L2.Th1.A.logSpec K W
  have hlS : PowerSeries.HasSubst (Formalism.L2.Th1.A.logSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
  have hl_ne : Formalism.L2.Th1.A.logSer W ≠ 0 := by
    intro h; rw [h, map_zero] at hl1; exact zero_ne_one hl1
  set lW := Formalism.L2.Th1.A.logSer W with hlW
  set P := Formalism.L2.Th1.A.wpReg W with hP
  set xs := Formalism.L2.Th1.A.xS W with hxs
  set N : PowerSeries K := xs + PowerSeries.C (W.b₂ / 12) * PowerSeries.X ^ 2 with hN
  set D : PowerSeries K := xs - PowerSeries.C (W.a₁ / 2) * PowerSeries.X * xs -
    PowerSeries.C (W.a₃ / 2) * PowerSeries.X ^ 3 with hD
  have hD1 : PowerSeries.constantCoeff D = 1 := by
    rw [hD]; simp [hx1]
  have hden1 : PowerSeries.constantCoeff (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) ≠ 0 := by
    rw [hden]; simp
  have hsn : PowerSeries.subst lW (Formalism.L2.Th1.CM.wpNum (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      1 + lW ^ 2 * PowerSeries.subst lW P := by
    rw [hnum, PowerSeries.subst_add hlS, PowerSeries.subst_mul hlS, PowerSeries.subst_pow hlS,
      PowerSeries.subst_X hlS, ← PowerSeries.coe_substAlgHom hlS, map_one]
  have hsd : PowerSeries.subst lW (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      1 - PowerSeries.C (1 / 2 : K) * lW ^ 3 * PowerSeries.subst lW (PowerSeries.derivative K P) := by
    rw [hden, PowerSeries.subst_sub hlS, PowerSeries.subst_mul hlS, PowerSeries.subst_mul hlS,
      PowerSeries.subst_pow hlS, PowerSeries.subst_X hlS, PowerSeries.subst_C, ← PowerSeries.coe_substAlgHom hlS,
      map_one]
    rfl
  set I := PowerSeries.subst lW (Formalism.L2.Th1.CM.uSer (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) with hI
  have hIB : I * PowerSeries.subst lW (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      lW * PowerSeries.subst lW (Formalism.L2.Th1.CM.wpNum (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) := by
    rw [hI, ← PowerSeries.subst_mul hlS]
    unfold Formalism.L2.Th1.CM.uSer
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hden1, mul_one, PowerSeries.subst_mul hlS, PowerSeries.subst_X hlS]
  rw [hsn, hsd] at hIB
  have hID : I * D = PowerSeries.X * N := by
    have h3ne : lW ^ 3 ≠ 0 := pow_ne_zero 3 hl_ne
    apply mul_left_cancel₀ h3ne
    have e2 : (2 : K) ≠ 0 := two_ne_zero
    have hB' : PowerSeries.X ^ 3 * (1 - PowerSeries.C (1 / 2 : K) * lW ^ 3 * PowerSeries.subst lW (PowerSeries.derivative K P)) =
        lW ^ 3 * D := by
      have hh : (PowerSeries.C (1 / 2 : K) : PowerSeries K) * (2 : PowerSeries K) = 1 := by
        rw [show (2 : PowerSeries K) = PowerSeries.C (2 : K) from (map_ofNat _ 2).symm, ← map_mul]; norm_num
      rw [hD]
      have ha1 : (PowerSeries.C (W.a₁ / 2) : PowerSeries K) = PowerSeries.C (1 / 2 : K) * PowerSeries.C W.a₁ := by
        rw [← map_mul]; ring_nf
      have ha3 : (PowerSeries.C (W.a₃ / 2) : PowerSeries K) = PowerSeries.C (1 / 2 : K) * PowerSeries.C W.a₃ := by
        rw [← map_mul]; ring_nf
      rw [ha1, ha3]
      linear_combination (-(PowerSeries.C (1 / 2 : K) : PowerSeries K)) * hB -
        (PowerSeries.X ^ 3 - lW ^ 3 * xs) * hh
    linear_combination PowerSeries.X ^ 3 * hIB - I * hB' + lW * PowerSeries.X * hA
  have hDinv : D⁻¹ * D = 1 := PowerSeries.inv_mul_cancel _ (by rw [hD1]; exact one_ne_zero)
  have hIe : I = PowerSeries.X * N * D⁻¹ := by
    calc I = I * D * D⁻¹ := by rw [mul_assoc, mul_comm D, hDinv, mul_one]
      _ = _ := by rw [hID]
  rw [hIe]
  have h12 : ‖(12 : K)‖ = 1 := by
    rw [show (12 : K) = 2 * 2 * 3 by norm_num, norm_mul, norm_mul, h2, h3]; norm_num
  have hi1 : ‖W.a₁‖ ≤ 1 := hW.1
  have hi2 : ‖W.a₂‖ ≤ 1 := hW.2.1
  have hi3 : ‖W.a₃‖ ≤ 1 := hW.2.2.1
  have hb2 : ‖W.b₂ / 12‖ ≤ 1 := by
    rw [norm_div, h12, div_one, WeierstrassCurve.b₂]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hi1
    · rw [norm_mul]
      refine mul_le_one₀ ?_ (norm_nonneg _) hi2
      rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h2]; norm_num
  have ha12 : ‖W.a₁ / 2‖ ≤ 1 := by rw [norm_div, h2, div_one]; exact hi1
  have ha32 : ‖W.a₃ / 2‖ ≤ 1 := by rw [norm_div, h2, div_one]; exact hi3
  have hX2 : Integral (((PowerSeries.X : PowerSeries K) ^ 2 : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [pow_two]; exact ips_mul' ips_X' ips_X'
  have hX3 : Integral (((PowerSeries.X : PowerSeries K) ^ 3 : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [pow_succ]; exact ips_mul' hX2 ips_X'
  have hNI : Integral ((N : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [hN]; exact ips_add' hxI (ips_Cmul' hb2 hX2)
  have hDI : Integral ((D : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [hD]
    exact ips_sub' (ips_sub' hxI (ips_mul' (ips_Cmul' ha12 ips_X') hxI)) (ips_Cmul' ha32 hX3)
  have hDiI : Integral ((D⁻¹ : PowerSeries K) : MvPowerSeries Unit K) :=
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_of_mul_eq_one hDI hD1 hDinv
  exact ips_mul' (ips_mul' ips_X' hNI) hDiI

theorem exists_witt_series_inverse_formalGroup_iso_short {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) :
    ∃ w : PowerSeries (WW l), PowerSeries.map (wToC l) w = vLT hLT := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set th0 := Formalism.L2.G.Pend.thOf hLT with hth0
  have h00 : PowerSeries.constantCoeff th0 = 0 := Formalism.L2.G.Pend.thOf_zero hLT
  have hu : IsUnit (PowerSeries.coeff 1 th0) := Formalism.L2.G.Pend.thOf_unit hLT
  set i0 := th0.substInvOfIsUnit hu with hi0
  have hi00 : PowerSeries.constantCoeff i0 = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hR : PowerSeries.subst i0 th0 = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right _ h00 hu
  set thC := PowerSeries.map (wToC l) th0 with hthC
  set iC := PowerSeries.map (wToC l) i0 with hiC
  have hthC0 : PowerSeries.constantCoeff thC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hthC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h00, map_zero]
  have hiC0 : PowerSeries.constantCoeff iC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hiC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hi00, map_zero]
  have hRC : PowerSeries.subst iC thC = PowerSeries.X := by
    have h := congrArg (MvPowerSeries.map (wToC l)) hR
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hi00)] at h
    exact h.trans (MvPowerSeries.map_X _ _)
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hlog : PowerSeries.subst thC (lgF ℂ_[l] l) = PowerSeries.C e * g.l := by
    have h := Formalism.L2.G.Pend.thOf_log hLT
    rw [lgF_eq_logF] at h
    exact h
  have hVT : PowerSeries.subst thC (vLT hLT) = PowerSeries.X := by
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0),
      PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_C, hlog]
    have e1 : (MvPowerSeries.C e⁻¹ : PowerSeries ℂ_[l]) * (PowerSeries.C e * g.l) = g.l := by
      rw [← mul_assoc]
      show PowerSeries.C e⁻¹ * PowerSeries.C e * g.l = g.l
      rw [← map_mul, inv_mul_cancel₀ hene, map_one, one_mul]
    rw [e1]
    exact Formalism.L2.G.Pend.ex_l g hex hinv
  refine ⟨i0, ?_⟩
  show iC = vLT hLT
  symm
  calc vLT hLT = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[l]) (vLT hLT) := (PowerSeries.X_subst _).symm
    _ = PowerSeries.subst (PowerSeries.subst iC thC) (vLT hLT) := by rw [hRC]
    _ = PowerSeries.subst iC (PowerSeries.subst thC (vLT hLT)) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0) _).symm
    _ = PowerSeries.subst iC (PowerSeries.X : PowerSeries ℂ_[l]) := by rw [hVT]
    _ = iC := PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0)

theorem v_integral' {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) (n : ℕ) :
    ‖PowerSeries.coeff n (vLT hLT)‖ ≤ 1 := by
  obtain ⟨w, hw⟩ := exists_witt_series_inverse_formalGroup_iso_short hOk hLT
  rw [← hw, PowerSeries.coeff_map]
  have := Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)
  simpa using this

theorem norm_nat_one' {l : ℕ} [Fact l.Prime] (h5 : 5 ≤ l) (m : ℕ) (hm1 : 0 < m) (hm : m < 5) :
    ‖(m : ℂ_[l])‖ = 1 := by
  have hp : l.Prime := Fact.out
  refine Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one l) ?_
  intro h
  have := Nat.le_of_dvd hm1 h
  omega

theorem thetaTie_holds : ThetaTie := by
  intro l _ h5 g hLT hOk n
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hvcc : PowerSeries.constantCoeff (vLT hLT) = 0 := PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex
  have hvS : PowerSeries.HasSubst (vLT hLT) := PowerSeries.HasSubst.of_constantCoeff_zero' hvcc
  have hgl : g.l = Formalism.L2.Th1.A.logSer g.W := Formalism.L2.KerInert.Dict.formal_logarithm_agree l g.W g.wq hOk.2.1
  have hlW0 : PowerSeries.constantCoeff (Formalism.L2.Th1.A.logSer g.W) = 0 := by rw [← hgl]; exact Formalism.MainNotions.J.cc_l g
  have hvl : PowerSeries.subst (vLT hLT) (Formalism.L2.Th1.A.logSer g.W) = PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l := by
    rw [← hgl]; exact Formalism.L2.G.Pend.lg_pt g hex hinv hv0
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by exact_mod_cast norm_nat_one' h5 2 (by norm_num) (by norm_num)
  have h3 : ‖(3 : ℂ_[l])‖ = 1 := by exact_mod_cast norm_nat_one' h5 3 (by norm_num) (by norm_num)
  have hiso := shortIso_holds ℂ_[l] h2 h3 g.W (Formalism.L2.KerInert.Dict.intModel_of_ok hOk)
  have hθ : thetaS l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) (eLT hLT)⁻¹ =
      MvPowerSeries.subst (fun _ => vLT hLT) (PowerSeries.subst (Formalism.L2.Th1.A.logSer g.W)
        (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W)))) := by
    unfold thetaS
    rw [Formalism.L2.Th1.A.uSerEq ℂ_[l] _ _, ← PowerSeries.subst_def,
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlW0) hvS, hvl]
  rw [hθ]
  exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun _ => hvcc) (fun _ => integral_ps' (v_integral' hOk hLT)) hiso
    (Finsupp.single () n)

end GlobalTheory.ShortModelTheta
