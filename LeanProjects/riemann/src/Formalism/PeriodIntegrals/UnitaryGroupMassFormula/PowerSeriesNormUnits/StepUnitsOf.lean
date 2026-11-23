import Mathlib
import Formalism.PeriodIntegrals.PhNormUnits
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffFormalSMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.TendstoCoeffOfCont
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffVar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.SimeqSubst1

noncomputable section

open Classical

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

theorem stepUnits_of (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense) : StepUnits := by
  intro p _ l ex ph S hS α hα h1 h2
  obtain ⟨hex0, hinv, hp2, h22, hswap, -, -, hint_r, hIA, -, hprod, -, hB, hNorm⟩ := hS
  have hph : PowerSeries.constantCoeff ph = 0 := by
    have h2n : ‖(2 : ℂ_[p])‖ = 1 := norm_two_of hp2
    have h2' := hNorm ((2 : ℂ_[p]), (2 : ℂ_[p])) h22 h2n h2n
    dsimp only at h2'
    exact ph_const_of h2' hex0 hinv
  obtain ⟨n, hn⟩ := hprod α hα
  have hU := hNorm α hα h1 h2
  have hc : α.1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hnorm : ‖PI.PhNormUnits.zc n‖ = 1 := by rw [← hn, norm_mul, h1, h2, one_mul]
  obtain ⟨m, hm⟩ := zc_inv_of n hnorm
  have hinvc : α.1⁻¹ = α.2 * PI.PhNormUnits.zc m := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hn, hm]
  have h1v : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    constantCoeff_var _
  have hd : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex α.2 (PI.PhNormUnits.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
    have h := hint_r _ (hswap α hα)
    rw [Prod.fst_swap] at h
    exact h
  have hw : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex α.1⁻¹ (PI.PhNormUnits.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := by
    rw [hinvc, ← mulBy_mulBy hex0 hinv α.2 (PI.PhNormUnits.zc m) (PI.PhNormUnits.Xv (1 : Fin 2)) h1v]
    exact int_mulBy_of hSub hex0 hinv α.2 hd _
      (constantCoeff_formalSMul hex0 hinv _ _ h1v)
      (int_mulBy_zp hSub hex0 hinv hC hD hIA _ h1v
        (int_X _) m)
  have step1 := units_i hE hSub hex0 hinv hIA α.1 (α.1 * α.2) hU
  have step2 := units_ii hE hSub hC hD hex0 hinv hph hIA hB α.1 α.2 n hn
  exact units_iv hE hSub hex0 hinv α.1 α.2 hc hw (sTrans hE step1 step2)

theorem stepAll_of (hE : CalcEquiv) (hSub : CalcSubst) : StepAll := by
  intro p _ l ex ph S hS hU α hα
  obtain ⟨hex0, hinv, -, -, hswap, -, -, hint_r, hIA, -, -, hdec, hB, -⟩ := hS
  obtain ⟨β, hβ, γ, hγ, hb1, hb2, hg1, hg2, rfl⟩ := hdec α hα
  have h0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    constantCoeff_var _
  have h1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    constantCoeff_var _
  have i0 : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.Xv (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) := int_X _
  have i1 : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.Xv (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) := int_X _
  have hI1 : ∀ δ ∈ S, ∀ x : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff x = 0 →
      PI.PhNormUnits.IntegralMv x → PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex δ.1 x) :=
    fun δ hδ x hx0 hx => int_mulBy_of hSub hex0 hinv δ.1 (hint_r δ hδ) x hx0 hx
  have hI2 : ∀ δ ∈ S, ∀ x : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff x = 0 →
      PI.PhNormUnits.IntegralMv x → PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex δ.2 x) :=
    fun δ hδ x hx0 hx => by
      have h := hint_r _ (hswap δ hδ)
      rw [Prod.fst_swap] at h
      exact int_mulBy_of hSub hex0 hinv δ.2 h x hx0 hx
  have c0 : ∀ (c : ℂ_[p]) (x : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.constantCoeff x = 0 →
      MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c x) = 0 :=
    fun c x hx => constantCoeff_formalSMul hex0 hinv c x hx
  show PI.PhNormUnits.Simeq (PI.PhNormUnits.be l ex ph (PI.PhNormUnits.mulBy l ex (β.1 + γ.1) (PI.PhNormUnits.Xv 0)) (PI.PhNormUnits.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
    (PI.PhNormUnits.be l ex ph (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.mulBy l ex (β.2 + γ.2) (PI.PhNormUnits.Xv 1)))
  rw [← add_mulBy hex0 hinv β.1 γ.1 _ h0,
    ← add_mulBy hex0 hinv β.2 γ.2 _ h1]
  have L := be_add_left hSub hex0 hinv hB (PI.PhNormUnits.mulBy l ex β.1 (PI.PhNormUnits.Xv 0))
    (PI.PhNormUnits.mulBy l ex γ.1 (PI.PhNormUnits.Xv 0)) (PI.PhNormUnits.Xv 1) (c0 _ _ h0) (c0 _ _ h0) h1
    (hI1 β hβ _ h0 i0) (hI1 γ hγ _ h0 i0) i1
  have R := be_add_right hSub hex0 hinv hB (PI.PhNormUnits.mulBy l ex β.2 (PI.PhNormUnits.Xv 1))
    (PI.PhNormUnits.mulBy l ex γ.2 (PI.PhNormUnits.Xv 1)) (PI.PhNormUnits.Xv 0) (c0 _ _ h1) (c0 _ _ h1) h0
    (hI2 β hβ _ h1 i1) (hI2 γ hγ _ h1 i1) i0
  exact sTrans hE L (sTrans hE
    (sAdd hE (hU β hβ hb1 hb2) (hU γ hγ hg1 hg2)) (sSymm hE R))

end PI.PhNormUnits.UnitaryGroupMassFormula
