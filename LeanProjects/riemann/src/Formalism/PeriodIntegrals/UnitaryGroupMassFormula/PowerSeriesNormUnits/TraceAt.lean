import Mathlib
import Formalism.PeriodIntegrals.PhNormUnits
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffFormalSMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.TendstoCoeffOfCont
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffVar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.SimeqSubst1
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.StepUnitsOf

noncomputable section

open Classical

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

variable {p : ℕ} [Fact p.Prime]

section

variable (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense) (hZ : CalcZpScale)
variable {l ex ph : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X) (hph : PowerSeries.constantCoeff ph = 0)
  (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
  (hB : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))

include hE hSub hC hD hZ hex0 hinv hph hIA hB in
theorem trace_at (c d : ℂ_[p]) (hc : IntegralMv (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    (hd : IntegralMv (mulBy l ex d (Xv ()) : MvPowerSeries Unit ℂ_[p])) (t : ℤ_[p]) (ht : c + d = zc t)
    (hsw : Simeq (be l ex ph (mulBy l ex c (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex d (Xv 1))))
    (hU2 : Simeq (phAt ph (mulBy l ex 2 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (2 * 2) * phAt ph (Xv ())))
    (h2inv : ∃ h : ℤ_[p], 2 * zc h = 1) {τ : Type} (w : MvPowerSeries τ ℂ_[p])
    (w0 : MvPowerSeries.constantCoeff w = 0) (wI : IntegralMv w) :
    Simeq (be l ex ph w (mulBy l ex c w)) (MvPowerSeries.C (c + d) * phAt ph w) := by
  have hw2 : ∀ i, MvPowerSeries.constantCoeff (![w, w] i) = 0 := by
    intro i; fin_cases i <;> simpa using w0
  have hcw0 : MvPowerSeries.constantCoeff (mulBy l ex c w) = 0 := constantCoeff_formalSMul hex0 hinv c w w0
  have hdw0 : MvPowerSeries.constantCoeff (mulBy l ex d w) = 0 := constantCoeff_formalSMul hex0 hinv d w w0
  have hcw : IntegralMv (mulBy l ex c w) := int_mulBy_of hSub hex0 hinv c hc w w0 wI
  have hdw : IntegralMv (mulBy l ex d w) := int_mulBy_of hSub hex0 hinv d hd w w0 wI
  have S1 : Simeq (be l ex ph (mulBy l ex c w) w) (be l ex ph w (mulBy l ex d w)) := by
    have e := simeq_subst2 hSub hex0 hinv w w w0 w0 wI wI hsw
    rw [sb_be (![w, w]) hw2 hex0 hinv ph _ _ (constantCoeff_formalSMul hex0 hinv c _ (constantCoeff_var 0)) (constantCoeff_var 1),
      sb_be (![w, w]) hw2 hex0 hinv ph _ _ (constantCoeff_var 0) (constantCoeff_formalSMul hex0 hinv d _ (constantCoeff_var 1)),
      sb_mulBy (![w, w]) hw2 hex0 hinv c _ (constantCoeff_var 0), sb_mulBy (![w, w]) hw2 hex0 hinv d _ (constantCoeff_var 1),
      sb_X (![w, w]) hw2, sb_X (![w, w]) hw2] at e
    simpa using e
  have A : Simeq (be l ex ph w (mulBy l ex c w)) (be l ex ph w (mulBy l ex d w)) := by
    rw [be_comm]; exact S1
  have S3 : Simeq (be l ex ph w (mulBy l ex (zc t) w))
      (be l ex ph w (mulBy l ex c w) + be l ex ph w (mulBy l ex d w)) := by
    rw [← ht, ← add_mulBy hex0 hinv c d w w0]
    exact be_add_right hSub hex0 hinv hB _ _ _ hcw0 hdw0 w0 hcw hdw wI
  have S4 := be_zp hE hSub hex0 hinv hB hC hD hph hIA w w w0 w0 wI wI t
  have S5 : Simeq (be l ex ph w w) (MvPowerSeries.C 2 * phAt ph w) := by
    have n2 := norm_at hSub hex0 hinv 2 (2 * 2) hU2 w w0 wI
    have e : be l ex ph w w = phAt ph (mulBy l ex 2 w) - phAt ph w - phAt ph w := by
      rw [be, add_self hex0 hinv w w0]
    rw [e]
    refine sTrans hE (sSub hE (sSub hE n2 (sRefl hE _)) (sRefl hE _)) (sOfEq hE ?_)
    simp only [map_mul, map_ofNat]
    ring
  have T1 : Simeq (MvPowerSeries.C 2 * be l ex ph w (mulBy l ex c w))
      (MvPowerSeries.C 2 * (MvPowerSeries.C (c + d) * phAt ph w)) := by
    have e1 : MvPowerSeries.C (2 : ℂ_[p]) * be l ex ph w (mulBy l ex c w) =
        be l ex ph w (mulBy l ex c w) + be l ex ph w (mulBy l ex c w) := by
      simp only [map_ofNat]; ring
    rw [e1]
    refine sTrans hE (sAdd hE (sRefl hE _) A) (sTrans hE (sSymm hE S3) (sTrans hE S4 ?_))
    refine sTrans hE (hZ p τ _ _ t S5) (sOfEq hE ?_)
    rw [← ht]
    ring
  obtain ⟨h, hh⟩ := h2inv
  have T2 := hZ p τ _ _ h T1
  refine sTrans hE (sOfEq hE ?_) (sTrans hE T2 (sOfEq hE ?_))
  · rw [← mul_assoc, ← map_mul, mul_comm (zc h), hh, map_one, one_mul]
  · rw [← mul_assoc, ← map_mul, mul_comm (zc h), hh, map_one, one_mul]

include hE hSub hex0 hinv in
theorem sum_at (β γ : ℂ_[p] × ℂ_[p]) (iγ : IntegralMv (mulBy l ex γ.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    (hsw : Simeq (be l ex ph (mulBy l ex β.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex β.2 (Xv 1))))
    (htr : Simeq (be l ex ph (Xv ()) (mulBy l ex (β.2 * γ.1) (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (β.2 * γ.1 + β.1 * γ.2) * phAt ph (Xv ())))
    (nβ : Simeq (phAt ph (mulBy l ex β.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (β.1 * β.2) * phAt ph (Xv ())))
    (nγ : Simeq (phAt ph (mulBy l ex γ.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (γ.1 * γ.2) * phAt ph (Xv ()))) :
    Simeq (phAt ph (mulBy l ex (β.1 + γ.1) (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C ((β.1 + γ.1) * (β.2 + γ.2)) * phAt ph (Xv ())) := by
  have hX0 : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := constantCoeff_var ()
  have hg0 : MvPowerSeries.constantCoeff (mulBy l ex γ.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 :=
    constantCoeff_formalSMul hex0 hinv γ.1 _ hX0
  have hb0 : MvPowerSeries.constantCoeff (mulBy l ex β.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 :=
    constantCoeff_formalSMul hex0 hinv β.1 _ hX0
  have hs2 : ∀ i, MvPowerSeries.constantCoeff
      (![Xv (), mulBy l ex γ.1 (Xv ())] i : MvPowerSeries Unit ℂ_[p]) = 0 := by
    intro i; fin_cases i
    · simp [hX0]
    · simpa using hg0
  have S1 : Simeq (be l ex ph (mulBy l ex β.1 (Xv ())) (mulBy l ex γ.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (be l ex ph (Xv ()) (mulBy l ex (β.2 * γ.1) (Xv ()))) := by
    have e := simeq_subst2 hSub hex0 hinv (Xv ()) (mulBy l ex γ.1 (Xv ())) hX0 hg0 (int_X ()) iγ hsw
    rw [sb_be _ hs2 hex0 hinv ph _ _ (constantCoeff_formalSMul hex0 hinv β.1 _ (constantCoeff_var 0)) (constantCoeff_var 1),
      sb_be _ hs2 hex0 hinv ph _ _ (constantCoeff_var 0) (constantCoeff_formalSMul hex0 hinv β.2 _ (constantCoeff_var 1)),
      sb_mulBy _ hs2 hex0 hinv β.1 _ (constantCoeff_var 0), sb_mulBy _ hs2 hex0 hinv β.2 _ (constantCoeff_var 1),
      sb_X _ hs2, sb_X _ hs2] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    rwa [mulBy_mulBy hex0 hinv β.2 γ.1 _ hX0] at e
  have e : phAt ph (mulBy l ex (β.1 + γ.1) (Xv ())) =
      be l ex ph (mulBy l ex β.1 (Xv ())) (mulBy l ex γ.1 (Xv ())) +
        phAt ph (mulBy l ex β.1 (Xv ())) + phAt ph (mulBy l ex γ.1 (Xv ())) := by
    rw [be, add_mulBy hex0 hinv β.1 γ.1 _ hX0]
    ring
  rw [e]
  refine sTrans hE (sAdd hE (sAdd hE (sTrans hE S1 htr) nβ) nγ) (sOfEq hE ?_)
  simp only [map_add, map_mul]
  ring

end

end PI.PhNormUnits.UnitaryGroupMassFormula
