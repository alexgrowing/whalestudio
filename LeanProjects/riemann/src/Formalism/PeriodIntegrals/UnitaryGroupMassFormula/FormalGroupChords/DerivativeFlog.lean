import Mathlib
import Formalism.PeriodIntegrals.FglChordFactor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.DXEqDerivative
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.DvCoeffMulEqZeroOfLtOrder
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GlueHoldsVar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupChords.NormDeltaWc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupChords.SubstPairSecondVariable

noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS inv_mem_SerS)

variable {p : ℕ} [Fact p.Prime]

abbrev cP (x : ℂ_[p]) : PowerSeries ℂ_[p] := algebraMap ℂ_[p] (PowerSeries ℂ_[p]) x

def Dser (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  1 - (cP W.a₁ * PowerSeries.X + cP W.a₃ * PowerSeries.X ^ 3 * wq)

def iW (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  -PowerSeries.X * (Dser W wq)⁻¹

theorem wq_const' {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.constantCoeff wq = 1 := by
  have h' : wq = 1 + cP W.a₁ * PowerSeries.X * wq + cP W.a₂ * PowerSeries.X ^ 2 * wq +
      cP W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 + cP W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      cP W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := h
  have e := congrArg PowerSeries.constantCoeff h'
  simpa using e

theorem D_const (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (Dser W wq) = 1 := by
  simp [Dser]

theorem iW_mul_D (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    iW W wq * Dser W wq = -PowerSeries.X := by
  have hc : PowerSeries.constantCoeff (Dser W wq) ≠ 0 := by rw [D_const]; exact one_ne_zero
  rw [iW, mul_assoc, PowerSeries.inv_mul_cancel _ hc, mul_one]

theorem iW_const (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (iW W wq) = 0 := by
  simp [iW]

theorem hasSubst_iW (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : PowerSeries.HasSubst (iW W wq) := by
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero' (iW_const W wq)
  | exact PowerSeries.HasSubst.of_constantCoeff_zero (iW_const W wq)

theorem subst_isWq {W : WeierstrassCurve ℂ_[p]} {wq t : PowerSeries ℂ_[p]} (ht : PowerSeries.HasSubst t)
    (h : IsWq W wq) :
    PowerSeries.subst t wq = 1 + cP W.a₁ * t * PowerSeries.subst t wq + cP W.a₂ * t ^ 2 * PowerSeries.subst t wq +
      cP W.a₃ * t ^ 3 * PowerSeries.subst t wq ^ 2 + cP W.a₄ * t ^ 4 * PowerSeries.subst t wq ^ 2 +
      cP W.a₆ * t ^ 6 * PowerSeries.subst t wq ^ 3 := by
  have h' : wq = 1 + cP W.a₁ * PowerSeries.X * wq + cP W.a₂ * PowerSeries.X ^ 2 * wq +
      cP W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 + cP W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      cP W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := h
  have hφ : ∀ f : PowerSeries ℂ_[p], PowerSeries.subst t f = PowerSeries.substAlgHom ht f := fun f => by
    rw [PowerSeries.coe_substAlgHom]
  have hX : PowerSeries.substAlgHom ht (PowerSeries.X : PowerSeries ℂ_[p]) = t := by
    rw [← hφ, PowerSeries.subst_X ht]
  conv_lhs => rw [h']
  simp only [hφ, map_add, map_mul, map_pow, map_one, AlgHom.commutes, hX]

theorem fix_unique {a₁ a₂ a₃ a₄ a₆ : ℂ_[p]} {t V₁ V₂ : PowerSeries ℂ_[p]} (ht : PowerSeries.constantCoeff t = 0)
    (h₁ : V₁ = 1 + cP a₁ * t * V₁ + cP a₂ * t ^ 2 * V₁ + cP a₃ * t ^ 3 * V₁ ^ 2 + cP a₄ * t ^ 4 * V₁ ^ 2 +
      cP a₆ * t ^ 6 * V₁ ^ 3)
    (h₂ : V₂ = 1 + cP a₁ * t * V₂ + cP a₂ * t ^ 2 * V₂ + cP a₃ * t ^ 3 * V₂ ^ 2 + cP a₄ * t ^ 4 * V₂ ^ 2 +
      cP a₆ * t ^ 6 * V₂ ^ 3) : V₁ = V₂ := by
  have key : (V₁ - V₂) * (1 - (cP a₁ * t + cP a₂ * t ^ 2 + cP a₃ * t ^ 3 * (V₁ + V₂) +
      cP a₄ * t ^ 4 * (V₁ + V₂) + cP a₆ * t ^ 6 * (V₁ ^ 2 + V₁ * V₂ + V₂ ^ 2))) = 0 := by
    linear_combination h₁ - h₂
  have hc : PowerSeries.constantCoeff (1 - (cP a₁ * t + cP a₂ * t ^ 2 + cP a₃ * t ^ 3 * (V₁ + V₂) +
      cP a₄ * t ^ 4 * (V₁ + V₂) + cP a₆ * t ^ 6 * (V₁ ^ 2 + V₁ * V₂ + V₂ ^ 2))) ≠ 0 := by
    simp [ht]
  rcases mul_eq_zero.1 key with h | h
  · exact sub_eq_zero.1 h
  · exact absurd (by rw [h, map_zero]) hc

theorem wq_iW {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.subst (iW W wq) wq = wq * Dser W wq ^ 2 := by
  have hw : wq = 1 + cP W.a₁ * PowerSeries.X * wq + cP W.a₂ * PowerSeries.X ^ 2 * wq +
      cP W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 + cP W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      cP W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := h
  refine fix_unique (a₁ := W.a₁) (a₂ := W.a₂) (a₃ := W.a₃) (a₄ := W.a₄) (a₆ := W.a₆) (iW_const W wq) ?_ ?_
  · exact subst_isWq (hasSubst_iW W wq) h
  · have e := iW_mul_D W wq
    generalize iW W wq = i at e ⊢
    generalize hDdef : Dser W wq = D at e ⊢
    have hD : D = 1 - (cP W.a₁ * PowerSeries.X + cP W.a₃ * PowerSeries.X ^ 3 * wq) := hDdef.symm
    linear_combination (-(cP W.a₁) * wq * D - cP W.a₂ * wq * (i * D - PowerSeries.X)
      - cP W.a₃ * wq ^ 2 * D * ((i * D) ^ 2 - i * D * PowerSeries.X + PowerSeries.X ^ 2)
      - cP W.a₄ * wq ^ 2 * ((i * D) ^ 3 - (i * D) ^ 2 * PowerSeries.X + i * D * PowerSeries.X ^ 2 - PowerSeries.X ^ 3)
      - cP W.a₆ * wq ^ 3 * ((i * D) ^ 5 - (i * D) ^ 4 * PowerSeries.X + (i * D) ^ 3 * PowerSeries.X ^ 2
          - (i * D) ^ 2 * PowerSeries.X ^ 3 + i * D * PowerSeries.X ^ 4 - PowerSeries.X ^ 5)) * e
      + hw + wq * (D + 1) * hD

theorem dX_eq (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative ℂ_[p] f := by
  ext n
  rw [dX, PowerSeries.coeff_mk, PowerSeries.coeff_derivative]
  ring

theorem derivative_flog' (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.derivative ℂ_[p] (flog W wq) = omegaW W wq := by
  ext n
  rw [PowerSeries.coeff_derivative, flog, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
  push_cast
  exact div_mul_cancel₀ _ (Nat.cast_add_one_ne_zero n)

theorem flog_const (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, flog, PowerSeries.coeff_mk, if_pos rfl]

theorem omega_mul {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    omegaW W wq * (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2)) =
      -2 * wq - PowerSeries.X * PowerSeries.derivative ℂ_[p] wq := by
  have hM : PowerSeries.constantCoeff (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2)) ≠ 0 := by
    have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
    simp [wq_const' h, h2]
  simp only [omegaW]
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hM, mul_one, dX_eq]

theorem deriv_ext {f g : PowerSeries ℂ_[p]} (hd : PowerSeries.derivative ℂ_[p] f = PowerSeries.derivative ℂ_[p] g)
    (h0 : PowerSeries.constantCoeff f = PowerSeries.constantCoeff g) : f = g := by
  ext n
  rcases n with _ | n
  · simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
  · have e := congrArg (PowerSeries.coeff n) hd
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at e
    first
    | exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero n) e
    | exact mul_right_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) e

private theorem derivative_subst_eq_subst_derivative_mul (a f : PowerSeries ℂ_[p]) (ha : PowerSeries.HasSubst a) :
    PowerSeries.derivative ℂ_[p] (PowerSeries.subst a f) =
      PowerSeries.subst a (PowerSeries.derivative ℂ_[p] f) * PowerSeries.derivative ℂ_[p] a := by
  have hpd : ∀ g : PowerSeries ℂ_[p], MvPowerSeries.pderiv ℂ_[p] () g = PowerSeries.derivative ℂ_[p] g := by
    intro g
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_derivative]
    show MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.pderiv ℂ_[p] () g) = _
    rw [MvPowerSeries.coeff_pderiv, ← Finsupp.single_add, Finsupp.single_eq_same]
    rfl
  have := PI.AddIntG.Wk.pderiv_subst (σ := Unit) ha f ()
  rw [hpd, hpd] at this
  exact this

theorem flog_iW {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.subst (iW W wq) (flog W wq) = -flog W wq := by
  have hs := hasSubst_iW W wq
  have hφ : ∀ f : PowerSeries ℂ_[p], PowerSeries.subst (iW W wq) f = PowerSeries.substAlgHom hs f := fun f => by
    rw [PowerSeries.coe_substAlgHom]
  have hX : PowerSeries.substAlgHom hs (PowerSeries.X : PowerSeries ℂ_[p]) = iW W wq := by
    rw [← hφ, PowerSeries.subst_X hs]
  apply deriv_ext
  · have hwi := wq_iW h
    have e := iW_mul_D W wq
    have hD0 : Dser W wq = 1 - (cP W.a₁ * PowerSeries.X + cP W.a₃ * PowerSeries.X ^ 3 * wq) := rfl
    have hom := omega_mul h
    have hom' := congrArg (PowerSeries.substAlgHom hs) hom
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, AlgHom.commutes, hX] at hom'
    simp only [← hφ] at hom'
    rw [hwi] at hom'
    have hcw := derivative_subst_eq_subst_derivative_mul (iW W wq) wq hs
    rw [hwi] at hcw
    have hdwD : PowerSeries.derivative ℂ_[p] (wq * Dser W wq ^ 2) =
        PowerSeries.derivative ℂ_[p] wq * Dser W wq ^ 2 +
          wq * (2 * Dser W wq * PowerSeries.derivative ℂ_[p] (Dser W wq)) := by
      rw [pow_two, Derivation.leibniz, Derivation.leibniz]
      simp only [smul_eq_mul]
      ring
    have e2 := congrArg (PowerSeries.derivative ℂ_[p]) e
    rw [Derivation.leibniz, map_neg, PowerSeries.derivative_X] at e2
    simp only [smul_eq_mul] at e2
    have hDM : Dser W wq * (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
        algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2)) ≠ 0 := by
      intro h0
      have h00 := congrArg PowerSeries.constantCoeff h0
      have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
      simp [D_const, wq_const' h, h2] at h00
    rw [derivative_subst_eq_subst_derivative_mul (iW W wq) (flog W wq) hs, derivative_flog', map_neg, derivative_flog']
    have key : (PowerSeries.subst (iW W wq) (omegaW W wq) * PowerSeries.derivative ℂ_[p] (iW W wq) +
        omegaW W wq) * (Dser W wq * (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
        algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2))) = 0 := by
      linear_combination Dser W wq * hom + PowerSeries.derivative ℂ_[p] (iW W wq) * hom'
        - PowerSeries.derivative ℂ_[p] (iW W wq) * PowerSeries.subst (iW W wq) (omegaW W wq) * wq *
          Dser W wq * (cP W.a₁ + cP W.a₃ * wq * ((iW W wq * Dser W wq) ^ 2 -
            iW W wq * Dser W wq * PowerSeries.X + PowerSeries.X ^ 2)) * e
        - PowerSeries.derivative ℂ_[p] wq * Dser W wq * e
        + 2 * PowerSeries.derivative ℂ_[p] (iW W wq) * PowerSeries.subst (iW W wq) (omegaW W wq) * wq *
          Dser W wq * hD0
        - 2 * wq * Dser W wq * e2 + iW W wq * (hcw - hdwD)
    have h3 := (mul_eq_zero.1 key).resolve_right hDM
    linear_combination h3
  · obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.2 (flog_const W wq)
    rw [map_neg, flog_const, neg_zero, hg, hφ, map_mul, hX, map_mul, iW_const, zero_mul]

theorem iW_mem {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h1 : W.a₁ ∈ S)
    (h3 : W.a₃ ∈ S) (hw : ∀ n, PowerSeries.coeff n wq ∈ S) : ∀ n, PowerSeries.coeff n (iW W wq) ∈ S := by
  have hcP : ∀ x ∈ S, ∀ n, PowerSeries.coeff n (cP x) ∈ S := by
    intro x hx n
    rw [cP, Algebra.algebraMap_eq_smul_one, PowerSeries.coeff_smul, PowerSeries.coeff_one]
    split_ifs
    · rw [smul_eq_mul, mul_one]; exact hx
    · rw [smul_zero]; exact S.zero_mem
  have hXm : (PowerSeries.X : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := serS_unit fun n => by
    rw [PowerSeries.coeff_X]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have h1m := serS_unit (hcP _ h1)
  have h3m := serS_unit (hcP _ h3)
  have hwm := serS_unit hw
  have hDm : (Dser W wq : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit :=
    (SerS S Unit).sub_mem (SerS S Unit).one_mem ((SerS S Unit).add_mem ((SerS S Unit).mul_mem h1m hXm)
      ((SerS S Unit).mul_mem ((SerS S Unit).mul_mem h3m ((SerS S Unit).pow_mem hXm 3)) hwm))
  have hi : (iW W wq : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit :=
    (SerS S Unit).mul_mem ((SerS S Unit).neg_mem hXm) (inv_mem_SerS S (D_const W wq) hDm)
  exact serS_unit_iff.1 hi

end PI.FglChordFactor.Wk
