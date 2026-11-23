import Mathlib
import Formalism.PeriodIntegrals.FglChordFactor
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AddIntG

noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

def Wc : WeierstrassCurve ℂ_[2] := ⟨0, 0, 1, 0, 0⟩

def catC : PowerSeries ℂ_[2] := PowerSeries.map (Nat.castRingHom ℂ_[2]) PowerSeries.catalanSeries

theorem catC_eq : catC ^ 2 * PowerSeries.X + 1 = catC := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℂ_[2])) PowerSeries.catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_one, PowerSeries.map_X] at h
  exact h

def wqc : PowerSeries ℂ_[2] := PowerSeries.subst (PowerSeries.X ^ 3 : PowerSeries ℂ_[2]) catC

theorem wqc_isWq : IsWq Wc wqc := by
  have hX3 : PowerSeries.HasSubst (PowerSeries.X ^ 3 : PowerSeries ℂ_[2]) :=
    PowerSeries.HasSubst.X_pow (by norm_num)
  have h1 : PowerSeries.subst (PowerSeries.X ^ 3 : PowerSeries ℂ_[2]) (1 : PowerSeries ℂ_[2]) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hX3, map_one]
  have key := congrArg (PowerSeries.subst (PowerSeries.X ^ 3 : PowerSeries ℂ_[2])) catC_eq
  rw [PowerSeries.subst_add hX3, PowerSeries.subst_mul hX3, PowerSeries.subst_pow hX3,
    PowerSeries.subst_X hX3, h1] at key
  simp only [IsWq, Wc, map_zero, map_one, zero_mul, add_zero, one_mul]
  rw [wqc]
  linear_combination -key

theorem norm_delta_Wc : ‖Wc.Δ‖ = 1 := by
  have hΔ : Wc.Δ = -27 := by
    simp only [Wc, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    norm_num
  have h27 : ‖(27 : ℚ_[2])‖ = 1 := by
    have := (Padic.norm_natCast_eq_one_iff (p := 2) (n := 27)).2 (by norm_num)
    simpa using this
  have hc : (27 : ℂ_[2]) = algebraMap ℚ_[2] ℂ_[2] 27 := (map_ofNat _ 27).symm
  rw [hΔ, norm_neg, hc, norm_algebraMap', h27]

theorem isWq_bridge {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h : IsWq W wq) : PI.AddIntG.IsWq W wq := h

theorem flog_bridge {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    flog W wq = PI.AddIntG.flog W wq := rfl

theorem add_bridge {p : ℕ} [Fact p.Prime] {σ : Type*} (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) :
    add l ex a b = PI.AddIntG.add l ex a b := rfl

theorem inhab : ∃ (W : WeierstrassCurve ℂ_[2]) (wq ex : PowerSeries ℂ_[2]),
    IsIntP W.a₁ ∧ IsIntP W.a₂ ∧ IsIntP W.a₃ ∧ IsIntP W.a₄ ∧ IsIntP W.a₆ ∧ ‖W.Δ‖ = 1 ∧
    IsWq W wq ∧ PowerSeries.constantCoeff ex = 0 ∧ PowerSeries.subst ex (flog W wq) = PowerSeries.X ∧
    IntegralMv (add (flog W wq) ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[2]) := by
  have hW := wqc_isWq
  have hl0 : PowerSeries.constantCoeff (flog Wc wqc) = 0 := PI.AddIntG.Wk.flog_constantCoeff Wc wqc
  have hu : IsUnit (PowerSeries.coeff 1 (flog Wc wqc)) := by
    rw [flog_bridge, PI.AddIntG.Wk.coeff_one_flog (isWq_bridge hW)]; exact isUnit_one
  set ex := PowerSeries.substInvOfIsUnit (flog Wc wqc) hu
  have hex0 : PowerSeries.constantCoeff ex = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ hu
  have hex : PowerSeries.subst ex (flog Wc wqc) = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right (flog Wc wqc) hl0 hu
  have hI := (additive_integral_generation 2 Wc wqc ex (by simp [PI.AddIntG.IsIntP, Wc]) (by simp [PI.AddIntG.IsIntP, Wc])
    (by simp [PI.AddIntG.IsIntP, Wc]) (by simp [PI.AddIntG.IsIntP, Wc]) (by simp [PI.AddIntG.IsIntP, Wc])
    (isWq_bridge hW) hex0 hex).1
  exact ⟨Wc, wqc, ex, by simp [IsIntP, Wc], by simp [IsIntP, Wc], by simp [IsIntP, Wc], by simp [IsIntP, Wc],
    by simp [IsIntP, Wc], norm_delta_Wc, hW, hex0, hex, hI⟩

end PI.FglChordFactor.Wk
