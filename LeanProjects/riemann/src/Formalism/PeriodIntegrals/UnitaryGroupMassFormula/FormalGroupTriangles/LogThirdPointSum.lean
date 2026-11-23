import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.SubstUpdateVarTwoLiftedThirdRoot
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GlueHoldsVar

noncomputable section

namespace PI.FglTriFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)

variable {p : ℕ} [Fact p.Prime]

theorem cc_flog (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  first
  | exact PI.FglChordFactor.Wk.flog_const W wq
  | (rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, flog, PowerSeries.coeff_mk, if_pos rfl])
  | simp [flog]

theorem abel' {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    lg (flog W wq) (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) + lg (flog W wq) (MvPowerSeries.X 1) +
      lg (flog W wq) (Z3 W wq) = 0 := PI.AddIntG.Wk.abel h

theorem inv' {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (h : IsWq W wq)
    (hex0 : PowerSeries.constantCoeff ex = 0) (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X) :
    PowerSeries.subst (flog W wq) ex = PowerSeries.X :=
  PI.AddIntG.Wk.subst_left_inv (cc_flog W wq) (PI.AddIntG.Wk.coeff_one_flog h) hex0 hex

theorem cc_X {τ : Type*} (i : τ) : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries τ ℂ_[p]) = 0 := by
  simp

theorem log_third_point_sum {τ : Type*} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq)
    {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    lg (flog W wq) (pr x y (Z3 W wq)) = -lg (flog W wq) x - lg (flog W wq) y := by
  have H := hasSubst_pr hx hy
  have e := congrArg (MvPowerSeries.subst ![x, y]) (abel' h)
  rw [MvPowerSeries.subst_add H, MvPowerSeries.subst_add H, subst_lg H (cc_X 0), subst_lg H (cc_X 1),
    subst_lg H (PI.AddIntG.Wk.constantCoeff_thirdRoot W wq), MvPowerSeries.subst_X H, MvPowerSeries.subst_X H] at e
  have hz : MvPowerSeries.subst ![x, y] (0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom H, map_zero]
  rw [hz] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
  rw [pr]
  linear_combination e

theorem sub_factor {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq)
    (hex0 : PowerSeries.constantCoeff ex = 0) (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X)
    (hF : add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2)) :
    ∃ u ∈ SerS S (Fin 2), MvPowerSeries.constantCoeff u = 1 ∧
      sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * u := by
  have hl0 := cc_flog W wq
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := map_zero _
  set Zn := pr (0 : MvPowerSeries (Fin 2) ℂ_[p]) (MvPowerSeries.X 1) (Z3 W wq) with hZn
  have hZn0 : MvPowerSeries.constantCoeff Zn = 0 := cc_pr h0 (cc_X 1) (PI.AddIntG.Wk.constantCoeff_thirdRoot W wq)
  have hZnS : Zn ∈ SerS S (Fin 2) :=
    pr_mem h0 (cc_X 1) (zero_mem _) (X_mem_SerS' S 1) (PI.AddIntG.Wk.thirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h)
  have hlZn : lg (flog W wq) Zn = -lg (flog W wq) (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) := by
    rw [hZn, log_third_point_sum h h0 (cc_X 1), lg_zero hl0, neg_zero, zero_sub]
  have hsa : sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) =
      add (flog W wq) ex (MvPowerSeries.X 0) Zn := by
    unfold sub add; rw [hlZn, sub_eq_add_neg]
  have hGS : sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2) := by
    rw [hsa, add_pr hl0 (cc_X 0) hZn0]
    exact pr_mem (cc_X 0) hZn0 (X_mem_SerS' S 0) hZnS hF
  have HU := hasSubst_upd (0 : Fin 2) (cc_X (p := p) (1 : Fin 2))
  obtain ⟨u, huS, hu⟩ := fact_div (k := 0) (cc_X 1) (X_mem_SerS' S 1)
    (fun t ht => by rw [MvPowerSeries.subst_X (hasSubst_upd 0 ht), upd_ne _ (by decide)]) hGS (by
      rw [subst_sub hl0 HU (cc_X 0) (cc_X 1), MvPowerSeries.subst_X HU, MvPowerSeries.subst_X HU, upd_self,
        upd_ne _ (by decide : (1 : Fin 2) ≠ 0)]
      unfold sub; rw [sub_self, pt_zero hex0])
  refine ⟨u, huS, ?_, hu⟩
  have H1 := hasSubst_upd (1 : Fin 2) h0
  have e := congrArg (MvPowerSeries.subst (upd (1 : Fin 2) (0 : MvPowerSeries (Fin 2) ℂ_[p]))) hu
  rw [subst_sub hl0 H1 (cc_X 0) (cc_X 1), MvPowerSeries.subst_mul H1, MvPowerSeries.subst_sub H1,
    MvPowerSeries.subst_X H1, MvPowerSeries.subst_X H1, upd_self, upd_ne _ (by decide : (0 : Fin 2) ≠ 1),
    sub_zero] at e
  have e' : sub (flog W wq) ex (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) 0 = MvPowerSeries.X 0 := by
    unfold sub; rw [lg_zero hl0, sub_zero, pt_lg hl0 (inv' h hex0 hex) (cc_X 0)]
  rw [e'] at e
  have hX0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    intro h'
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h'
    simp [MvPowerSeries.coeff_X] at this
  have e2 : MvPowerSeries.X 0 * (MvPowerSeries.subst (upd (1 : Fin 2) (0 : MvPowerSeries (Fin 2) ℂ_[p])) u - 1) = 0 := by
    linear_combination -e
  have e3 := sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_left hX0)
  rw [← cc_subst_eq H1 (upd_const h0) u, e3, map_one]

theorem add_factor {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq)
    (hex0 : PowerSeries.constantCoeff ex = 0) (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X)
    (hF : add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2)) :
    ∃ u ∈ SerS S (Fin 3), MvPowerSeries.constantCoeff u = 1 ∧
      add (flog W wq) ex (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) (MvPowerSeries.X 2) =
        (MvPowerSeries.X 2 - s3 W wq) * u := by
  have hl0 := cc_flog W wq
  set l := flog W wq with hl
  have hab0 : MvPowerSeries.constantCoeff
      (add l ex (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1)) = 0 :=
    cc_add hl0 hex0 (cc_X 0) (cc_X 1)
  have hGS : add l ex (add l ex (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1))
      (MvPowerSeries.X 2) ∈ SerS S (Fin 3) := by
    rw [add_pr hl0 hab0 (cc_X 2), add_pr hl0 (cc_X 0) (cc_X 1)]
    have hab0' := hab0
    rw [add_pr hl0 (cc_X 0) (cc_X 1)] at hab0'
    exact pr_mem hab0' (cc_X 2) (pr_mem (cc_X 0) (cc_X 1) (X_mem_SerS' S 0) (X_mem_SerS' S 1) hF)
      (X_mem_SerS' S 2) hF
  have hlab : lg l (add l ex (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1)) =
      lg l (MvPowerSeries.X 0) + lg l (MvPowerSeries.X 1) := by
    unfold add
    exact lg_pt hex0 hex (by rw [map_add, cc_lg hl0 (cc_X 0), cc_lg hl0 (cc_X 1), add_zero])
  have HU := hasSubst_upd (2 : Fin 3) (constantCoeff_liftedThirdRoot W wq)
  obtain ⟨u, huS, hu⟩ := fact_div (k := 2) (constantCoeff_liftedThirdRoot W wq) (liftedThirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h) (subst_updateVar_two_liftedThirdRoot W wq) hGS (by
      rw [subst_add hl0 HU hab0 (cc_X 2), subst_add hl0 HU (cc_X 0) (cc_X 1), MvPowerSeries.subst_X HU,
        MvPowerSeries.subst_X HU, MvPowerSeries.subst_X HU, upd_self, upd_ne _ (by decide : (0 : Fin 3) ≠ 2),
        upd_ne _ (by decide : (1 : Fin 3) ≠ 2)]
      have hZ := log_third_point_sum h (cc_X (p := p) (0 : Fin 3)) (cc_X 1)
      rw [← hl] at hZ
      change pt ex (lg l (add l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) + lg l (s3 W wq)) = 0
      rw [hlab, s3, hZ]
      rw [show lg l (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) + lg l (MvPowerSeries.X 1) +
          (-lg l (MvPowerSeries.X 0) - lg l (MvPowerSeries.X 1)) = 0 by ring, pt_zero hex0])
  refine ⟨u, huS, ?_, hu⟩
  have Hz := hasSubst_zc (p := p)
  have e := congrArg (MvPowerSeries.subst (zc (p := p))) hu
  rw [subst_add hl0 Hz hab0 (cc_X 2), subst_add hl0 Hz (cc_X 0) (cc_X 1), MvPowerSeries.subst_mul Hz,
    MvPowerSeries.subst_sub Hz, MvPowerSeries.subst_X Hz, MvPowerSeries.subst_X Hz, MvPowerSeries.subst_X Hz,
    subst_lastVarSubst_liftedThirdRoot, sub_zero] at e
  have e0 : zc (p := p) 0 = 0 := rfl
  have e1 : zc (p := p) 1 = 0 := rfl
  have e2 : zc (p := p) 2 = MvPowerSeries.X 2 := rfl
  rw [e0, e1, e2] at e
  have e00 : add l ex (0 : MvPowerSeries (Fin 3) ℂ_[p]) 0 = 0 := by
    unfold add; rw [lg_zero hl0, add_zero, pt_zero hex0]
  have ec : add l ex (0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 2) = MvPowerSeries.X 2 := by
    unfold add; rw [lg_zero hl0, zero_add, pt_lg hl0 (inv' h hex0 hex) (cc_X 2)]
  rw [e00, ec] at e
  have e' := eq_of_X_two_mul_eq (f := MvPowerSeries.subst (zc (p := p)) u) (g := 1) (by rw [mul_one]; exact e.symm)
  rw [← cc_subst_eq Hz (zc_const (p := p)) u, e', map_one]

end PI.FglTriFactor.Wk
