import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.LiftedThirdRootSubXZeroNeZero

noncomputable section

namespace PI.FglTriFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)

variable {p : ℕ} [Fact p.Prime]

theorem h0X (i : Fin 3) : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
  simp

theorem lam_as {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (s3 W wq) (lam wq) = Lab wq := by
  have H := hasSubst_pr (h0X (p := p) 0) (h0X 1)
  have hl := lam_pr wq (h0X (p := p) 0) (constantCoeff_liftedThirdRoot W wq)
  have hZ0 := PI.AddIntG.Wk.constantCoeff_thirdRoot W wq
  have ws : PowerSeries.subst (s3 W wq) (wser wq) = Lab wq * s3 W wq + pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) (nu wq) := by
    rw [s3, pr, ← psubst_comm hZ0 H, PI.AddIntG.Wk.subst_thirdRoot_wSeries h, MvPowerSeries.subst_add H, MvPowerSeries.subst_mul H]
    rfl
  have hnu : pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1) (nu wq) =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (wser wq) - Lab wq * MvPowerSeries.X 0 := by
    simp only [nu, wv, PI.AddIntG.Xv]
    rw [pr, MvPowerSeries.subst_sub H, MvPowerSeries.subst_mul H, psubst_comm (by simp) H, MvPowerSeries.subst_X H]
    rfl
  rw [ws, hnu] at hl
  have key : (s3 W wq - MvPowerSeries.X 0) *
      (pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (s3 W wq) (lam wq) - Lab wq) = 0 := by
    linear_combination hl
  exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left (liftedThirdRoot_sub_X_zero_ne_zero W wq))

theorem mu_vanish {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq)
    {μ : MvPowerSeries (Fin 3) ℂ_[p]} (hμ : Lac wq - Lab wq = (MvPowerSeries.X 2 - MvPowerSeries.X 1) * μ) :
    MvPowerSeries.subst (upd 2 (s3 W wq)) μ = 0 := by
  have Hφ := hasSubst_upd (2 : Fin 3) (constantCoeff_liftedThirdRoot W wq)
  have e := congrArg (MvPowerSeries.subst (upd 2 (s3 W wq))) hμ
  rw [MvPowerSeries.subst_sub Hφ, MvPowerSeries.subst_mul Hφ, MvPowerSeries.subst_sub Hφ, Lac, Lab,
    pr_comp Hφ (h0X 0) (h0X 2), pr_comp Hφ (h0X 0) (h0X 1), MvPowerSeries.subst_X Hφ, MvPowerSeries.subst_X Hφ,
    MvPowerSeries.subst_X Hφ, upd_ne _ (by decide : (0 : Fin 3) ≠ 2), upd_ne _ (by decide : (1 : Fin 3) ≠ 2),
    upd_self] at e
  rw [← Lab, lam_as h, sub_self] at e
  exact (mul_eq_zero.1 e.symm).resolve_left (liftedThirdRoot_sub_X_one_ne_zero W wq)

theorem subst_updateVar_two_liftedThirdRoot (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (t : MvPowerSeries (Fin 3) ℂ_[p])
    (ht : MvPowerSeries.constantCoeff t = 0) : MvPowerSeries.subst (upd 2 t) (s3 W wq) = s3 W wq := by
  have hz3 : ∀ i, MvPowerSeries.constantCoeff (upd 2 t i) = 0 := fun i => by
    fin_cases i <;> simp [upd, Function.update, ht]
  have hu : MvPowerSeries.HasSubst (upd 2 t) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz3
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [hz3 i]; exact IsNilpotent.zero)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hz3
  have hz2 : ∀ i, MvPowerSeries.constantCoeff
      (![MvPowerSeries.X 0, MvPowerSeries.X 1] i : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := fun i => by
    fin_cases i <;> simp
  have h2 : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]), MvPowerSeries.X 1] := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz2
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [hz2 i]; exact IsNilpotent.zero)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hz2
  unfold s3 pr
  rw [MvPowerSeries.subst_comp_subst_apply h2 hu]
  congr 1
  funext i
  fin_cases i
  · show MvPowerSeries.subst (upd 2 t) (MvPowerSeries.X 0) = MvPowerSeries.X 0
    rw [MvPowerSeries.subst_X hu]
    simp [upd, Function.update_apply]
  · show MvPowerSeries.subst (upd 2 t) (MvPowerSeries.X 1) = MvPowerSeries.X 1
    rw [MvPowerSeries.subst_X hu]
    simp [upd, Function.update_apply]

theorem liftedThirdRoot_mem_coeffSubring {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    s3 W wq ∈ SerS S (Fin 3) :=
  pr_mem (h0X 0) (h0X 1) (X_mem_SerS' S 0) (X_mem_SerS' S 1) (PI.AddIntG.Wk.thirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h)

def zc : Fin 3 → MvPowerSeries (Fin 3) ℂ_[p] := ![0, 0, MvPowerSeries.X 2]

theorem zc_const (i : Fin 3) : MvPowerSeries.constantCoeff (zc (p := p) i) = 0 := by
  fin_cases i <;> simp [zc]

theorem hasSubst_zc : MvPowerSeries.HasSubst (zc (p := p)) := by
  first
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun i => zc_const i)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun i => zc_const (p := p) i)
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => zc_const i)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [zc_const i]; exact IsNilpotent.zero)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (a := zc (p := p)) (by intro i; exact zc_const i)

theorem pr_zero_zero (g : MvPowerSeries (Fin 2) ℂ_[p]) (hg : MvPowerSeries.constantCoeff g = 0) :
    pr (0 : MvPowerSeries (Fin 3) ℂ_[p]) 0 g = 0 := by
  unfold pr
  ext e
  have hz : ∀ i, MvPowerSeries.constantCoeff (![(0 : MvPowerSeries (Fin 3) ℂ_[p]), 0] i) = 0 := fun i => by
    fin_cases i <;> simp
  have ha : MvPowerSeries.HasSubst ![(0 : MvPowerSeries (Fin 3) ℂ_[p]), 0] := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [hz i]; exact IsNilpotent.zero)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hz
  rw [MvPowerSeries.coeff_subst ha, finsum_eq_single _ 0]
  · simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg]
  · intro d hd
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hs
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)]
    · simp
    · fin_cases s <;> simp <;> exact hs

theorem subst_lastVarSubst_liftedThirdRoot (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst (zc (p := p)) (s3 W wq) = 0 := by
  rw [s3, pr_comp (hasSubst_zc (p := p)) (h0X 0) (h0X 1), MvPowerSeries.subst_X (hasSubst_zc (p := p)), MvPowerSeries.subst_X (hasSubst_zc (p := p))]
  exact pr_zero_zero _ (PI.AddIntG.Wk.constantCoeff_thirdRoot W wq)

theorem eq_of_X_two_mul_eq {f g : MvPowerSeries (Fin 3) ℂ_[p]} (h : MvPowerSeries.X 2 * f = MvPowerSeries.X 2 * g) :
    f = g := by
  refine mul_left_cancel₀ ?_ h
  intro h0
  have e := congrArg (MvPowerSeries.coeff (Finsupp.single (2 : Fin 3) 1)) h0
  simp at e

theorem zc_mu {wq : PowerSeries ℂ_[p]} {μ : MvPowerSeries (Fin 3) ℂ_[p]}
    (hμ : Lac wq - Lab wq = (MvPowerSeries.X 2 - MvPowerSeries.X 1) * μ) :
    MvPowerSeries.subst (zc (p := p)) μ = MvPowerSeries.X 2 * PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq := by
  have Hz := hasSubst_zc (p := p)
  have e := congrArg (MvPowerSeries.subst (zc (p := p))) hμ
  rw [MvPowerSeries.subst_sub Hz, MvPowerSeries.subst_mul Hz, MvPowerSeries.subst_sub Hz, Lac, Lab,
    pr_comp Hz (h0X 0) (h0X 2), pr_comp Hz (h0X 0) (h0X 1), MvPowerSeries.subst_X Hz, MvPowerSeries.subst_X Hz,
    MvPowerSeries.subst_X Hz] at e
  have e0 : zc (p := p) 0 = 0 := rfl
  have e1 : zc (p := p) 1 = 0 := rfl
  have e2 : zc (p := p) 2 = MvPowerSeries.X 2 := rfl
  rw [e0, e1, e2, pr_zero_zero _ (PI.AddIntG.Wk.constantCoeff_lam wq), sub_zero, sub_zero] at e
  have hl := lam_pr wq (x := (0 : MvPowerSeries (Fin 3) ℂ_[p])) (y := MvPowerSeries.X 2) (by simp) (by simp)
  rw [PowerSeries.subst_zero_of_constantCoeff_zero (cc_wser wq), wser_X, sub_zero, sub_zero, e] at hl
  apply eq_of_X_two_mul_eq
  apply eq_of_X_two_mul_eq
  linear_combination hl

theorem m_exists {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq)
    {μ : MvPowerSeries (Fin 3) ℂ_[p]} (hμS : μ ∈ SerS S (Fin 3))
    (hμ : Lac wq - Lab wq = (MvPowerSeries.X 2 - MvPowerSeries.X 1) * μ) :
    ∃ m ∈ SerS S (Fin 3), MvPowerSeries.constantCoeff m = 1 ∧ μ = (MvPowerSeries.X 2 - s3 W wq) * m := by
  obtain ⟨m, hmS, hm⟩ := fact_div (k := 2) (constantCoeff_liftedThirdRoot W wq) (liftedThirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h) (subst_updateVar_two_liftedThirdRoot W wq) hμS
    (mu_vanish h hμ)
  refine ⟨m, hmS, ?_, hm⟩
  have Hz := hasSubst_zc (p := p)
  have e := congrArg (MvPowerSeries.subst (zc (p := p))) hm
  rw [zc_mu hμ, MvPowerSeries.subst_mul Hz, MvPowerSeries.subst_sub Hz, MvPowerSeries.subst_X Hz, subst_lastVarSubst_liftedThirdRoot,
    sub_zero] at e
  have e2 : zc (p := p) 2 = MvPowerSeries.X 2 := rfl
  rw [e2] at e
  have e' := eq_of_X_two_mul_eq e
  rw [← cc_subst_eq Hz (zc_const (p := p)) m, ← e', PowerSeries.subst_def,
    cc_subst_eq (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => h0X (p := p) 2)) (fun _ => h0X (p := p) 2)]
  exact PI.AddIntG.Wk.wq_const h

end PI.FglTriFactor.Wk
