import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.PairSubstXZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.FormalGroupLawExists

noncomputable section

namespace PI.FglTriFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)

variable {p : ℕ} [Fact p.Prime]

theorem wser_X {τ : Type*} (wq : PowerSeries ℂ_[p]) (i : τ) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries τ ℂ_[p]) (wser wq) =
      (MvPowerSeries.X i) ^ 3 * PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries τ ℂ_[p]) wq := by
  have hX := PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X (R := ℂ_[p]) i)
  rw [wser, PowerSeries.subst_mul hX, PowerSeries.subst_pow hX, PowerSeries.subst_X hX]

theorem cc_wser (wq : PowerSeries ℂ_[p]) : PowerSeries.constantCoeff (wser wq) = 0 := by
  simp [wser]

theorem lam_pr {τ : Type*} (wq : PowerSeries ℂ_[p]) {x y : MvPowerSeries τ ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    (y - x) * pr x y (lam wq) = PowerSeries.subst y (wser wq) - PowerSeries.subst x (wser wq) := by
  have hb : MvPowerSeries.HasSubst (![x, y] : Fin 2 → MvPowerSeries τ ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp [hx, hy])
  have hcomp : ∀ i : Fin 2, MvPowerSeries.subst ![x, y] (PI.AddIntG.Wk.wv wq i) =
      PowerSeries.subst ((![x, y] : Fin 2 → MvPowerSeries τ ℂ_[p]) i) (wser wq) := by
    intro i
    have hXi : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[p]) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
    rw [PI.AddIntG.Wk.wv, PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hXi.const hb]
    simp only [MvPowerSeries.subst_X hb]
    rfl
  have h := congrArg (MvPowerSeries.subst ![x, y]) (PI.AddIntG.Wk.lam_mul wq)
  rw [MvPowerSeries.subst_mul hb, MvPowerSeries.subst_sub hb, MvPowerSeries.subst_sub hb, hcomp 1, hcomp 0] at h
  simp only [MvPowerSeries.subst_X hb, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at h
  exact h

def Lab (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) (lam wq)

def Lac (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  pr (MvPowerSeries.X 0) (MvPowerSeries.X 2) (lam wq)

def s3 (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) (Z3 W wq)

theorem T_eq (wq : PowerSeries ℂ_[p]) :
    T wq = (MvPowerSeries.X 1 - MvPowerSeries.X 0) * (MvPowerSeries.X 2 - MvPowerSeries.X 0) * (Lac wq - Lab wq) := by
  have hAB := lam_pr wq (x := (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p])) (y := MvPowerSeries.X 1)
    (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _)
  have hAC := lam_pr wq (x := (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p])) (y := MvPowerSeries.X 2)
    (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _)
  rw [wser_X, wser_X] at hAB hAC
  simp only [T, Lab, Lac]
  linear_combination (MvPowerSeries.X 2 - MvPowerSeries.X 0) * hAB - (MvPowerSeries.X 1 - MvPowerSeries.X 0) * hAC

theorem lam_SerS {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hwq : ∀ n, PowerSeries.coeff n wq ∈ S) :
    lam wq ∈ SerS S (Fin 2) := by
  refine ⟨fun e => ⟨lam wq e, ?_⟩, ?_⟩
  · show PowerSeries.coeff (e 0 + e 1 + 1) (wser wq) ∈ S
    rw [wser, PowerSeries.coeff_X_pow_mul']
    split_ifs
    · exact hwq _
    · exact S.zero_mem
  · ext e
    rfl

private theorem coeff_pr_X_X (i j : Fin 3) (hij : i ≠ j) (f : MvPowerSeries (Fin 2) ℂ_[p]) (e : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff e (pr (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X j) f) =
      if e = Finsupp.single i (e i) + Finsupp.single j (e j) then
        MvPowerSeries.coeff (Finsupp.single 0 (e i) + Finsupp.single 1 (e j)) f else 0 := by
  classical
  have ha : MvPowerSeries.HasSubst
      (![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  have hprod : ∀ d : Fin 2 →₀ ℕ,
      (d.prod fun s k => (![MvPowerSeries.X i, MvPowerSeries.X j] s : MvPowerSeries (Fin 3) ℂ_[p]) ^ k) =
        MvPowerSeries.monomial (Finsupp.single i (d 0) + Finsupp.single j (d 1)) 1 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, MvPowerSeries.X_pow_eq,
      MvPowerSeries.monomial_mul_monomial, mul_one]
  have hij' : j ≠ i := Ne.symm hij
  unfold pr
  rw [MvPowerSeries.coeff_subst ha]
  simp only [hprod, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [finsum_eq_single _ (Finsupp.single 0 (e i) + Finsupp.single 1 (e j)) (fun d hd => by
      rw [if_neg]
      intro h'
      apply hd
      have hi := congrArg (fun f => f i) h'
      have hj := congrArg (fun f => f j) h'
      simp [Finsupp.single_apply, hij, hij'] at hi hj
      ext k
      fin_cases k
      · simp [hi]
      · simp [hj])]
    have e0 : (Finsupp.single (0 : Fin 2) (e i) + Finsupp.single 1 (e j) : Fin 2 →₀ ℕ) 0 = e i := by simp
    have e1 : (Finsupp.single (0 : Fin 2) (e i) + Finsupp.single 1 (e j) : Fin 2 →₀ ℕ) 1 = e j := by simp
    rw [if_pos (by rw [e0, e1]; exact h)]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    rw [if_neg]
    intro h'
    apply h
    rw [h']
    simp [Finsupp.single_apply, hij, hij']

set_option maxHeartbeats 800000 in

theorem mu_exists {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hwq : ∀ n, PowerSeries.coeff n wq ∈ S) :
    ∃ μ ∈ SerS S (Fin 3), Lac wq - Lab wq = (MvPowerSeries.X 2 - MvPowerSeries.X 1) * μ := by
  classical
  obtain ⟨μ, hμc⟩ : ∃ μ : MvPowerSeries (Fin 3) ℂ_[p], ∀ e, MvPowerSeries.coeff e μ =
      MvPowerSeries.coeff (Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1 + e 2 + 1)) (lam wq) :=
    ⟨fun e => MvPowerSeries.coeff (Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1 + e 2 + 1)) (lam wq),
      fun e => by simp only [MvPowerSeries.coeff_apply]; exact MvPowerSeries.coeff_apply _ _⟩
  have hlam : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d (lam wq) = PowerSeries.coeff (d 0 + d 1 + 1) (wser wq) :=
    fun d => by rw [MvPowerSeries.coeff_apply]; rfl
  refine ⟨μ, (mem_SerS S _).2 (fun e => ?_), ?_⟩
  · rw [hμc]
    exact (mem_SerS S _).1 (lam_SerS hwq) _
  · ext e
    have h02 : (e = Finsupp.single 0 (e 0) + Finsupp.single 2 (e 2)) ↔ e 1 = 0 := by
      constructor
      · intro h
        rw [h]
        simp [Finsupp.single_apply]
      · intro h
        ext k
        fin_cases k <;> simp [Finsupp.single_apply, h]
    have h01 : (e = Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1)) ↔ e 2 = 0 := by
      constructor
      · intro h
        rw [h]
        simp [Finsupp.single_apply]
      · intro h
        ext k
        fin_cases k <;> simp [Finsupp.single_apply, h]
    have hX : ∀ k : Fin 3, (MvPowerSeries.X k : MvPowerSeries (Fin 3) ℂ_[p]) =
        MvPowerSeries.monomial (Finsupp.single k 1) 1 := fun k => by
      rw [← MvPowerSeries.X_pow_eq, pow_one]
    rw [map_sub, Lac, Lab, coeff_pr_X_X 0 2 (by decide), coeff_pr_X_X 0 1 (by decide), sub_mul, map_sub, hX 2, hX 1,
      MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, hμc, hμc, hlam, hlam, hlam, hlam]
    simp only [Finsupp.single_le_iff, h02, h01, one_mul]
    have hidx : ∀ a b : ℕ, a = b → PowerSeries.coeff a (wser wq) = PowerSeries.coeff b (wser wq) :=
      fun a b h => by rw [h]
    by_cases h1 : e 1 = 0 <;> by_cases h2 : e 2 = 0
    · rw [if_pos h1, if_pos h2, if_neg (by omega), if_neg (by omega), sub_self, sub_eq_zero]
      apply hidx
      simp [Finsupp.single_apply, h1, h2]
    · rw [if_pos h1, if_neg h2, if_pos (by omega), if_neg (by omega), sub_zero, sub_zero]
      apply hidx
      simp [Finsupp.single_apply, Finsupp.tsub_apply, h1]
      omega
    · rw [if_neg h1, if_pos h2, if_neg (by omega), if_pos (by omega), zero_sub, zero_sub, neg_inj]
      apply hidx
      simp [Finsupp.single_apply, Finsupp.tsub_apply, h2]
      omega
    · rw [if_neg h1, if_neg h2, if_pos (by omega), if_pos (by omega), sub_self, eq_comm, sub_eq_zero]
      apply hidx
      simp [Finsupp.single_apply, Finsupp.tsub_apply]
      omega

theorem subst_pairSubst_zero_one (g : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1, (0 : MvPowerSeries (Fin 2) ℂ_[p])]
      (pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1) g) = g := by
  have h3 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  have h2 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  rw [pr, MvPowerSeries.subst_comp_subst_apply h2 h3]
  have e : (fun s => MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] :
      Fin 3 → MvPowerSeries (Fin 2) ℂ_[p])
      ((![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[p]) s)) =
      MvPowerSeries.X := by
    funext s
    fin_cases s <;> simp [MvPowerSeries.subst_X h3]
  rw [e, MvPowerSeries.subst_self]
  rfl

theorem pairSubst_zero_one_ne_zero {g : MvPowerSeries (Fin 2) ℂ_[p]} (hg : g ≠ 0) :
    pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1) g ≠ 0 := by
  have h3 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  intro h
  apply hg
  rw [← subst_pairSubst_zero_one g, h, ← MvPowerSeries.coe_substAlgHom h3, map_zero]

theorem constantCoeff_liftedThirdRoot (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (s3 W wq) = 0 := by
  have h2 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  exact MvPowerSeries.constantCoeff_subst_eq_zero h2 (fun i => by fin_cases i <;> simp)
    (PI.AddIntG.Wk.constantCoeff_thirdRoot W wq)

theorem liftedThirdRoot_sub_X (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (i : Fin 2) :
    s3 W wq - MvPowerSeries.X (Fin.castSucc i) = pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p])
      (MvPowerSeries.X 1) (Z3 W wq - MvPowerSeries.X i) := by
  have h2 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  simp only [s3, pr]
  rw [MvPowerSeries.subst_sub h2, MvPowerSeries.subst_X h2]
  fin_cases i <;> rfl

theorem liftedThirdRoot_sub_X_zero_ne_zero (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    s3 W wq - MvPowerSeries.X 0 ≠ 0 := by
  intro h
  apply pairSubst_zero_one_ne_zero (PI.AddIntG.Wk.thirdRoot_sub_var_zero_ne_zero W wq)
  rw [← liftedThirdRoot_sub_X W wq 0]
  exact h

theorem liftedThirdRoot_sub_X_one_ne_zero (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    s3 W wq - MvPowerSeries.X 1 ≠ 0 := by
  intro h
  apply pairSubst_zero_one_ne_zero (PI.AddIntG.Wk.thirdRoot_sub_var_one_ne_zero W wq)
  rw [← liftedThirdRoot_sub_X W wq 1]
  exact h

end PI.FglTriFactor.Wk
