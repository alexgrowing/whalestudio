import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

namespace GlobalTheory.FormalCalc

open MvPowerSeries

variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]

noncomputable def formalExp (f : MvPowerSeries σ A) : MvPowerSeries σ A :=
  (PowerSeries.exp A).subst f

noncomputable def formalLog (g : MvPowerSeries σ A) : MvPowerSeries σ A :=
  (PowerSeries.log A).subst (g - 1)

omit [Algebra ℚ A] in
private theorem hasSubst_sub_one {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    PowerSeries.HasSubst (g - 1) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by simp [hg])

theorem constantCoeff_formalExp {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    constantCoeff (formalExp f) = 1 := by
  have h := constantCoeff_subst_of_zero (σ := Unit) (a := fun _ => f)
    (PowerSeries.HasSubst.of_constantCoeff_zero hf).const (fun _ => hf) (PowerSeries.exp A)
  rw [formalExp, PowerSeries.subst, h, ← PowerSeries.constantCoeff_eq]
  simp

theorem constantCoeff_formalLog {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    constantCoeff (formalLog g) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp [hg]) _ PowerSeries.constantCoeff_log

theorem isUnit_formalExp {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    IsUnit (formalExp f) :=
  isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_formalExp hf]; exact isUnit_one)

theorem pderiv_formalExp {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) (i : σ) :
    pderiv A i (formalExp f) = formalExp f * pderiv A i f := by
  rw [formalExp, pderiv_powerSeries_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    PowerSeries.derivative_exp]

private theorem one_add_X_mul_deriv_log :
    (1 + PowerSeries.X) * PowerSeries.derivative A (PowerSeries.log A) = 1 := by
  rw [PowerSeries.deriv_log]
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero => simp
  | succ n => simp [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, pow_succ]

theorem mul_pderiv_formalLog {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) (i : σ) :
    g * pderiv A i (formalLog g) = pderiv A i g := by
  have hs := hasSubst_sub_one hg
  have h := congrArg (PowerSeries.substAlgHom (R := A) hs) (one_add_X_mul_deriv_log (A := A))
  rw [map_mul, map_add, map_one, PowerSeries.substAlgHom_X, add_sub_cancel,
    PowerSeries.coe_substAlgHom] at h
  rw [formalLog, pderiv_powerSeries_subst hs, ← mul_assoc, h, map_sub, pderiv_one, sub_zero,
    one_mul]

theorem eq_formalExp_of_pderiv {f u : MvPowerSeries σ A} (hf : constantCoeff f = 0)
    (hu : constantCoeff u = 1) (h : ∀ i, pderiv A i u = u * pderiv A i f) :
    u = formalExp f := by
  haveI : IsAddTorsionFree A := .of_module_rat A
  have hn : constantCoeff (-f) = 0 := by simp [hf]
  have key : ∀ v : MvPowerSeries σ A, constantCoeff v = 1 →
      (∀ i, pderiv A i v = v * pderiv A i f) → v * formalExp (-f) = 1 := by
    intro v hv hd
    refine pderiv.ext (fun i => ?_) (by simp [hv, constantCoeff_formalExp hn])
    rw [Derivation.leibniz, pderiv_formalExp hn, hd, map_neg, pderiv_one, smul_eq_mul,
      smul_eq_mul]
    ring
  exact (isUnit_formalExp hn).mul_right_cancel
    ((key u hu h).trans (key _ (constantCoeff_formalExp hf) (pderiv_formalExp hf)).symm)

theorem eq_formalLog_of_pderiv {g u : MvPowerSeries σ A} (hg : constantCoeff g = 1)
    (hu : constantCoeff u = 0) (h : ∀ i, g * pderiv A i u = pderiv A i g) :
    u = formalLog g := by
  haveI : IsAddTorsionFree A := .of_module_rat A
  have hunit : IsUnit g := isUnit_iff_constantCoeff.mpr (hg ▸ isUnit_one)
  refine pderiv.ext (fun i => hunit.mul_left_cancel ?_) (by rw [hu, constantCoeff_formalLog hg])
  rw [h, mul_pderiv_formalLog hg]

@[simp] theorem formalExp_zero : formalExp (0 : MvPowerSeries σ A) = 1 :=
  (eq_formalExp_of_pderiv (by simp) (by simp) fun i => by simp).symm

@[simp] theorem formalLog_one : formalLog (1 : MvPowerSeries σ A) = 0 :=
  (eq_formalLog_of_pderiv (by simp) (by simp) fun i => by simp).symm

theorem formalExp_add {f g : MvPowerSeries σ A} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : formalExp (f + g) = formalExp f * formalExp g := by
  refine (eq_formalExp_of_pderiv (by simp [hf, hg])
    (by simp [constantCoeff_formalExp hf, constantCoeff_formalExp hg]) fun i => ?_).symm
  rw [Derivation.leibniz, pderiv_formalExp hf, pderiv_formalExp hg, map_add, smul_eq_mul,
    smul_eq_mul]
  ring

theorem formalExp_mul_formalExp_neg {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    formalExp f * formalExp (-f) = 1 := by
  rw [← formalExp_add hf (by simp [hf]), add_neg_cancel, formalExp_zero]

theorem formalLog_mul {f g : MvPowerSeries σ A} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) : formalLog (f * g) = formalLog f + formalLog g := by
  refine (eq_formalLog_of_pderiv (by simp [hf, hg])
    (by simp [constantCoeff_formalLog hf, constantCoeff_formalLog hg]) fun i => ?_).symm
  rw [Derivation.leibniz, ← mul_pderiv_formalLog hf, ← mul_pderiv_formalLog hg, map_add,
    smul_eq_mul, smul_eq_mul]
  ring

theorem formalLog_prod {κ : Type*} (s : Finset κ) {g : κ → MvPowerSeries σ A}
    (hg : ∀ k ∈ s, constantCoeff (g k) = 1) :
    formalLog (∏ k ∈ s, g k) = ∑ k ∈ s, formalLog (g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have h' : ∀ j ∈ s, constantCoeff (g j) = 1 := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hk, Finset.prod_insert hk, formalLog_mul
      (hg k (Finset.mem_insert_self _ _)) (by rw [map_prod]; exact Finset.prod_eq_one h'), ih h']

theorem formalLog_pow (n : ℕ) {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    formalLog (g ^ n) = n • formalLog g := by
  simpa using formalLog_prod (Finset.range n) (g := fun _ => g) fun _ _ => hg

theorem subst_formalExp {a : σ → MvPowerSeries τ A} (ha : HasSubst a)
    {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    subst a (formalExp f) = formalExp (subst a f) := by
  rw [formalExp, formalExp, PowerSeries.subst, PowerSeries.subst,
    subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const ha]

theorem subst_formalLog {a : σ → MvPowerSeries τ A} (ha : HasSubst a)
    {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    subst a (formalLog g) = formalLog (subst a g) := by
  rw [formalLog, formalLog, PowerSeries.subst, PowerSeries.subst,
    subst_comp_subst_apply (hasSubst_sub_one hg).const ha, subst_sub ha, subst_one' ha]

theorem map_formalLog (φ : A →+* B) {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    map φ (formalLog g) = formalLog (map φ g) := by
  refine eq_formalLog_of_pderiv (by simp [hg]) (by simp [constantCoeff_formalLog hg]) fun i => ?_
  rw [pderiv_map, pderiv_map, ← map_mul, mul_pderiv_formalLog hg]

end GlobalTheory.FormalCalc
