import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.LogInv

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]
variable {σ τ υ : Type*}

theorem rename_subst' (e : σ ↪ τ) {a : υ → MvPowerSeries σ ℂ_[p]} (ha : HasSubst a)
    (f : MvPowerSeries υ ℂ_[p]) :
    rename e (subst a f) = subst (fun s => rename e (a s)) f := by
  rw [rename_eq_subst, subst_comp_subst_apply ha (HasSubst.X_comp e)]
  simp only [rename_eq_subst]

theorem subst_rename' (e : σ ↪ τ) {b : τ → MvPowerSeries υ ℂ_[p]} (hb : HasSubst b)
    (f : MvPowerSeries σ ℂ_[p]) :
    subst b (rename e f) = subst (fun w => b (e w)) f := by
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp e) hb]
  simp only [Function.comp_apply, subst_X hb]

theorem rename_psubst (e : σ ↪ τ) {g : MvPowerSeries σ ℂ_[p]} (hg : PowerSeries.HasSubst g)
    (f : PowerSeries ℂ_[p]) :
    rename e (PowerSeries.subst g f) = PowerSeries.subst (rename e g) f := by
  rw [PowerSeries.subst, rename_subst' e hg.const]
  rfl

theorem rename_phiA [Finite σ] [Finite τ] (e : σ ↪ τ) (c : ℂ_[p]) (w : σ) :
    rename e (phiA p c w) = phiA p c (e w) := by
  rw [phiA, phiA, map_mul, rename_C, rename_psubst e (PowerSeries.HasSubst.X w), rename_X]

theorem phi_rename [Finite σ] [Finite τ] (e : σ ↪ τ) (c : ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]) :
    subst (phiA p c) (rename e f) = rename e (subst (phiA p c) f) := by
  rw [subst_rename' e (hs_phiA p c), rename_subst' e (hs_phiA p c)]
  simp only [rename_phiA]

theorem prod_monomial_one {ι : Type*} (s : Finset ι) (d : ι → τ →₀ ℕ) :
    ∏ i ∈ s, monomial (d i) (1 : ℂ_[p]) = monomial (∑ i ∈ s, d i) 1 := by
  induction s using Finset.induction_on with
  | empty => simp [monomial_zero_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, monomial_mul_monomial, one_mul]

end PI.OrbJet.AO

end
