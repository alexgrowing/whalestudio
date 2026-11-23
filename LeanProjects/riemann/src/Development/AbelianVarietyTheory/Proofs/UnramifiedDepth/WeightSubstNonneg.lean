import Mathlib
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation

open ReciprocityTheory.PGsh

namespace GlobalTheory.WeightSubst

open MvPowerSeries

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type} [Fintype σ]
  [DecidableEq σ] (ρ : σ → ℝ)

def WtNonneg (g : MvPowerSeries σ C) : Prop :=
  ∀ α : σ →₀ ℕ, ((0 - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (coeff α g)

omit [Fintype σ] in
theorem wtNonneg_one : WtNonneg v ρ (1 : MvPowerSeries σ C) := by
  intro α
  rw [coeff_one]
  split_ifs with h
  · subst h
    simp
  · simp

omit [Fintype σ] in
theorem wtNonneg_mul {f g : MvPowerSeries σ C} (hf : WtNonneg v ρ f) (hg : WtNonneg v ρ g) :
    WtNonneg v ρ (f * g) := by
  intro α
  rw [coeff_mul]
  apply AddValuation.map_le_sum
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [AddValuation.map_mul]
  have e : ((0 - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) =
      ((0 - p.1.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) +
        ((0 - p.2.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_add, ← hp, Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring)]
    congr 1
    ring
  rw [e]
  exact add_le_add (hf p.1) (hg p.2)

omit [Fintype σ] in
theorem wtNonneg_prod {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries σ C)
    (h : ∀ i ∈ s, WtNonneg v ρ (f i)) : WtNonneg v ρ (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using wtNonneg_one v ρ
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact wtNonneg_mul v ρ (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

omit [Fintype σ] in
theorem wtNonneg_pow {f : MvPowerSeries σ C} (hf : WtNonneg v ρ f) (n : ℕ) :
    WtNonneg v ρ (f ^ n) := by
  induction n with
  | zero => simpa using wtNonneg_one v ρ
  | succ k ih =>
    rw [pow_succ]
    exact wtNonneg_mul v ρ ih hf

theorem weight_subst_nonneg :
  (∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (σ τ : Type) [Fintype σ] [DecidableEq σ] [Fintype τ] (ρ : σ → ℝ) (K : MvPowerSeries τ C) (t : τ → MvPowerSeries σ C),
    MvIsInt v K → (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ c, (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (t c)))) → (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (MvPowerSeries.subst t K)))) := by
  intro C _ v σ τ _ _ _ ρ K t hK ht0 ht α
  have hs : MvPowerSeries.HasSubst t := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  rw [MvPowerSeries.coeff_subst hs, finsum_eq_sum _ (MvPowerSeries.coeff_subst_finite hs K α)]
  apply AddValuation.map_le_sum
  intro d _
  rw [smul_eq_mul, AddValuation.map_mul]
  have h1 : (0 : WithTop ℝ) ≤ v (MvPowerSeries.coeff d K) := hK d
  have h2 : WtNonneg v ρ (d.prod fun c e => t c ^ e) := by
    unfold Finsupp.prod
    exact wtNonneg_prod v ρ _ _ (fun c _ => wtNonneg_pow v ρ (ht c) _)
  have h3 := add_le_add h1 (h2 α)
  rwa [zero_add] at h3

end GlobalTheory.WeightSubst
