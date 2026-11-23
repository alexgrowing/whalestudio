import Mathlib
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation
open ReciprocityTheory.PGsh

namespace GlobalTheory.ExpWeight

open MvPowerSeries

variable {C : Type} [Field C] {M : ℕ}

def OrdBelow (v : AddValuation C (WithTop ℝ)) (ρ : ℝ) (D : ℕ) (g : MvPowerSeries (Fin M) C)
    (r : ℝ) : Prop :=
  ∀ α : Fin M →₀ ℕ, Finsupp.degree α < D →
    (((r - ρ * (Finsupp.degree α : ℕ) : ℝ)) : WithTop ℝ) ≤ v (coeff α g)

theorem OrdBelow.mul {v : AddValuation C (WithTop ℝ)} {ρ : ℝ} {D : ℕ}
    {g h : MvPowerSeries (Fin M) C} {r s : ℝ} (hg0 : constantCoeff g = 0)
    (hh0 : constantCoeff h = 0) (hg : OrdBelow v ρ D g r) (hh : OrdBelow v ρ D h s) :
    OrdBelow v ρ (D + 1) (g * h) (r + s) := by
  classical
  intro α hα
  rw [coeff_mul]
  refine v.map_le_sum fun p hp => ?_
  have hp' : p.1 + p.2 = α := by simpa using hp
  by_cases h1 : p.1 = 0
  · rw [h1, coeff_zero_eq_constantCoeff_apply, hg0, zero_mul, v.map_zero]; exact le_top
  by_cases h2 : p.2 = 0
  · rw [h2, coeff_zero_eq_constantCoeff_apply, hh0, mul_zero, v.map_zero]; exact le_top
  have hd : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree α := by
    rw [← hp', map_add]
  have d1 : Finsupp.degree p.1 ≠ 0 := fun e => h1 ((Finsupp.degree_eq_zero_iff _).1 e)
  have d2 : Finsupp.degree p.2 ≠ 0 := fun e => h2 ((Finsupp.degree_eq_zero_iff _).1 e)
  rw [v.map_mul]
  refine le_trans (le_of_eq ?_) (add_le_add (hg p.1 (by omega)) (hh p.2 (by omega)))
  rw [← WithTop.coe_add, ← hd]
  congr 1
  push_cast
  ring

theorem OrdBelow.pow_succ {v : AddValuation C (WithTop ℝ)} {ρ : ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : OrdBelow v ρ D g r) (k : ℕ) :
    OrdBelow v ρ D (g ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * r) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    have h := OrdBelow.mul (by simp [hg0]) hg0 ih hg
    intro α hα
    have h' := h α (by omega)
    rw [_root_.pow_succ g (k + 1)]
    refine le_trans (le_of_eq ?_) h'
    congr 1
    push_cast
    ring

theorem OrdBelow.pow {v : AddValuation C (WithTop ℝ)} {ρ : ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : OrdBelow v ρ D g r) {N : ℕ} (hN : 2 ≤ N) :
    OrdBelow v ρ (D + 1) (g ^ N) ((N : ℝ) * r) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  have h := OrdBelow.mul (by simp [hg0]) hg0 (hg.pow_succ hg0 k) hg
  rw [_root_.pow_succ g (k + 1)]
  convert h using 1
  push_cast
  ring

theorem ordGe_of_lgSum_eq_linear :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (d M : ℕ) (al : Fin d → ℕ → Fin d → C) (z : Fin d → Fin M → C) (t : Fin d → MvPowerSeries (Fin M) C),
    (∀ c e, al c 0 e = if c = e then 1 else 0) → (∀ c (n : ℕ) e, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) → (∀ c j, 0 ≤ v (z c j)) →
    (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ e, lgSum l al t e = ∑ j, MvPowerSeries.C (z e j) * MvPowerSeries.X j) →
    ∀ c, OrdGe v (fun _ => 1 / ((l : ℝ) - 1)) (t c) (1 / ((l : ℝ) - 1))) := by
  intro C _ _ v l hl _ d M al z t h0 hal hz ht hlg
  classical
  set ρ : ℝ := 1 / ((l : ℝ) - 1) with hρ
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hρ1 : ρ * ((l : ℝ) - 1) = 1 := by
    rw [hρ]; field_simp [show (l : ℝ) - 1 ≠ 0 by linarith]
  have hρ0 : 0 < ρ := by rw [hρ]; apply one_div_pos.2; linarith
  have key : ∀ D : ℕ, ∀ c, OrdBelow v ρ D (t c) ρ := by
    intro D
    induction D with
    | zero => intro c α hα; omega
    | succ D ih =>
      intro e α hα
      have h1 : coeff α (lgSum l al t e) = coeff α (∑ j, MvPowerSeries.C (z e j) * MvPowerSeries.X j) := by
        rw [hlg e]
      have h2 : coeff α (lgSum l al t e) =
          ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, al a n e * coeff α (t a ^ (l ^ n)) := rfl
      rw [h2, Finset.sum_range_succ'] at h1
      have h3 : ∑ a, al a 0 e * coeff α (t a ^ (l ^ 0)) = coeff α (t e) := by
        simp [h0]
      rw [h3] at h1
      rw [eq_sub_of_add_eq' h1]
      refine v.map_le_sub ?_ ?_
      · rw [map_sum]
        refine v.map_le_sum fun j _ => ?_
        rw [coeff_C_mul, coeff_X]
        split_ifs with hj
        · rw [hj, mul_one]
          simpa using hz e j
        · rw [mul_zero, v.map_zero]; exact le_top
      · refine v.map_le_sum fun n _ => v.map_le_sum fun a _ => ?_
        have hN : 2 ≤ l ^ (n + 1) := le_trans hl.two_le (Nat.le_self_pow (by omega) l)
        have h4 := (ih a).pow (ht a) hN α hα
        rw [v.map_mul]
        refine le_trans ?_ (add_le_add (hal a (n + 1) e) h4)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        have hb := one_add_mul_sub_le_pow (a := (l : ℝ)) (by linarith) (n + 1)
        have hb' := mul_le_mul_of_nonneg_left hb hρ0.le
        push_cast at hb' ⊢
        have : ρ * (1 + ((n : ℝ) + 1) * (l - 1)) = ρ + (n + 1) := by
          linear_combination ((n : ℝ) + 1) * hρ1
        linarith
  intro c α
  have h := key (Finsupp.degree α + 1) c α (by omega)
  refine le_trans (le_of_eq ?_) h
  congr 2
  rw [Finsupp.degree_eq_sum, ← Finset.mul_sum]
  push_cast
  rfl

end GlobalTheory.ExpWeight
