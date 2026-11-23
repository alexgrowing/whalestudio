import Mathlib
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
open MvPowerSeries ReciprocityTheory.PGsh

namespace GlobalTheory.LgSubst

theorem coeff_pow_eq_zero_of_degree_lt {M : ℕ} {C : Type} [CommRing C]
    (f : MvPowerSeries (Fin M) C) (hf : constantCoeff f = 0) (m : ℕ) (α : Fin M →₀ ℕ)
    (h : α.degree < m) : coeff α (f ^ m) = 0 := by
  apply coeff_of_lt_order
  have h1 : 1 ≤ f.order := one_le_order_iff_constCoeff_eq_zero.2 hf
  have h2 : (m : ℕ∞) ≤ (f ^ m).order :=
    le_trans (by simpa using nsmul_le_nsmul_right h1 m) (le_order_pow _)
  exact lt_of_lt_of_le (by exact_mod_cast h) h2

theorem coeff_subst_of_pow_support {M : ℕ} {C : Type} [Field C] (p : ℕ) (hp : 2 ≤ p)
    (L : PowerSeries C) (hL : ∀ m, (∀ n, m ≠ p ^ n) → PowerSeries.coeff m L = 0)
    (s : MvPowerSeries (Fin M) C) (hs : constantCoeff s = 0) (α : Fin M →₀ ℕ) :
    coeff α (PowerSeries.subst s L) =
      ∑ n ∈ Finset.range (α.degree + 1), PowerSeries.coeff (p ^ n) L * coeff α (s ^ (p ^ n)) := by
  classical
  have hsub : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have hinj : Function.Injective (fun n : ℕ => p ^ n) := Nat.pow_right_injective hp
  rw [PowerSeries.coeff_subst hsub]
  rw [finsum_eq_sum_of_support_subset (s := (Finset.range (α.degree + 1)).image (fun n => p ^ n))]
  · rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    simp only [smul_eq_mul]
  · intro m hm
    rw [Function.mem_support] at hm
    by_cases hpt : ∃ n, m = p ^ n
    · obtain ⟨n, rfl⟩ := hpt
      rw [Finset.coe_image, Set.mem_image]
      refine ⟨n, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra hn
      apply hm
      have hlt : n < p ^ n := Nat.lt_pow_self (by omega)
      rw [coeff_pow_eq_zero_of_degree_lt s hs _ α (by omega), smul_zero]
    · push_neg at hpt
      exact absurd (by rw [hL m hpt, zero_smul]) hm

theorem subst_sum_lgCurve_eq_lgSum : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → ∀ (d M : ℕ) (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C), (∀ a, G.IsPTypical p (γ a)) → ∀ (t : Fin d → MvPowerSeries (Fin M) C), (∀ a, constantCoeff (t a) = 0) → ∀ e : Fin d, subst t (∑ a, PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) e)) = lgSum p (fun a n => G.lc p (γ a) n) t e := by
  intro C _ _ v p hp d M G γ hγ t ht e
  have hts : HasSubst t := hasSubst_of_constantCoeff_zero ht
  have step : ∀ a, subst t (PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) e))
      = PowerSeries.subst (t a) (G.lgCurve (γ a) e) := by
    intro a
    rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X a).const hts]
    simp only [subst_X hts]
    rfl
  rw [← coe_substAlgHom hts, map_sum]
  simp only [coe_substAlgHom, step]
  ext α
  rw [map_sum]
  simp only [coeff_subst_of_pow_support p hp.two_le _ (fun m hm => hγ _ e m hm) _ (ht _) α]
  rw [Finset.sum_comm]
  rfl

end GlobalTheory.LgSubst
