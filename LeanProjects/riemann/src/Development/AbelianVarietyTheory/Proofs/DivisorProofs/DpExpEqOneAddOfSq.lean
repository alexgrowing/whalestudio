import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

set_option autoImplicit false

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer

theorem dpExp_eq_one_add_of_sq {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type}
    [CommRing C] {J : Ideal C} (δ : DividedPowers J) (ρ : Hol W →+* C) {x : C} (hx : x ∈ J)
    (hx2 : x * x = 0) : dpExp δ x = 1 + x := by
  have hv : ∀ n, 2 ≤ n → δ.dpow n x = 0 := by
    intro n hn
    have hu : IsUnit ((n.factorial : ℕ) : C) := by
      have h1 : IsUnit ((n.factorial : ℕ) : Hol W) := by
        rw [← map_natCast (algebraMap ℂ (Hol W))]
        exact (IsUnit.mk0 _ (by exact_mod_cast (Nat.factorial_ne_zero n))).map _
      simpa using h1.map ρ
    have hp : x ^ n = 0 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, sq, hx2, zero_mul]
    have := δ.factorial_mul_dpow_eq_pow hx (n := n)
    rw [hp] at this
    exact (hu.mul_right_eq_zero).1 this
  rw [dpExp_eq_sum_range_of_vanish δ x 2 hv]
  simp [Finset.sum_range_succ, δ.dpow_zero hx, δ.dpow_one hx]

theorem step_exp {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C]
    {J : Ideal C} {ρ ρ' : Hol W →+* C} (s : Step J ρ ρ') (e l : Hol W)
    (he : ∀ a, dw a e = dw a l * e) :
    ρ' l - ρ l ∈ J ∧ (ρ' l - ρ l) * (ρ' l - ρ l) = 0 ∧ ρ' e = ρ e * (1 + (ρ' l - ρ l)) := by
  obtain ⟨n, h1, h2, h3⟩ := s
  have hx : ρ' l - ρ l = ∑ a, ρ (dw a l) * n a := by rw [h3 l]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hx]; exact J.sum_mem fun a _ ↦ J.mul_mem_left _ (h1 a)
  · rw [hx, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
    rw [mul_mul_mul_comm, h2, mul_zero]
  · rw [hx, h3 e, mul_add, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [he, map_mul]; ring

theorem close_exp : ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C]
    (J : Ideal C) (δ : DividedPowers J), IsNilDP δ → ∀ (ρ₁ ρ₂ : Hol W →+* C) (e l : Hol W),
    (∀ a, dw a e = dw a l * e) → Close J ρ₁ ρ₂ → ρ₂ e = ρ₁ e * dpExp δ (ρ₂ l - ρ₁ l) := by
  intro I _ g W C _ J δ hδ ρ₁ ρ₂ e l he hc
  induction hc with
  | refl => rw [sub_self, dpExp_zero, mul_one]
  | @tail ρ ρ' hc' s ih =>
    obtain ⟨hxJ, hx2, hρ'⟩ := step_exp s e l he
    have hyJ : ρ l - ρ₁ l ∈ J := Close.sub_mem hc' l
    rw [show ρ' l - ρ₁ l = (ρ l - ρ₁ l) + (ρ' l - ρ l) by ring,
      hδ.dpExp_add_eq_mul hyJ hxJ, dpExp_eq_one_add_of_sq δ ρ₁ hxJ hx2, hρ', ih, mul_assoc]

end GlobalTheory.AnPer
