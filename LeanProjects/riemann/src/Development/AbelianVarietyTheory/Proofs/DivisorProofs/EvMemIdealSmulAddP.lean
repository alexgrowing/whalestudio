import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem Chart.ev_mem_ideal_smul_add_p (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d) (n : ℕ) (I : Ideal O) (h : MvPowerSeries (Fin d) O) :
    (∀ α, coeff α h ∈ I) → ∃ a ∈ I • (⊤ : Submodule O (G.A n)), ∃ b : G.A n,
      c.ev n h = a + (p : G.A n) * b := by
  intro hI
  classical
  obtain ⟨N, hN⟩ := (c.isEval n).2 1
  let S : Finset (Fin d →₀ ℕ) := Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => N)
  let h₁ : MvPowerSeries (Fin d) O := ∑ α ∈ S, monomial α (coeff α h)
  have hmon : ∀ α, (monomial α (coeff α h) : MvPowerSeries (Fin d) O) =
      coeff α h • monomial α (1 : O) := by
    intro α
    ext β
    simp only [coeff_monomial, coeff_smul]
    split_ifs <;> simp
  have hcoeff : ∀ β ∈ S, coeff β h₁ = coeff β h := by
    intro β hβ
    simp only [h₁, map_sum, coeff_monomial]
    rw [Finset.sum_eq_single_of_mem β hβ]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
  have h₂ : (p : G.A n) ^ 1 ∣ c.ev n (h - h₁) := by
    apply hN
    intro β hβ
    have hmem : β ∈ S := by
      simp only [S, Finset.mem_Iic]
      intro i
      show β i ≤ N
      have : β i ≤ β.degree := by
        by_cases h0 : β i = 0
        · omega
        rw [Finsupp.degree]
        exact Finset.single_le_sum (f := fun j => β j) (fun _ _ => Nat.zero_le _)
          (by simpa using h0)
      omega
    rw [map_sub, hcoeff β hmem, sub_self]
  obtain ⟨b, hb⟩ := h₂
  refine ⟨c.ev n h₁, ?_, b, ?_⟩
  · simp only [h₁, map_sum]
    refine Submodule.sum_mem _ fun α _ => ?_
    rw [hmon, map_smul]
    exact Submodule.smul_mem_smul (hI α) Submodule.mem_top
  · rw [map_sub, pow_one] at hb
    rw [← hb]; ring

end GlobalTheory
