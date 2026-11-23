import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.BK GlobalTheory.BKReal
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem N_sub_smul_mem_A {c : K} (hc : ‖c‖ ≤ 1) {g : K⟦X⟧} (hg : g ∈ A O K) :
    N K g - c • g ∈ A O K := fun n => by
  rw [map_sub, coeff_N, coeff_smul, smul_eq_mul, ← sub_mul, norm_mul]
  rw [sub_eq_add_neg]
  refine mul_le_one₀ ?_ (norm_nonneg _) (hg n)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  rw [norm_neg]
  exact
    max_le (IsUltrametricDist.norm_natCast_le_one K n) hc

theorem exists_N_sub_smul_E_pow_mul (l e : ℕ) {c : K} (hc : ‖c‖ ≤ 1) {g : K⟦X⟧} (hg : g ∈ A O K)
    (j : ℕ) : ∃ g' ∈ A O K,
      N K (E K l e ^ j * g) - c • (E K l e ^ j * g) = E K l e ^ (j - 1) * g' := by
  cases j with
  | zero => exact ⟨_, N_sub_smul_mem_A hc hg, by simp⟩
  | succ j =>
    refine ⟨((j + 1 : ℕ) : K⟦X⟧) * ((e : K⟦X⟧) * X ^ e) * g + E K l e * (N K g - c • g),
      (A O K).add_mem ((A O K).mul_mem ((A O K).mul_mem (natCast_mem _ _)
        ((A O K).mul_mem (natCast_mem _ _) ((A O K).pow_mem HasU.X_mem e))) hg)
        ((A O K).mul_mem (E_mem l e _) (N_sub_smul_mem_A hc hg)), ?_⟩
    rw [Derivation.leibniz, Derivation.leibniz_pow, N_E, Nat.add_sub_cancel]
    simp only [smul_eq_mul, nsmul_eq_mul, smul_eq_C_mul]
    push_cast
    ring

theorem exists_aeval_comp_E_pow_mul (l e i : ℕ) : ∀ (m : ℕ) {g : K⟦X⟧}, g ∈ A O K →
    ∃ g' ∈ A O K, Polynomial.aeval (N K).toLinearMap
      ((descPochhammer K i).comp (Polynomial.X - 1)) (E K l e ^ m * g) = E K l e ^ (m - i) * g' := by
  induction i with
  | zero => intro m g hg; exact ⟨g, hg, by simp⟩
  | succ i ih =>
    intro m g hg
    obtain ⟨g₁, hg₁, h₁⟩ := exists_N_sub_smul_E_pow_mul (O := O) l e (c := ((i + 1 : ℕ) : K))
      (IsUltrametricDist.norm_natCast_le_one K _) hg m
    obtain ⟨g₂, hg₂, h₂⟩ := ih (m - 1) hg₁
    refine ⟨g₂, hg₂, ?_⟩
    have h₃ : ∀ x : K⟦X⟧, Polynomial.aeval (N K).toLinearMap
        ((Polynomial.X - (i : Polynomial K)).comp (Polynomial.X - 1)) x = N K x - ((i + 1 : ℕ) : K) • x := by
      intro x
      rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.natCast_comp, map_sub, map_sub,
        Polynomial.aeval_X, map_natCast, map_one, LinearMap.sub_apply, LinearMap.sub_apply,
        Module.End.natCast_apply, Module.End.one_apply, Derivation.coeFn_coe]
      push_cast
      rw [add_smul, one_smul, Nat.cast_smul_eq_nsmul]
      abel
    rw [descPochhammer_succ_right, Polynomial.mul_comp, map_mul (Polynomial.aeval _), Module.End.mul_apply, h₃, h₁, h₂,
      Nat.sub_sub, add_comm 1 i]

theorem exists_l_pow_mul_descN_eq_E_pow_mul : ∀ (l e : ℕ) (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (f h : K⟦X⟧) (k m : ℕ), h ∈ A O K →
    (l : K⟦X⟧) ^ k * N K f = E K l e ^ m * h → ∀ i : ℕ, 1 ≤ i →
    ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i f = E K l e ^ (m + 1 - i) * h' := by
  intro l e O K _ _ _ _ _ f h k m hh hf i hi
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
  obtain ⟨h', hh', h₁⟩ := exists_aeval_comp_E_pow_mul (O := O) l e i m hh
  refine ⟨h', hh', ?_⟩
  have hl : (l : K⟦X⟧) ^ k = C ((l : K) ^ k) := by simp
  rw [Nat.add_sub_add_right, ← h₁, ← hf, descN, descPochhammer_succ_left, mul_comm (Polynomial.X : Polynomial K), map_mul (Polynomial.aeval _),
    Polynomial.aeval_X, Module.End.mul_apply, hl, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]
  rfl

end GlobalTheory.BKReal
