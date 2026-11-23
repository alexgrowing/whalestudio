import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationAddPowSubLeStatement

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

lemma nnreal_mul_max_le (a b c : ℝ≥0) (hc : c ≤ 1) : c * max a b ≤ max a (c * b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact le_max_right _ _
  · rw [max_eq_left h]; exact (mul_le_of_le_one_left (by positivity) hc).trans (le_max_left _ _)

theorem exists_approxRoot_step : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ (F : Subfield L) (θ : ℝ≥0), θ ≤ 1 → v (p : L) ≤ 1 →
    (∀ u ∈ F, ∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → ∀ α y : L, α ^ p ∈ F → y ∈ F →
    v (α - y) ≤ v α → ∃ y' ∈ F, v (α - y') ^ p ≤
      max (v (p : L) * v (α - y) * v α ^ (p - 1)) (max θ (v (p : L)) * v (α - y) ^ p) := by
  intro L _ v p hp F θ hθ hvp hF α y hα hy hβα
  set β := α - y with hβ
  set A := v (p : L) * v β * v α ^ (p - 1) with hA
  have hyα : v y ≤ v α := by
    have : y = α - β := by rw [hβ]; ring
    rw [this]; exact (Valuation.map_sub v α β).trans (max_le le_rfl hβα)
  have hpp : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  set u := α ^ p - y ^ p with hu
  have huF : u ∈ F := F.sub_mem hα (F.pow_mem hy p)
  have h1 : v (u - β ^ p) ≤ A := by
    have := GlobalTheory.T.valuation_add_pow_sub_pow_sub_pow_le L v p hp y β
    have e : y + β = α := by rw [hβ]; ring
    rw [e] at this
    refine this.trans ?_
    rw [hA]
    gcongr
    exact max_le hyα hβα
  set M := max A (v β ^ p) with hM
  have hvu : v u ≤ M := by
    have : u = (u - β ^ p) + β ^ p := by ring
    rw [this]; refine (Valuation.map_add v _ _).trans ?_
    rw [Valuation.map_pow]; exact max_le_max h1 le_rfl
  obtain ⟨w, hwF, hw⟩ := hF u huF
  have hw' : v (u - w ^ p) ≤ v u := hw.trans (mul_le_of_le_one_left (by positivity) hθ)
  have hwM : v w ^ p ≤ M := by
    have : w ^ p = u - (u - w ^ p) := by ring
    rw [← Valuation.map_pow, this]
    exact ((Valuation.map_sub v _ _).trans (max_le le_rfl hw')).trans hvu
  have h2 : v (β ^ p - w ^ p) ≤ max A (θ * v β ^ p) := by
    have : β ^ p - w ^ p = -(u - β ^ p) + (u - w ^ p) := by ring
    rw [this]; refine (Valuation.map_add v _ _).trans (max_le ?_ ?_)
    · rw [Valuation.map_neg]; exact h1.trans (le_max_left _ _)
    · exact (hw.trans (mul_le_mul_of_nonneg_left hvu (by positivity))).trans (nnreal_mul_max_le _ _ _ hθ)
  refine ⟨y + w, F.add_mem hy hwF, ?_⟩
  set γ := β - w with hγ
  have e2 : α - (y + w) = γ := by rw [hγ, hβ]; ring
  rw [e2]
  set m := max (v w) (v γ) with hm
  have hmβ : m ≤ max (v β) (v w) :=
    max_le (le_max_right _ _) ((Valuation.map_sub v β w))
  have hmM : m ^ p ≤ M := by
    refine (pow_le_pow_left₀ (by positivity) hmβ p).trans ?_
    rcases le_total (v β) (v w) with h | h
    · rw [max_eq_right h]; exact hwM
    · rw [max_eq_left h]; exact le_max_right _ _
  have h3 : v ((w + γ) ^ p - w ^ p - γ ^ p) ≤ max A (v (p : L) * v β ^ p) := by
    refine (GlobalTheory.T.valuation_add_pow_sub_pow_sub_pow_le L v p hp w γ).trans ?_
    have : v (p : L) * v γ * m ^ (p - 1) ≤ v (p : L) * m ^ p := by
      rw [mul_assoc, ← hpp, pow_succ, mul_comm (m ^ (p - 1)) m, hpp]
      gcongr
      exact le_max_right _ _
    refine this.trans ((mul_le_mul_of_nonneg_left hmM (by positivity)).trans (nnreal_mul_max_le _ _ _ hvp))
  have e3 : γ ^ p = (β ^ p - w ^ p) - ((w + γ) ^ p - w ^ p - γ ^ p) := by
    have : w + γ = β := by rw [hγ]; ring
    rw [this]; ring
  rw [← Valuation.map_pow, e3]
  refine (Valuation.map_sub v _ _).trans (max_le (h2.trans ?_) (h3.trans ?_))
  · exact max_le_max le_rfl (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact max_le_max le_rfl (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end GlobalTheory.AlmostEt
