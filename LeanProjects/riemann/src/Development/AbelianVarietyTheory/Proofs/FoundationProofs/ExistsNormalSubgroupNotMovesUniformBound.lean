import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

variable {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]

theorem not_moves_top_iff (v : Valuation L ℝ≥0) (σ : G) :
    ¬ Moves v ⊤ σ ↔ ∃ r : ℝ≥0, r < 1 ∧ ∀ x : L, v x ≤ 1 → v (σ • x - x) ≤ r := by
  unfold Moves
  push_neg
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun x hx => h x (Subfield.mem_top x) hx⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun x _ hx => h x hx⟩

def smallSubgroup (v : Valuation L ℝ≥0) (hv : ∀ (g : G) (x : L), v (g • x) = v x) : Subgroup G where
  carrier := {σ | ¬ Moves v ⊤ σ}
  one_mem' := by
    show ¬ Moves v ⊤ (1 : G)
    rw [not_moves_top_iff]
    exact ⟨0, zero_lt_one, fun x _ => by simp⟩
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Set.mem_setOf_eq, not_moves_top_iff] at hσ hτ ⊢
    obtain ⟨r, hr, h1⟩ := hσ
    obtain ⟨s, hs, h2⟩ := hτ
    refine ⟨max r s, max_lt hr hs, fun x hx => ?_⟩
    have hτx : v (τ • x) ≤ 1 := by rw [hv]; exact hx
    have e : (σ * τ) • x - x = (σ • (τ • x) - τ • x) + (τ • x - x) := by
      rw [mul_smul]; ring
    rw [e]
    exact (v.map_add _ _).trans (max_le_max (h1 _ hτx) (h2 _ hx))
  inv_mem' := by
    intro σ hσ
    simp only [Set.mem_setOf_eq, not_moves_top_iff] at hσ ⊢
    obtain ⟨r, hr, h1⟩ := hσ
    refine ⟨r, hr, fun x hx => ?_⟩
    have hy : v (σ⁻¹ • x) ≤ 1 := by rw [hv]; exact hx
    have e : σ⁻¹ • x - x = -(σ • (σ⁻¹ • x) - σ⁻¹ • x) := by
      rw [smul_inv_smul]; ring
    rw [e, Valuation.map_neg]
    exact h1 _ hy

theorem smallSubgroup_normal (v : Valuation L ℝ≥0) (hv : ∀ (g : G) (x : L), v (g • x) = v x) :
    (smallSubgroup v hv).Normal := by
  constructor
  intro σ hσ g
  change ¬ Moves v ⊤ σ at hσ
  change ¬ Moves v ⊤ (g * σ * g⁻¹)
  rw [not_moves_top_iff] at hσ ⊢
  obtain ⟨r, hr, h1⟩ := hσ
  refine ⟨r, hr, fun x hx => ?_⟩
  have hy : v (g⁻¹ • x) ≤ 1 := by rw [hv]; exact hx
  have e : (g * σ * g⁻¹) • x - x = g • (σ • (g⁻¹ • x) - g⁻¹ • x) := by
    rw [smul_sub, mul_smul, mul_smul, smul_inv_smul]
  rw [e, hv]
  exact h1 _ hy

theorem exists_normal_not_moves_uniform :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L]
      [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) →
      ∃ N : Subgroup G, N.Normal ∧ (∀ σ : G, σ ∈ N ↔ ¬ Moves v ⊤ σ) ∧
        ∃ i : ℝ≥0, i < 1 ∧ ∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i := by
  intro L _ v G _ _ _ hv
  refine ⟨smallSubgroup v hv, smallSubgroup_normal v hv, fun σ => Iff.rfl, ?_⟩
  have hc : ∀ τ : G, ∃ r : ℝ≥0, r < 1 ∧
      (¬ Moves v ⊤ τ → ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ r) := by
    intro τ
    by_cases h : Moves v ⊤ τ
    · exact ⟨0, zero_lt_one, fun h' => absurd h h'⟩
    · obtain ⟨r, hr, h1⟩ := (not_moves_top_iff v τ).1 h
      exact ⟨r, hr, fun _ => h1⟩
  choose f hf1 hf2 using hc
  letI := Fintype.ofFinite G
  refine ⟨Finset.univ.sup f, ?_, ?_⟩
  · rw [Finset.sup_lt_iff zero_lt_one]
    exact fun τ _ => hf1 τ
  · intro τ hτ x hx
    exact (hf2 τ hτ x hx).trans (Finset.le_sup (f := f) (Finset.mem_univ τ))

end GlobalTheory.AlmostEt
