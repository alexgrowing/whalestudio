import Mathlib

open Classical

namespace GlobalTheory

theorem classFun_eq_sum_indicator_le (β : Type) (le : β → β → Prop)
    (htr : ∀ x y z, le x y → le y z → le x z)
    (B : Set β) (R : Finset β) (F : β → ℂ) (hRB : (↑R : Set β) ⊆ B)
    (hcov : ∀ x ∈ B, ∃ y ∈ R, le x y ∧ le y x)
    (hF : ∀ x ∈ B, ∀ y ∈ B, le x y → le y x → F x = F y) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (a : Fin m → β), (∀ i, a i ∈ B) ∧
      ∀ x ∈ B, F x = ∑ i, c i * (if le x (a i) then 1 else 0) := by
  induction R using Finset.strongInduction generalizing B with
  | H R ih =>
    rcases R.eq_empty_or_nonempty with hR | hR
    · refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun x hx => ?_⟩
      obtain ⟨y, hy, -⟩ := hcov x hx
      simp [hR] at hy
    obtain ⟨y₀, hy₀, hmin⟩ := R.exists_min_image (fun y => (R.filter (fun z => le z y)).card) hR
    have hy₀B : y₀ ∈ B := hRB hy₀
    have hrefl : le y₀ y₀ := by
      obtain ⟨y, -, h1, h2⟩ := hcov y₀ hy₀B
      exact htr _ _ _ h1 h2
    have hminR : ∀ y ∈ R, le y y₀ → le y₀ y := by
      intro y hy hle
      have hsub : R.filter (fun z => le z y) ⊆ R.filter (fun z => le z y₀) := by
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, htr _ _ _ hz.2 hle⟩
      have heq := Finset.eq_of_subset_of_card_le hsub (hmin y hy)
      have : y₀ ∈ R.filter (fun z => le z y) := by
        rw [heq, Finset.mem_filter]; exact ⟨hy₀, hrefl⟩
      exact (Finset.mem_filter.1 this).2
    have hminB : ∀ x ∈ B, le x y₀ → le y₀ x := by
      intro x hx hle
      obtain ⟨y, hy, h1, h2⟩ := hcov x hx
      exact htr _ _ _ (hminR y hy (htr _ _ _ h2 hle)) h2
    have hss : R.filter (fun z => ¬ le z y₀) ⊂ R := by
      rw [Finset.filter_ssubset]
      exact ⟨y₀, hy₀, not_not.2 hrefl⟩
    obtain ⟨m, c, a, ha, hG⟩ := ih _ hss {x | x ∈ B ∧ ¬ le x y₀}
      (by
        intro z hz
        rw [Finset.mem_coe, Finset.mem_filter] at hz
        exact ⟨hRB hz.1, hz.2⟩)
      (by
        rintro x ⟨hx, hn⟩
        obtain ⟨y, hy, h1, h2⟩ := hcov x hx
        exact ⟨y, Finset.mem_filter.2 ⟨hy, fun h => hn (htr _ _ _ h1 h)⟩, h1, h2⟩)
      (fun x hx y hy => hF x hx.1 y hy.1)
    refine ⟨m + 1,
      Fin.cons (F y₀ - ∑ i, c i * (if le y₀ (a i) then 1 else 0)) c, Fin.cons y₀ a, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hy₀B
      · simpa using (ha j).1
    · intro x hx
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      by_cases hle : le x y₀
      · have hge := hminB x hx hle
        have h1 : ∀ i, le x (a i) ↔ le y₀ (a i) :=
          fun i => ⟨fun h => htr _ _ _ hge h, fun h => htr _ _ _ hle h⟩
        rw [if_pos hle, hF x hx y₀ hy₀B hle hge]
        simp only [h1]
        ring
      · rw [if_neg hle, hG x ⟨hx, hle⟩]
        ring

end GlobalTheory
