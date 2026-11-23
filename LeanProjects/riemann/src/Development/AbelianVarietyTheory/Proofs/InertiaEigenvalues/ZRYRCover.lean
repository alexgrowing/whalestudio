import Mathlib

namespace GlobalTheory.HarmLine

def zR (m n p : ℕ) : Fin (min p m) × Fin n → Fin m × Fin n :=
  fun u => (⟨u.1, lt_of_lt_of_le u.1.2 (min_le_right _ _)⟩, u.2)

def yR (m n p : ℕ) : Fin (m - p) × Fin n → Fin m × Fin n :=
  fun u => (⟨m - 1 - u.1, by have := u.1.2; omega⟩, u.2)

theorem zR_inj (m n p : ℕ) : Function.Injective (zR m n p) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [zR, Prod.mk.injEq, Fin.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) h.2

theorem yR_inj (m n p : ℕ) : Function.Injective (yR m n p) := by
  rintro ⟨⟨a, ha⟩, b⟩ ⟨⟨c, hc⟩, d⟩ h
  simp only [yR, Prod.mk.injEq, Fin.mk.injEq] at h
  exact Prod.ext (Fin.ext (by simp only; omega)) h.2

theorem zR_ne_yR (m n p : ℕ) (u : Fin (min p m) × Fin n) (v : Fin (m - p) × Fin n) : zR m n p u ≠ yR m n p v := by
  intro h
  simp only [zR, yR, Prod.mk.injEq, Fin.mk.injEq] at h
  have := u.1.2; have := v.1.2
  have := min_le_left p m
  omega

theorem zR_yR_cover (m n p : ℕ) (s : Fin m × Fin n) : (∃ u, zR m n p u = s) ∨ ∃ v, yR m n p v = s := by
  rcases s with ⟨i, a⟩
  by_cases h : (i : ℕ) < p
  · left
    exact ⟨(⟨i, lt_min h i.2⟩, a), rfl⟩
  · right
    refine ⟨(⟨m - 1 - i, by have := i.2; omega⟩, a), ?_⟩
    simp only [yR, Prod.mk.injEq, and_true]
    ext
    simp only
    have := i.2
    omega

end GlobalTheory.HarmLine
