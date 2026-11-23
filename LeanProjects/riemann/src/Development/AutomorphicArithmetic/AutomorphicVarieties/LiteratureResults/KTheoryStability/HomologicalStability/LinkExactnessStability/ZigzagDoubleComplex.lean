import Mathlib
open Function

namespace GlobalTheory

theorem zigzag_double_complex : ∀ (A : Type) [AddCommGroup A] (C : ℕ → ℕ → Submodule ℤ A) (h v : A →ₗ[ℤ] A) (p : ℕ), (∀ x, h (h x) = 0) → (∀ x, h (v x) = v (h x)) → (∀ a b, ∀ x ∈ C (a + 1) b, h x ∈ C a b) → (∀ a b, ∀ x ∈ C a (b + 1), v x ∈ C a b) → (∀ b, ∀ x ∈ C 0 b, h x = 0) → (∀ a b, a + b = p → ∀ x ∈ C a b, v x = 0 → ∃ y ∈ C a (b + 1), v y = x) → (∀ a b, a + b = p + 1 → 2 ≤ b → ∀ x ∈ C a b, h x = 0 → ∃ y ∈ C (a + 1) b, h y = x) → (∀ x, v (v x) = 0) → ∀ c ∈ C p 0, h c = 0 → v c = 0 → ∃ z ∈ C p 1, h z = 0 ∧ v z = c := by
  intro A _ C h v p hh hhv hC1 hC2 h0 hv hH hvv
  have key : ∀ a b, a + b = p → ∀ c ∈ C a b, h c = 0 → v c = 0 →
      ∃ z ∈ C a (b + 1), h z = 0 ∧ v z = c := by
    intro a
    induction a with
    | zero =>
      intro b hab c hc _ hvc
      obtain ⟨y, hy, hyc⟩ := hv 0 b hab c hc hvc
      exact ⟨y, hy, h0 (b + 1) y hy, hyc⟩
    | succ a ih =>
      intro b hab c hc hhc hvc
      obtain ⟨y, hy, hyc⟩ := hv (a + 1) b hab c hc hvc
      have hy1 : h y ∈ C a (b + 1) := hC1 a (b + 1) y hy
      have hab' : a + (b + 1) = p := by omega
      have hvhy : v (h y) = 0 := by rw [← hhv y, hyc, hhc]
      obtain ⟨z', hz', hhz', hvz'⟩ := ih (b + 1) hab' (h y) hy1 (hh y) hvhy
      obtain ⟨u, hu, hu'⟩ := hH a (b + 1 + 1) (by omega) (by omega) z' hz' hhz'
      refine ⟨y - v u, Submodule.sub_mem _ hy (hC2 (a + 1) (b + 1) u hu), ?_, ?_⟩
      · rw [map_sub, hhv u, hu', hvz', sub_self]
      · rw [map_sub, hvv u, sub_zero, hyc]
  intro c hc hhc hvc
  exact key p 0 (by simp) c hc hhc hvc

end GlobalTheory
