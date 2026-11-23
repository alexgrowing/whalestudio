import Mathlib

namespace GlobalTheory

theorem closure_cover_meeting_pair (T : Type) [TopologicalSpace T] (S : Set T) (W : Finset T) (e : T → ℚ) (hS : _root_.IsPreconnected S)
    (hsub : ∀ w ∈ W, closure {w} ⊆ S) (hcov : ∀ x ∈ S, ∃ w ∈ W, x ∈ closure {w}) (hnn : ∀ w ∈ W, 0 ≤ e w)
    (h0 : ∃ w ∈ W, e w = 0) (hp : ∃ w ∈ W, 0 < e w) :
      ∃ i ∈ W, ∃ k ∈ W, e i = 0 ∧ 0 < e k ∧ (closure {i} ∩ closure {k}).Nonempty := by
  classical
  set A : Set T := ⋃ w ∈ W.filter (fun w => e w = 0), closure {w} with hA
  set B : Set T := ⋃ w ∈ W.filter (fun w => 0 < e w), closure {w} with hB
  have hAc : IsClosed A := by
    rw [hA]
    exact Set.Finite.isClosed_biUnion (Finset.finite_toSet _) (fun _ _ => isClosed_closure)
  have hBc : IsClosed B := by
    rw [hB]
    exact Set.Finite.isClosed_biUnion (Finset.finite_toSet _) (fun _ _ => isClosed_closure)
  have hSAB : S ⊆ A ∪ B := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := hcov x hx
    rcases (hnn w hw).eq_or_lt with h | h
    · left
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hw, h.symm⟩)) hxw
    · right
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hw, h⟩)) hxw
  have hSA : (S ∩ A).Nonempty := by
    obtain ⟨w, hw, hew⟩ := h0
    exact ⟨w, hsub w hw (subset_closure rfl),
      Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hw, hew⟩)) (subset_closure rfl)⟩
  have hSB : (S ∩ B).Nonempty := by
    obtain ⟨w, hw, hew⟩ := hp
    exact ⟨w, hsub w hw (subset_closure rfl),
      Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hw, hew⟩)) (subset_closure rfl)⟩
  obtain ⟨x, _, hxA, hxB⟩ := isPreconnected_closed_iff.1 hS A B hAc hBc hSAB hSA hSB
  rw [hA, Set.mem_iUnion₂] at hxA
  rw [hB, Set.mem_iUnion₂] at hxB
  obtain ⟨i, hi, hxi⟩ := hxA
  obtain ⟨k, hk, hxk⟩ := hxB
  rw [Finset.mem_filter] at hi hk
  exact ⟨i, hi.1, k, hk.1, hi.2, hk.2, x, hxi, hxk⟩

example : ∀ (T : Type) [TopologicalSpace T] (S : Set T) (W : Finset T) (e : T → ℚ), _root_.IsPreconnected S →
    (∀ w ∈ W, closure {w} ⊆ S) → (∀ x ∈ S, ∃ w ∈ W, x ∈ closure {w}) → (∀ w ∈ W, 0 ≤ e w) →
    (∃ w ∈ W, e w = 0) → (∃ w ∈ W, 0 < e w) →
      ∃ i ∈ W, ∃ k ∈ W, e i = 0 ∧ 0 < e k ∧ (closure {i} ∩ closure {k}).Nonempty :=
  fun T _ S W e => closure_cover_meeting_pair T S W e

end GlobalTheory
