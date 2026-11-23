import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory

theorem symEdge_span_eq_top : ∀ (k : Type) [Field k] (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → ∀ (a : Fin n → Fin n → k), (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ (V : Submodule k (Fin n → k)), V ≠ ⊥ → (∀ w ∈ V, (fun j => ∑ i, if symEdge ρ κ i j then a i j * w i else 0) ∈ V) → (∀ i j : Fin n, i < j → ¬(ρ ≤ i.val ∧ i.val < ρ + κ ∧ j.val = ρ + κ) → ∀ w ∈ V, Pi.single i (w j) ∈ V) → V = ⊤ := by
  intro k _ n ρ κ hn hρ a ha V hV hT hU
  have hsc : ∀ (i : Fin n) (c : k), c ≠ 0 → Pi.single i c ∈ V → Pi.single i (1 : k) ∈ V := by
    intro i c hc h
    have e : c⁻¹ • Pi.single i c = Pi.single i (1 : k) := by
      ext j; by_cases hj : j = i <;> simp [hj, hc]
    rw [← e]; exact V.smul_mem _ h
  let i0 : Fin n := ⟨0, by omega⟩
  have h0 : Pi.single i0 (1 : k) ∈ V := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    by_cases hex : ∃ j : Fin n, 0 < j.val ∧ w j ≠ 0
    · obtain ⟨j, hj, hwj⟩ := hex
      exact hsc i0 (w j) hwj (hU i0 j (Fin.lt_def.2 hj) (by simp [i0]; omega) w hw)
    · push_neg at hex
      have hwe : w = Pi.single i0 (w i0) := by
        funext j
        by_cases hj : j = i0
        · subst hj; simp
        · have : 0 < j.val := by
            rcases Nat.eq_zero_or_pos j.val with h | h
            · exact absurd (Fin.ext h) hj
            · exact h
          rw [hex j this, Pi.single_eq_of_ne hj]
      have hne : w i0 ≠ 0 := fun h => hw0 (by rw [hwe, h, Pi.single_zero])
      exact hsc i0 _ hne (hwe ▸ hw)
  have hstep : ∀ x y : Fin n, symEdge ρ κ x y → (∀ j : Fin n, symEdge ρ κ x j → j = y) →
      Pi.single x (1 : k) ∈ V → Pi.single y (1 : k) ∈ V := by
    intro x y hxy huniq hx
    refine hsc y (a x y) (ha x y hxy) ?_
    have hu := hT _ hx
    convert hu using 1
    funext j
    rw [Finset.sum_eq_single x]
    · by_cases hj : j = y
      · subst hj; simp [hxy]
      · have : ¬ symEdge ρ κ x j := fun h => hj (huniq j h)
        simp [this, Pi.single_eq_of_ne hj]
    · intro i _ hi; simp [Pi.single_eq_of_ne hi]
    · simp
  have hwalk : ∀ t, t ≤ 2 * ρ → ∀ x : Fin n, x.val = (if t < ρ then t else t + κ) → Pi.single x (1 : k) ∈ V := by
    intro t
    induction t with
    | zero =>
      intro _ x hx
      have : x = i0 := Fin.ext (by simp [i0] at hx ⊢; split_ifs at hx <;> omega)
      rw [this]; exact h0
    | succ t ih =>
      intro ht y hy
      have hxlt : (if t < ρ then t else t + κ) < n := by split_ifs <;> omega
      let x : Fin n := ⟨_, hxlt⟩
      refine hstep x y ?_ ?_ (ih (by omega) x rfl)
      · unfold symEdge
        simp only [x]
        split_ifs at hy ⊢ <;> omega
      · intro j hj
        apply Fin.ext
        unfold symEdge at hj
        simp only [x] at hj
        split_ifs at hy hj <;> omega
  let last : Fin n := ⟨2 * ρ + κ, by omega⟩
  have hlast : Pi.single last (1 : k) ∈ V := hwalk (2 * ρ) le_rfl last (by simp [last]; omega)
  have hall : ∀ i : Fin n, Pi.single i (1 : k) ∈ V := by
    intro i
    by_cases hi : i = last
    · rw [hi]; exact hlast
    · have hlt : i < last := by
        rw [Fin.lt_def]; have := i.2; have : i.val ≠ 2 * ρ + κ := fun h => hi (Fin.ext h); simp [last]; omega
      have := hU i last hlt (by simp [last]; omega) _ hlast
      simpa using this
  rw [eq_top_iff, ← (Pi.basisFun k (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  exact hall i

end GlobalTheory
