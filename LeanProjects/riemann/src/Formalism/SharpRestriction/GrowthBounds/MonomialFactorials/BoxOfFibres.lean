import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Comb

variable {s t : ℕ} (u : Fin t → Fin s)

open Classical in

def ovr (a : Fin s → ℕ) (n : Fin t → ℕ) : Fin s → ℕ :=
  fun l => if h : ∃ i, u i = l then n (Classical.choose h) else a l

theorem ovr_u (hu : Function.Injective u) (a : Fin s → ℕ) (n : Fin t → ℕ) (i : Fin t) : ovr u a n (u i) = n i := by
  unfold ovr
  have h : ∃ i', u i' = u i := ⟨i, rfl⟩
  rw [dif_pos h]
  exact congrArg n (hu (Classical.choose_spec h))

theorem ovr_not (a : Fin s → ℕ) (n : Fin t → ℕ) (l : Fin s) (h : ¬ ∃ i, u i = l) : ovr u a n l = a l := dif_neg h

theorem ovr_ovr (hu : Function.Injective u) (a : Fin s → ℕ) (n : Fin t → ℕ) :
    ovr u (ovr u a n) (fun i => a (u i)) = a := by
  funext l
  by_cases h : ∃ i, u i = l
  · obtain ⟨i, rfl⟩ := h
    exact ovr_u u hu _ _ i
  · rw [ovr_not u _ _ l h, ovr_not u _ _ l h]

theorem ovr_mem (hu : Function.Injective u) (W : Fin s → Finset ℕ) (a : Fin s → ℕ) (n : Fin t → ℕ)
    (ha : a ∈ Fintype.piFinset W) (hn : n ∈ Fintype.piFinset (fun i => W (u i))) :
    ovr u a n ∈ Fintype.piFinset W := by
  rw [Fintype.mem_piFinset] at ha hn ⊢
  intro l
  by_cases h : ∃ i, u i = l
  · obtain ⟨i, rfl⟩ := h
    rw [ovr_u u hu]
    exact hn i
  · rw [ovr_not u _ _ _ h]
    exact ha l

theorem ovr_update (hu : Function.Injective u) (a : Fin s → ℕ) (n : Fin t → ℕ) (i : Fin t) (v : ℕ) :
    Function.update (ovr u a n) (u i) v = ovr u a (Function.update n i v) := by
  funext l
  by_cases h : ∃ j, u j = l
  · obtain ⟨j, rfl⟩ := h
    by_cases hj : j = i
    · subst hj
      simp [ovr_u u hu]
    · rw [Function.update_of_ne (hu.ne hj), ovr_u u hu, ovr_u u hu, Function.update_of_ne hj]
  · have hl : l ≠ u i := fun e => h ⟨i, e.symm⟩
    rw [Function.update_of_ne hl, ovr_not u _ _ l h, ovr_not u _ _ l h]

theorem sum_ovr (hu : Function.Injective u) (W : Fin s → Finset ℕ) (F : (Fin s → ℕ) → ℝ) :
    ∑ a ∈ Fintype.piFinset W, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), F (ovr u a n) =
      ((Fintype.piFinset (fun i => W (u i))).card : ℝ) * ∑ a ∈ Fintype.piFinset W, F a := by
  calc ∑ a ∈ Fintype.piFinset W, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), F (ovr u a n)
      = ∑ q ∈ Fintype.piFinset W ×ˢ Fintype.piFinset (fun i => W (u i)), F (ovr u q.1 q.2) := by
        rw [Finset.sum_product]
    _ = ∑ q ∈ Fintype.piFinset W ×ˢ Fintype.piFinset (fun i => W (u i)), F q.1 := by
        refine Finset.sum_nbij' (fun q => (ovr u q.1 q.2, fun i => q.1 (u i)))
          (fun q => (ovr u q.1 q.2, fun i => q.1 (u i))) ?_ ?_ ?_ ?_ ?_
        · rintro ⟨a, n⟩ hq
          rw [Finset.mem_product] at hq ⊢
          refine ⟨ovr_mem u hu W a n hq.1 hq.2, ?_⟩
          have ha := hq.1
          rw [Fintype.mem_piFinset] at ha ⊢
          exact fun i => ha (u i)
        · rintro ⟨a, n⟩ hq
          rw [Finset.mem_product] at hq ⊢
          refine ⟨ovr_mem u hu W a n hq.1 hq.2, ?_⟩
          have ha := hq.1
          rw [Fintype.mem_piFinset] at ha ⊢
          exact fun i => ha (u i)
        · rintro ⟨a, n⟩ _
          exact Prod.ext (ovr_ovr u hu a n) (funext fun i => ovr_u u hu a n i)
        · rintro ⟨a, n⟩ _
          exact Prod.ext (ovr_ovr u hu a n) (funext fun i => ovr_u u hu a n i)
        · rintro ⟨a, n⟩ _
          rfl
    _ = _ := by
        rw [Finset.sum_product, Finset.mul_sum]
        simp [Finset.sum_const, nsmul_eq_mul]

theorem box_of_fibres (hu : Function.Injective u) (W : Fin s → Finset ℕ) (F : (Fin s → ℕ) → ℝ)
    (G : Fin t → (Fin s → ℕ) → ℝ) (ε : ℝ) (hne : (Fintype.piFinset W).Nonempty)
    (h : ∀ a ∈ Fintype.piFinset W, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), F (ovr u a n) ≤
      ε * ∑ i, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), G i (ovr u a n)) :
    ∑ a ∈ Fintype.piFinset W, F a ≤ ε * ∑ i, ∑ a ∈ Fintype.piFinset W, G i a := by
  obtain ⟨a0, ha0⟩ := hne
  have hmem : (fun i => a0 (u i)) ∈ Fintype.piFinset (fun i => W (u i)) := by
    rw [Fintype.mem_piFinset] at ha0 ⊢
    exact fun i => ha0 (u i)
  have hpos : (0 : ℝ) < ((Fintype.piFinset (fun i => W (u i))).card : ℝ) :=
    Nat.cast_pos.2 (Finset.card_pos.2 ⟨_, hmem⟩)
  have hG : ∀ i, ∑ a ∈ Fintype.piFinset W, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), G i (ovr u a n) =
      ((Fintype.piFinset (fun i => W (u i))).card : ℝ) * ∑ a ∈ Fintype.piFinset W, G i a :=
    fun i => sum_ovr u hu W (G i)
  have hsum := Finset.sum_le_sum h
  rw [sum_ovr u hu W F, ← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl fun i _ => hG i,
    ← Finset.mul_sum, mul_left_comm] at hsum
  exact le_of_mul_le_mul_left hsum hpos

theorem interval_eq (A : Finset ℕ) (hne : A.Nonempty) (hc : ∀ x ∈ A, ∀ y ∈ A, ∀ z, x ≤ z → z ≤ y → z ∈ A) :
    A = (Finset.range (A.sup id - sInf (A : Set ℕ) + 1)).image (fun k => sInf (A : Set ℕ) + 1 * k) := by
  have hmA : sInf (A : Set ℕ) ∈ A := Finset.mem_coe.1 (Nat.sInf_mem (Finset.coe_nonempty.2 hne))
  obtain ⟨M, hM, hMe⟩ := Finset.exists_mem_eq_sup A hne id
  have hle : ∀ x ∈ A, sInf (A : Set ℕ) ≤ x := fun x hx => Nat.sInf_le (Finset.mem_coe.2 hx)
  have hge : ∀ x ∈ A, x ≤ A.sup id := fun x hx => show x ≤ A.sup id from Finset.le_sup (f := id) hx
  ext x
  simp only [Finset.mem_image, Finset.mem_range, one_mul]
  constructor
  · intro hx
    have h1 := hle x hx
    have h2 := hge x hx
    exact ⟨x - sInf (A : Set ℕ), by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    refine hc _ hmA M hM _ (Nat.le_add_right _ _) ?_
    have h3 : A.sup id = M := hMe
    have h4 := hle M hM
    omega

end Comb

end Formalism.MainNotions.G.SymmetricFormBlocks

end
