import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPair

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G

section Pos

variable {α : Type*} [BEq α] [LawfulBEq α]

theorem cn_notMem {l1 l2 : List α} (h : (l1 ++ l2).Nodup) {x : α} (hx : x ∈ l2) : x ∉ l1 := by
  intro hx1
  first
  | exact List.disjoint_of_nodup_append h hx1 hx
  | exact (List.nodup_append.1 h).2.2 hx1 hx
  | exact (List.nodup_append.1 h).2.2 x hx1 x hx rfl
  | simp_all [List.nodup_append]

private theorem idxOf_cons_self_eq_zero (a : α) (l : List α) : (a :: l).idxOf a = 0 := by
  first
  | simp [List.idxOf_cons]
  | exact List.idxOf_cons_self l
  | simp [List.idxOf, List.findIdx_cons]

private theorem idxOf_cons_of_ne (a u : α) (h : a ≠ u) (l : List α) : (a :: l).idxOf u = l.idxOf u + 1 := by
  first
  | simp [List.idxOf_cons, h]
  | exact List.idxOf_cons_ne l h
  | simp [List.idxOf, List.findIdx_cons, h]

private theorem idxOf_append_of_not_mem_left (l1 : List α) (u : α) (hu : u ∉ l1) (l : List α) :
    (l1 ++ l).idxOf u = l1.length + l.idxOf u := by
  induction l1 with
  | nil => simp
  | cons a t ih =>
    have hau : a ≠ u := by
      rintro rfl
      simp at hu
    have ht : u ∉ t := fun h' => hu (List.mem_cons_of_mem _ h')
    rw [List.cons_append, idxOf_cons_of_ne a u hau, ih ht, List.length_cons]
    omega

private theorem idxOf_append_of_mem_left_and_lt_length (l1 : List α) (u : α) (hu : u ∈ l1) (l : List α) :
    (l1 ++ l).idxOf u = l1.idxOf u ∧ l1.idxOf u < l1.length := by
  induction l1 with
  | nil => simp at hu
  | cons a t ih =>
    by_cases hau : a = u
    · rw [hau, List.cons_append, idxOf_cons_self_eq_zero, idxOf_cons_self_eq_zero]
      simp
    · have ht : u ∈ t := by simpa [Ne.symm hau] using hu
      obtain ⟨h1, h2⟩ := ih ht
      rw [List.cons_append, idxOf_cons_of_ne a u hau, idxOf_cons_of_ne a u hau, h1, List.length_cons]
      exact ⟨rfl, by omega⟩

theorem cn_pos_swap (l1 l2 : List α) (x y : α) (hxy : x ≠ y) (hx : x ∉ l1) (hy : y ∉ l1) (u : α) :
    (u = x ∧ (l1 ++ x :: y :: l2).idxOf u = l1.length ∧ (l1 ++ y :: x :: l2).idxOf u = l1.length + 1) ∨
    (u = y ∧ (l1 ++ x :: y :: l2).idxOf u = l1.length + 1 ∧ (l1 ++ y :: x :: l2).idxOf u = l1.length) ∨
    (u ≠ x ∧ u ≠ y ∧ (l1 ++ y :: x :: l2).idxOf u = (l1 ++ x :: y :: l2).idxOf u ∧
      ((l1 ++ x :: y :: l2).idxOf u < l1.length ∨ l1.length + 2 ≤ (l1 ++ x :: y :: l2).idxOf u)) := by
  by_cases hux : u = x
  · refine Or.inl ⟨hux, ?_, ?_⟩ <;> rw [hux] <;>
      simp only [idxOf_append_of_not_mem_left l1 x hx, idxOf_cons_self_eq_zero, idxOf_cons_of_ne y x (Ne.symm hxy)] <;> omega
  · by_cases huy : u = y
    · refine Or.inr (Or.inl ⟨huy, ?_, ?_⟩) <;> rw [huy] <;>
        simp only [idxOf_append_of_not_mem_left l1 y hy, idxOf_cons_self_eq_zero, idxOf_cons_of_ne x y hxy] <;> omega
    · refine Or.inr (Or.inr ⟨hux, huy, ?_⟩)
      by_cases hu1 : u ∈ l1
      · obtain ⟨e1, e2⟩ := idxOf_append_of_mem_left_and_lt_length l1 u hu1 (x :: y :: l2)
        obtain ⟨e3, _⟩ := idxOf_append_of_mem_left_and_lt_length l1 u hu1 (y :: x :: l2)
        exact ⟨by rw [e1, e3], Or.inl (by rw [e1]; exact e2)⟩
      · refine ⟨?_, Or.inr ?_⟩ <;>
          simp only [idxOf_append_of_not_mem_left l1 u hu1, idxOf_cons_of_ne x u (Ne.symm hux), idxOf_cons_of_ne y u (Ne.symm huy)] <;> omega

theorem cn_pos_braid (l1 l2 : List α) (x y z : α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ∉ l1) (hy : y ∉ l1) (hz : z ∉ l1) (u : α) :
    (u = x ∧ (l1 ++ x :: y :: z :: l2).idxOf u = l1.length ∧ (l1 ++ z :: y :: x :: l2).idxOf u = l1.length + 2) ∨
    (u = y ∧ (l1 ++ x :: y :: z :: l2).idxOf u = l1.length + 1 ∧
      (l1 ++ z :: y :: x :: l2).idxOf u = l1.length + 1) ∨
    (u = z ∧ (l1 ++ x :: y :: z :: l2).idxOf u = l1.length + 2 ∧ (l1 ++ z :: y :: x :: l2).idxOf u = l1.length) ∨
    (u ≠ x ∧ u ≠ y ∧ u ≠ z ∧ (l1 ++ z :: y :: x :: l2).idxOf u = (l1 ++ x :: y :: z :: l2).idxOf u ∧
      ((l1 ++ x :: y :: z :: l2).idxOf u < l1.length ∨ l1.length + 3 ≤ (l1 ++ x :: y :: z :: l2).idxOf u)) := by
  by_cases hux : u = x
  · refine Or.inl ⟨hux, ?_, ?_⟩ <;> rw [hux] <;>
      simp only [idxOf_append_of_not_mem_left l1 x hx, idxOf_cons_self_eq_zero, idxOf_cons_of_ne y x (Ne.symm hxy), idxOf_cons_of_ne z x (Ne.symm hxz)] <;> omega
  · by_cases huy : u = y
    · refine Or.inr (Or.inl ⟨huy, ?_, ?_⟩) <;> rw [huy] <;>
        simp only [idxOf_append_of_not_mem_left l1 y hy, idxOf_cons_self_eq_zero, idxOf_cons_of_ne x y hxy, idxOf_cons_of_ne z y (Ne.symm hyz)] <;> omega
    · by_cases huz : u = z
      · refine Or.inr (Or.inr (Or.inl ⟨huz, ?_, ?_⟩)) <;> rw [huz] <;>
          simp only [idxOf_append_of_not_mem_left l1 z hz, idxOf_cons_self_eq_zero, idxOf_cons_of_ne x z hxz, idxOf_cons_of_ne y z hyz] <;> omega
      · refine Or.inr (Or.inr (Or.inr ⟨hux, huy, huz, ?_⟩))
        by_cases hu1 : u ∈ l1
        · obtain ⟨e1, e2⟩ := idxOf_append_of_mem_left_and_lt_length l1 u hu1 (x :: y :: z :: l2)
          obtain ⟨e3, _⟩ := idxOf_append_of_mem_left_and_lt_length l1 u hu1 (z :: y :: x :: l2)
          exact ⟨by rw [e1, e3], Or.inl (by rw [e1]; exact e2)⟩
        · refine ⟨?_, Or.inr ?_⟩ <;>
            simp only [idxOf_append_of_not_mem_left l1 u hu1, idxOf_cons_of_ne x u (Ne.symm hux), idxOf_cons_of_ne y u (Ne.symm huy),
              idxOf_cons_of_ne z u (Ne.symm huz)] <;> omega

theorem cn_idx_rev {l : List α} (hnd : l.Nodup) {x : α} (hx : x ∈ l) :
    l.reverse.idxOf x + l.idxOf x + 1 = l.length := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hat, hnd'⟩ := hnd
    rw [List.reverse_cons, List.length_cons]
    by_cases hax : a = x
    · have hat' : x ∉ t := hax ▸ hat
      have hr : x ∉ t.reverse := by simpa using hat'
      rw [hax]
      simp only [idxOf_append_of_not_mem_left t.reverse x hr, idxOf_cons_self_eq_zero, List.length_reverse]
      all_goals omega
    · have hxt : x ∈ t := by simpa [Ne.symm hax] using hx
      have hxr : x ∈ t.reverse := by simpa using hxt
      obtain ⟨e1, _⟩ := idxOf_append_of_mem_left_and_lt_length t.reverse x hxr [a]
      rw [e1, idxOf_cons_of_ne a x hax]
      have := ih hnd' hxt
      omega

theorem cn_decomp (F : α → Prop) (l : List α) :
    (∃ lF lG, l = lF ++ lG ∧ (∀ r ∈ lF, F r) ∧ (∀ r ∈ lG, ¬ F r)) ∨
    (∃ l1 g f lF lG, l = l1 ++ g :: f :: (lF ++ lG) ∧ ¬ F g ∧ F f ∧ (∀ r ∈ lF, F r) ∧ (∀ r ∈ lG, ¬ F r)) := by
  induction l with
  | nil => exact Or.inl ⟨[], [], by simp, by simp, by simp⟩
  | cons a t ih =>
    rcases ih with ⟨lF, lG, rfl, hF, hG⟩ | ⟨l1, g, f, lF, lG, rfl, hg, hf, hF, hG⟩
    · by_cases ha : F a
      · refine Or.inl ⟨a :: lF, lG, by simp, ?_, hG⟩
        intro r hr
        rcases List.mem_cons.1 hr with h | h
        · exact h ▸ ha
        · exact hF r h
      · cases lF with
        | nil =>
          refine Or.inl ⟨[], a :: lG, by simp, by simp, ?_⟩
          intro r hr
          rcases List.mem_cons.1 hr with h | h
          · exact h ▸ ha
          · exact hG r h
        | cons f lF' =>
          exact Or.inr ⟨[], a, f, lF', lG, by simp, ha, hF f (List.mem_cons_self ..),
            fun r hr => hF r (List.mem_cons_of_mem _ hr), hG⟩
    · exact Or.inr ⟨a :: l1, g, f, lF, lG, by simp, hg, hf, hF, hG⟩

end Pos

variable {n : ℕ}

abbrev Steps (n : ℕ) := Relation.ReflTransGen (Step n)

theorem cn_step_tail {l l' : List (Fin n × Fin n)} (h : Step n l l') (R : List (Fin n × Fin n)) :
    Step n (l ++ R) (l' ++ R) := by
  cases h <;>
    (simp only [List.append_assoc, List.cons_append]
     constructor <;> assumption)

theorem cn_steps_tail {l l' : List (Fin n × Fin n)} (h : Steps n l l') (R : List (Fin n × Fin n)) :
    Steps n (l ++ R) (l' ++ R) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (cn_step_tail hs R)

theorem cn_step_rev {l l' : List (Fin n × Fin n)} (h : Step n l l') : Step n l.reverse l'.reverse := by
  cases h with
  | swap l1 l2 a b c d h1 h2 h3 h4 =>
    simpa using Step.swap l2.reverse l1.reverse c d a b h1.symm h3.symm h2.symm h4.symm
  | braid l1 l2 a b c h1 h2 => simpa using Step.braid' l2.reverse l1.reverse a b c h1 h2
  | braid' l1 l2 a b c h1 h2 => simpa using Step.braid l2.reverse l1.reverse a b c h1 h2

theorem cn_steps_rev {l l' : List (Fin n × Fin n)} (h : Steps n l l') : Steps n l.reverse l'.reverse := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (cn_step_rev hs)

end Formalism.MainNotions.G.ExtremalProjector
