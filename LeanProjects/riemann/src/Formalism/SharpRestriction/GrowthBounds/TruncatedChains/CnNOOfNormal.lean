import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.CnStepsTail

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G

variable {n : ℕ}

def NO (n j : ℕ) (l : List (Fin n × Fin n)) : Prop :=
  l.Nodup ∧ (∀ ab ∈ l, j ≤ ab.1.val ∧ ab.1.val < ab.2.val) ∧
    (∀ a b : Fin n, j ≤ a.val → a.val < b.val → (a, b) ∈ l) ∧
    ∀ a b c : Fin n, j ≤ a.val → a.val < b.val → b.val < c.val →
      (l.idxOf (a, b) < l.idxOf (a, c) ∧ l.idxOf (a, c) < l.idxOf (b, c)) ∨
      (l.idxOf (b, c) < l.idxOf (a, c) ∧ l.idxOf (a, c) < l.idxOf (a, b))

theorem cn_NO_of_normal {ord : List (Fin n × Fin n)} (h : NormalOrder n ord) : NO n 0 ord := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold NO
  exact ⟨h1, fun ab hab => ⟨Nat.zero_le _, h2 ab hab⟩, fun a b _ hab => h3 a b hab,
    fun a b c _ hab hbc => h4 a b c hab hbc⟩

theorem cn_ne {x1 x2 y1 y2 : Fin n} (h : ¬ (x1.val = y1.val ∧ x2.val = y2.val)) : (x1, x2) ≠ (y1, y2) := by
  intro heq
  rw [Prod.mk.injEq] at heq
  exact h ⟨congrArg Fin.val heq.1, congrArg Fin.val heq.2⟩

theorem cn_posR_swap (l1 l2 : List (Fin n × Fin n)) (x1 x2 y1 y2 : Fin n) (hxy : (x1, x2) ≠ (y1, y2))
    (hx : (x1, x2) ∉ l1) (hy : (y1, y2) ∉ l1) (u1 u2 : Fin n) :
    (u1.val = x1.val ∧ u2.val = x2.val ∧ (l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2) = l1.length ∧
      (l1 ++ (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length + 1) ∨
    (u1.val = y1.val ∧ u2.val = y2.val ∧ (l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2) = l1.length + 1 ∧
      (l1 ++ (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length) ∨
    (¬ (u1.val = x1.val ∧ u2.val = x2.val) ∧ ¬ (u1.val = y1.val ∧ u2.val = y2.val) ∧
      (l1 ++ (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = (l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2) ∧
      ((l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2) < l1.length ∨
        l1.length + 2 ≤ (l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2))) := by
  have hu : ∀ v1 v2 : Fin n, u1.val = v1.val ∧ u2.val = v2.val → (u1, u2) = (v1, v2) :=
    fun v1 v2 hh => Prod.ext (Fin.ext hh.1) (Fin.ext hh.2)
  rcases cn_pos_swap l1 l2 (x1, x2) (y1, y2) hxy hx hy (u1, u2) with
    ⟨e, h2, h3⟩ | ⟨e, h2, h3⟩ | ⟨e1, e2, h3, h4⟩
  · rw [Prod.mk.injEq] at e
    exact Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩
  · rw [Prod.mk.injEq] at e
    exact Or.inr (Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩)
  · exact Or.inr (Or.inr ⟨fun hh => e1 (hu _ _ hh), fun hh => e2 (hu _ _ hh), h3, h4⟩)

theorem cn_posR_braid (l1 l2 : List (Fin n × Fin n)) (x1 x2 y1 y2 z1 z2 : Fin n) (hxy : (x1, x2) ≠ (y1, y2))
    (hxz : (x1, x2) ≠ (z1, z2)) (hyz : (y1, y2) ≠ (z1, z2))
    (hx : (x1, x2) ∉ l1) (hy : (y1, y2) ∉ l1) (hz : (z1, z2) ∉ l1) (u1 u2 : Fin n) :
    (u1.val = x1.val ∧ u2.val = x2.val ∧
      (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) = l1.length ∧
      (l1 ++ (z1, z2) :: (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length + 2) ∨
    (u1.val = y1.val ∧ u2.val = y2.val ∧
      (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) = l1.length + 1 ∧
      (l1 ++ (z1, z2) :: (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length + 1) ∨
    (u1.val = z1.val ∧ u2.val = z2.val ∧
      (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) = l1.length + 2 ∧
      (l1 ++ (z1, z2) :: (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length) ∨
    (¬ (u1.val = x1.val ∧ u2.val = x2.val) ∧ ¬ (u1.val = y1.val ∧ u2.val = y2.val) ∧
      ¬ (u1.val = z1.val ∧ u2.val = z2.val) ∧
      (l1 ++ (z1, z2) :: (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) =
        (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) ∧
      ((l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) < l1.length ∨
        l1.length + 3 ≤ (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2))) := by
  have hu : ∀ v1 v2 : Fin n, u1.val = v1.val ∧ u2.val = v2.val → (u1, u2) = (v1, v2) :=
    fun v1 v2 hh => Prod.ext (Fin.ext hh.1) (Fin.ext hh.2)
  rcases cn_pos_braid l1 l2 (x1, x2) (y1, y2) (z1, z2) hxy hxz hyz hx hy hz (u1, u2) with
    ⟨e, h2, h3⟩ | ⟨e, h2, h3⟩ | ⟨e, h2, h3⟩ | ⟨e1, e2, e3, h3, h4⟩
  · rw [Prod.mk.injEq] at e
    exact Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩
  · rw [Prod.mk.injEq] at e
    exact Or.inr (Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩)
  · rw [Prod.mk.injEq] at e
    exact Or.inr (Or.inr (Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨fun hh => e1 (hu _ _ hh), fun hh => e2 (hu _ _ hh),
      fun hh => e3 (hu _ _ hh), h3, h4⟩))

set_option maxHeartbeats 1600000 in
theorem cn_ar_swap {p P Q R P' Q' R' x y z a b c d : ℕ} (hxy : x < y) (hyz : y < z) (h1 : a ≠ c) (h2 : a ≠ d)
    (h3 : b ≠ c) (h4 : b ≠ d) (o : (P < Q ∧ Q < R) ∨ (R < Q ∧ Q < P))
    (p1 : (x = a ∧ y = b ∧ P = p ∧ P' = p + 1) ∨ (x = c ∧ y = d ∧ P = p + 1 ∧ P' = p) ∨
      (¬ (x = a ∧ y = b) ∧ ¬ (x = c ∧ y = d) ∧ P' = P ∧ (P < p ∨ p + 2 ≤ P)))
    (p2 : (x = a ∧ z = b ∧ Q = p ∧ Q' = p + 1) ∨ (x = c ∧ z = d ∧ Q = p + 1 ∧ Q' = p) ∨
      (¬ (x = a ∧ z = b) ∧ ¬ (x = c ∧ z = d) ∧ Q' = Q ∧ (Q < p ∨ p + 2 ≤ Q)))
    (p3 : (y = a ∧ z = b ∧ R = p ∧ R' = p + 1) ∨ (y = c ∧ z = d ∧ R = p + 1 ∧ R' = p) ∨
      (¬ (y = a ∧ z = b) ∧ ¬ (y = c ∧ z = d) ∧ R' = R ∧ (R < p ∨ p + 2 ≤ R))) :
    (P' < Q' ∧ Q' < R') ∨ (R' < Q' ∧ Q' < P') := by
  rcases p1 with h1' | h1' | h1' <;> rcases p2 with h2' | h2' | h2' <;>
    rcases p3 with h3' | h3' | h3' <;> rcases o with o | o <;> omega

set_option maxHeartbeats 3200000 in
theorem cn_ar_braid' {p P Q R P' Q' R' x y z a b c : ℕ} (hxy : x < y) (hyz : y < z) (hab : a < b) (hbc : b < c)
    (o : (P < Q ∧ Q < R) ∨ (R < Q ∧ Q < P))
    (p1 : (x = b ∧ y = c ∧ P = p ∧ P' = p + 2) ∨ (x = a ∧ y = c ∧ P = p + 1 ∧ P' = p + 1) ∨
      (x = a ∧ y = b ∧ P = p + 2 ∧ P' = p) ∨
      (¬ (x = b ∧ y = c) ∧ ¬ (x = a ∧ y = c) ∧ ¬ (x = a ∧ y = b) ∧ P' = P ∧ (P < p ∨ p + 3 ≤ P)))
    (p2 : (x = b ∧ z = c ∧ Q = p ∧ Q' = p + 2) ∨ (x = a ∧ z = c ∧ Q = p + 1 ∧ Q' = p + 1) ∨
      (x = a ∧ z = b ∧ Q = p + 2 ∧ Q' = p) ∨
      (¬ (x = b ∧ z = c) ∧ ¬ (x = a ∧ z = c) ∧ ¬ (x = a ∧ z = b) ∧ Q' = Q ∧ (Q < p ∨ p + 3 ≤ Q)))
    (p3 : (y = b ∧ z = c ∧ R = p ∧ R' = p + 2) ∨ (y = a ∧ z = c ∧ R = p + 1 ∧ R' = p + 1) ∨
      (y = a ∧ z = b ∧ R = p + 2 ∧ R' = p) ∨
      (¬ (y = b ∧ z = c) ∧ ¬ (y = a ∧ z = c) ∧ ¬ (y = a ∧ z = b) ∧ R' = R ∧ (R < p ∨ p + 3 ≤ R))) :
    (P' < Q' ∧ Q' < R') ∨ (R' < Q' ∧ Q' < P') := by
  rcases p1 with h1' | h1' | h1' | h1' <;> rcases p2 with h2' | h2' | h2' | h2' <;>
    rcases p3 with h3' | h3' | h3' | h3' <;> rcases o with o | o <;> omega

theorem cn_NO_swap {j : ℕ} (l1 l2 : List (Fin n × Fin n)) (a b c d : Fin n) (h1 : a ≠ c) (h2 : a ≠ d)
    (h3 : b ≠ c) (h4 : b ≠ d) (h : NO n j (l1 ++ (a, b) :: (c, d) :: l2)) :
    NO n j (l1 ++ (c, d) :: (a, b) :: l2) := by
  unfold NO at h ⊢
  obtain ⟨hnd, hb, hc, ht⟩ := h
  have hperm : (l1 ++ (c, d) :: (a, b) :: l2).Perm (l1 ++ (a, b) :: (c, d) :: l2) :=
    (List.Perm.swap (a, b) (c, d) l2).append_left l1
  have hne : (a, b) ≠ (c, d) := fun e => h1 (congrArg Prod.fst e)
  have hx : (a, b) ∉ l1 := cn_notMem hnd (by simp)
  have hy : (c, d) ∉ l1 := cn_notMem hnd (by simp)
  have v1 : a.val ≠ c.val := fun e => h1 (Fin.ext e)
  have v2 : a.val ≠ d.val := fun e => h2 (Fin.ext e)
  have v3 : b.val ≠ c.val := fun e => h3 (Fin.ext e)
  have v4 : b.val ≠ d.val := fun e => h4 (Fin.ext e)
  refine ⟨hperm.nodup_iff.2 hnd, fun ab hab => hb ab (hperm.mem_iff.1 hab),
    fun x y hj hxy => hperm.mem_iff.2 (hc x y hj hxy), ?_⟩
  intro x y z hj hxy hyz
  exact cn_ar_swap hxy hyz v1 v2 v3 v4 (ht x y z hj hxy hyz)
    (cn_posR_swap l1 l2 a b c d hne hx hy x y) (cn_posR_swap l1 l2 a b c d hne hx hy x z)
    (cn_posR_swap l1 l2 a b c d hne hx hy y z)

theorem cn_NO_braid' {j : ℕ} (l1 l2 : List (Fin n × Fin n)) (a b c : Fin n) (hab : a < b) (hbc : b < c)
    (h : NO n j (l1 ++ (b, c) :: (a, c) :: (a, b) :: l2)) :
    NO n j (l1 ++ (a, b) :: (a, c) :: (b, c) :: l2) := by
  unfold NO at h ⊢
  obtain ⟨hnd, hb, hc, ht⟩ := h
  have hperm : (l1 ++ (a, b) :: (a, c) :: (b, c) :: l2).Perm (l1 ++ (b, c) :: (a, c) :: (a, b) :: l2) :=
    ((((List.Perm.swap (a, c) (a, b) ((b, c) :: l2)).trans
      ((List.Perm.swap (b, c) (a, b) l2).cons (a, c))).trans
      (List.Perm.swap (b, c) (a, c) ((a, b) :: l2)))).append_left l1
  have hab' : a.val < b.val := hab
  have hbc' : b.val < c.val := hbc
  have hxy : ((b, c) : Fin n × Fin n) ≠ (a, c) := fun e => by
    have := congrArg (fun p : Fin n × Fin n => p.1.val) e; simp at this; omega
  have hxz : ((b, c) : Fin n × Fin n) ≠ (a, b) := fun e => by
    have := congrArg (fun p : Fin n × Fin n => p.1.val) e; simp at this; omega
  have hyz : ((a, c) : Fin n × Fin n) ≠ (a, b) := fun e => by
    have := congrArg (fun p : Fin n × Fin n => p.2.val) e; simp at this; omega
  have hx : (b, c) ∉ l1 := cn_notMem hnd (by simp)
  have hy : (a, c) ∉ l1 := cn_notMem hnd (by simp)
  have hz : (a, b) ∉ l1 := cn_notMem hnd (by simp)
  refine ⟨hperm.nodup_iff.2 hnd, fun ab hab => hb ab (hperm.mem_iff.1 hab),
    fun x y hj hxy => hperm.mem_iff.2 (hc x y hj hxy), ?_⟩
  intro x y z hj hxy' hyz'
  exact cn_ar_braid' hxy' hyz' hab' hbc' (ht x y z hj hxy' hyz')
    (cn_posR_braid l1 l2 b c a c a b hxy hxz hyz hx hy hz x y)
    (cn_posR_braid l1 l2 b c a c a b hxy hxz hyz hx hy hz x z)
    (cn_posR_braid l1 l2 b c a c a b hxy hxz hyz hx hy hz y z)

theorem cn_NO_rev {j : ℕ} {l : List (Fin n × Fin n)} (h : NO n j l) : NO n j l.reverse := by
  unfold NO at h ⊢
  obtain ⟨hnd, hb, hc, ht⟩ := h
  refine ⟨List.nodup_reverse.2 hnd, fun ab hab => hb ab (List.mem_reverse.1 hab),
    fun x y hj hxy => List.mem_reverse.2 (hc x y hj hxy), ?_⟩
  intro x y z hj hxy hyz
  have e1 := cn_idx_rev hnd (hc x y hj hxy)
  have e2 := cn_idx_rev hnd (hc x z hj (hxy.trans hyz))
  have e3 := cn_idx_rev hnd (hc y z (hj.trans hxy.le) hyz)
  have o := ht x y z hj hxy hyz
  omega

end Formalism.MainNotions.G.ExtremalProjector
