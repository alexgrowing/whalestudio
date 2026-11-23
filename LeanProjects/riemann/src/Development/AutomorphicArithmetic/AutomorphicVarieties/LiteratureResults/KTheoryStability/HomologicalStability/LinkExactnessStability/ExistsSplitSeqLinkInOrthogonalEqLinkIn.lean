import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx.RowLink

variable {R : Type} [CommRing R] {N : ℕ}

def Orth (y z : (Fin N → R) × (Fin N → R)) : Prop := y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0

theorem mem_splitSeq_iff (l : List ((Fin N → R) × (Fin N → R))) :
    l ∈ splitSeq R N ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧ l.Pairwise Orth := by
  simp only [splitSeq, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, List.pairwise_iff_get.mpr fun i j hij => ⟨?_, ?_⟩⟩
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hy
      simpa using h i i
    · simpa [Fin.ne_of_lt hij] using h i j
    · simpa [(Fin.ne_of_lt hij).symm] using h j i
  · rintro ⟨h1, h2⟩ i j
    have hp := List.pairwise_iff_get.mp h2
    rcases lt_trichotomy i j with hij | rfl | hij
    · simpa [Fin.ne_of_lt hij] using (hp i j hij).1
    · simpa using h1 _ (List.get_mem l i)
    · simpa [(Fin.ne_of_lt hij).symm] using (hp j i hij).2

theorem append_mem_splitSeq_iff (l₁ l₂ : List ((Fin N → R) × (Fin N → R))) :
    l₁ ++ l₂ ∈ splitSeq R N ↔
      l₁ ∈ splitSeq R N ∧ l₂ ∈ splitSeq R N ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, Orth a b := by
  rw [mem_splitSeq_iff, mem_splitSeq_iff, mem_splitSeq_iff, List.pairwise_append]
  constructor
  · rintro ⟨h1, p1, p2, p3⟩
    exact ⟨⟨fun y hy => h1 y (List.mem_append.mpr (Or.inl hy)), p1⟩,
      ⟨fun y hy => h1 y (List.mem_append.mpr (Or.inr hy)), p2⟩, p3⟩
  · rintro ⟨⟨h1, p1⟩, ⟨h2, p2⟩, p3⟩
    exact ⟨fun y hy => (List.mem_append.mp hy).elim (h1 y) (h2 y), p1, p2, p3⟩

def corr (γ : List ((Fin N → R) × (Fin N → R))) (v : Fin N → R) : Fin N → R :=
  v - ∑ i : Fin γ.length, ((γ.get i).2 ⬝ᵥ v) • (γ.get i).1

theorem dot_corr_of_orth (γ : List ((Fin N → R) × (Fin N → R))) (u v : Fin N → R)
    (hu : ∀ z ∈ γ, u ⬝ᵥ z.1 = 0) : u ⬝ᵥ corr γ v = u ⬝ᵥ v := by
  unfold corr
  rw [dotProduct_sub, dotProduct_sum, Finset.sum_eq_zero, sub_zero]
  intro i _
  rw [dotProduct_smul, hu _ (List.get_mem γ i), smul_zero]

theorem form_dot_corr (γ : List ((Fin N → R) × (Fin N → R))) (hγ : γ ∈ splitSeq R N)
    (z : (Fin N → R) × (Fin N → R)) (hz : z ∈ γ) (v : Fin N → R) : z.2 ⬝ᵥ corr γ v = 0 := by
  obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hz
  have h : ∀ i j : Fin γ.length, (γ.get i).2 ⬝ᵥ (γ.get j).1 = if i = j then 1 else 0 := hγ
  unfold corr
  rw [dotProduct_sub, dotProduct_sum]
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin γ.length)),
      (γ.get k).2 ⬝ᵥ (((γ.get i).2 ⬝ᵥ v) • (γ.get i).1) =
        if k = i then (γ.get i).2 ⬝ᵥ v else 0 := by
    intro i _
    rw [dotProduct_smul, h k i, smul_eq_mul]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hs, Finset.sum_ite_eq Finset.univ k, if_pos (Finset.mem_univ _),
    sub_self]

end GlobalTheory.SeqCx.RowLink

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exists_splitSeq_linkIn_orthogonal_eq_linkIn : ∀ (R : Type) [CommRing R] (N : ℕ) (γ σ : List ((Fin N → R) × (Fin N → R))), γ ∈ splitSeq R N → σ ∈ splitSeq R N → (∀ y ∈ σ, ∀ z ∈ γ, y.2 ⬝ᵥ z.1 = 0) → ∃ ρ ∈ splitSeq R N, ρ.length = γ.length + σ.length ∧ linkIn {x | x ∈ splitSeq R N ∧ ∀ y ∈ x, ∀ z ∈ γ, y.2 ⬝ᵥ z.1 = 0} {y | ∀ z ∈ γ, z.2 ⬝ᵥ y.1 = 0} σ = linkIn (splitSeq R N) Set.univ ρ := by
  intro R _ N γ σ hγ hσ hσγ
  obtain ⟨σ', hσ'eq⟩ : ∃ s, s = σ.map (fun y => (GlobalTheory.SeqCx.RowLink.corr γ y.1, y.2)) := ⟨_, rfl⟩
  have hc : ∀ y ∈ σ, ∀ v, y.2 ⬝ᵥ GlobalTheory.SeqCx.RowLink.corr γ v = y.2 ⬝ᵥ v :=
    fun y hy v => GlobalTheory.SeqCx.RowLink.dot_corr_of_orth γ y.2 v (hσγ y hy)
  have hσ's : σ' ∈ splitSeq R N := by
    rw [GlobalTheory.SeqCx.RowLink.mem_splitSeq_iff] at hσ ⊢
    rw [hσ'eq]
    refine ⟨?_, ?_⟩
    · intro y' hy'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hy'
      show y.2 ⬝ᵥ GlobalTheory.SeqCx.RowLink.corr γ y.1 = 1
      rw [hc y hy]
      exact hσ.1 y hy
    · rw [List.pairwise_map]
      refine hσ.2.imp_of_mem ?_
      intro a b ha hb hab
      simp only [GlobalTheory.SeqCx.RowLink.Orth] at hab ⊢
      exact ⟨(hc a ha b.1).trans hab.1, (hc b hb a.1).trans hab.2⟩
  have horth : ∀ a ∈ γ, ∀ b ∈ σ', GlobalTheory.SeqCx.RowLink.Orth a b := by
    intro a ha b hb
    rw [hσ'eq] at hb
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    simp only [GlobalTheory.SeqCx.RowLink.Orth]
    exact ⟨GlobalTheory.SeqCx.RowLink.form_dot_corr γ hγ a ha y.1, hσγ y hy a ha⟩
  have hρ : γ ++ σ' ∈ splitSeq R N :=
    (GlobalTheory.SeqCx.RowLink.append_mem_splitSeq_iff γ σ').mpr ⟨hγ, hσ's, horth⟩
  refine ⟨γ ++ σ', hρ, by rw [List.length_append, hσ'eq, List.length_map], ?_⟩
  ext w
  simp only [linkIn, Set.mem_setOf_eq, Set.mem_univ, implies_true, true_and, List.append_assoc,
    GlobalTheory.SeqCx.RowLink.append_mem_splitSeq_iff, List.mem_append]
  constructor
  · rintro ⟨hS, ⟨-, hw, hσw⟩, hz⟩
    refine ⟨hγ, ⟨hσ's, hw, ?_⟩, ?_⟩
    · intro a ha b hb
      rw [hσ'eq] at ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      have h1 := hσw y hy b hb
      simp only [GlobalTheory.SeqCx.RowLink.Orth] at h1 ⊢
      exact ⟨h1.1, (GlobalTheory.SeqCx.RowLink.dot_corr_of_orth γ b.2 y.1 (hz b (Or.inr hb))).trans h1.2⟩
    · intro a ha b hb
      rcases hb with hb | hb
      · exact horth a ha b hb
      · simp only [GlobalTheory.SeqCx.RowLink.Orth]
        exact ⟨hS b hb a ha, hz b (Or.inr hb) a ha⟩
  · rintro ⟨-, ⟨-, hw, hσ'w⟩, hγx⟩
    refine ⟨fun x hx z hz => And.left (hγx z hz x (Or.inr hx)), ⟨hσ, hw, ?_⟩, ?_⟩
    · intro a ha b hb
      have hbγ : ∀ z ∈ γ, b.2 ⬝ᵥ z.1 = 0 := fun z hz => And.right (hγx z hz b (Or.inr hb))
      have h1 := hσ'w (GlobalTheory.SeqCx.RowLink.corr γ a.1, a.2)
        (by rw [hσ'eq]; exact List.mem_map.mpr ⟨a, ha, rfl⟩) b hb
      simp only [GlobalTheory.SeqCx.RowLink.Orth] at h1 ⊢
      exact ⟨h1.1, (GlobalTheory.SeqCx.RowLink.dot_corr_of_orth γ b.2 a.1 hbγ).symm.trans h1.2⟩
    · intro y hy z hz
      rcases hy with hy | hy
      · exact hσγ y hy z hz
      · exact And.right (hγx z hz y (Or.inr hy))

end
