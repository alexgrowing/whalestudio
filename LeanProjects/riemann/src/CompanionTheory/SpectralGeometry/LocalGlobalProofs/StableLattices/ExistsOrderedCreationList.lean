import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgClusterOrder

def rootHt {n : ℕ} (i : Pos n) : ℕ := (i.1.2 : ℕ) - (i.1.1 : ℕ)

theorem exists_sorted_list {α : Type} (S : Finset α) (h : α → ℕ) :
    ∃ l : List α, l.Nodup ∧ (∀ i, i ∈ l ↔ i ∈ S) ∧ l.Pairwise (fun a b => h a ≤ h b) := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], List.nodup_nil, by simp, List.Pairwise.nil⟩
    · obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image S h hne
      obtain ⟨l, hnd, hmem, hs⟩ := ih (S.erase m) (Finset.erase_ssubset hm)
      refine ⟨m :: l, ?_, ?_, ?_⟩
      · refine List.nodup_cons.2 ⟨?_, hnd⟩
        intro hml
        exact (Finset.mem_erase.1 ((hmem m).1 hml)).1 rfl
      · intro i
        rw [List.mem_cons, hmem, Finset.mem_erase]
        constructor
        · rintro (rfl | hi)
          · exact hm
          · exact hi.2
        · intro hi
          by_cases him : i = m
          · exact Or.inl him
          · exact Or.inr ⟨him, hi⟩
      · refine List.pairwise_cons.2 ⟨?_, hs⟩
        intro b hb
        exact hmin b (Finset.mem_of_mem_erase ((hmem b).1 hb))

theorem adC_ne_zero_cases {n : ℕ} {p q : Fin n} {i k : Pos n} (h : adC p q i k ≠ 0) :
    (q = i.1.1 ∧ k.1 = (p, i.1.2)) ∨ (i.1.2 = p ∧ k.1 = (i.1.1, q)) := by
  by_contra hc
  rw [not_or] at hc
  exact h (by simp only [adC, if_neg hc.1, if_neg hc.2, sub_self])

theorem mem_inside_iff {n : ℕ} {ε : Fin n → Bool} {lev : Fin n → ℕ} (hlev : Monotone lev) (i : Pos n) :
    i ∈ om ε ∧ i ∉ omU ε lev ↔ ε i.1.1 = ε i.1.2 ∧ lev i.1.1 = lev i.1.2 := by
  have hle : lev i.1.1 ≤ lev i.1.2 := hlev (le_of_lt i.2)
  simp only [CompanionTheory.D.LK.om, omU, Finset.mem_filter, Finset.mem_univ, true_and, cpt, not_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, le_antisymm hle (not_lt.1 (h2 h1))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun _ => by omega⟩

theorem exists_inside_order : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ), Monotone lev →
    ∃ l : List (Pos n), l.Nodup ∧ (∀ i, i ∈ l ↔ i ∈ om ε ∧ i ∉ omU ε lev) ∧
      ∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
        adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post := by
  intro n ε lev hlev
  classical
  obtain ⟨l, hnd, hmem, hs⟩ := exists_sorted_list ((om ε).filter (· ∉ omU ε lev)) (rootHt (n := n))
  have hmem' : ∀ i, i ∈ l ↔ i ∈ om ε ∧ i ∉ omU ε lev := fun i => by
    rw [hmem, Finset.mem_filter]
  refine ⟨l, hnd, hmem', ?_⟩
  intro pre f post hl e he k hk
  have hfl : f ∈ l := by simp [hl]
  obtain ⟨he1, he2⟩ := (mem_inside_iff hlev e).1 ((hmem' e).1 he)
  obtain ⟨hf1, hf2⟩ := (mem_inside_iff hlev f).1 ((hmem' f).1 hfl)
  have he0 : (e.1.1 : ℕ) < e.1.2 := e.2
  have hf0 : (f.1.1 : ℕ) < f.1.2 := f.2

  have hkey : (ε k.1.1 = ε k.1.2 ∧ lev k.1.1 = lev k.1.2) ∧ rootHt f < rootHt k := by
    rcases adC_ne_zero_cases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [← h1] at hf1 hf2 ⊢
        exact he1.trans hf1
      · simp only [← h1] at hf1 hf2 ⊢
        exact he2.trans hf2
      · have : (e.1.2 : ℕ) = f.1.1 := congrArg Fin.val h1
        simp only [rootHt, h2]
        omega
    · rw [h2]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [h1] at hf1 hf2 ⊢
        exact hf1.trans he1
      · simp only [h1] at hf1 hf2 ⊢
        exact hf2.trans he2
      · have : (f.1.2 : ℕ) = e.1.1 := congrArg Fin.val h1
        simp only [rootHt, h2]
        omega
  have hkl : k ∈ l := (hmem' k).2 ((mem_inside_iff hlev k).2 hkey.1)
  rw [hl] at hkl hs
  rcases List.mem_append.1 hkl with hpre | hrest
  · have := (List.pairwise_append.1 hs).2.2 k hpre f (by simp)
    omega
  · rcases List.mem_cons.1 hrest with rfl | hpost
    · exact absurd hkey.2 (lt_irrefl _)
    · exact hpost

end GlobalTheory.CompanionTheory.RgClusterOrder
