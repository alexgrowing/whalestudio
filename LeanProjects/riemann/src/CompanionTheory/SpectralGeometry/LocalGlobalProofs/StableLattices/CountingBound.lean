import Mathlib
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.ZuckCount

theorem casG_polar {n : ℕ} (μ : Fin n → ℝ) (J : Finset (Fin n)) (s : Fin n) :
    casG (addSet μ J) + casG (μ + Pi.single s 1) + (2 - casG μ) - casG (addSet μ J + Pi.single s 1)
      = if s ∈ J then 0 else 2 := by
  have h : ∑ a, ((addSet μ J a) ^ 2 + ((μ + Pi.single s 1 : Fin n → ℝ) a) ^ 2 - μ a ^ 2
      - ((addSet μ J + Pi.single s 1 : Fin n → ℝ) a) ^ 2) = if s ∈ J then -2 else 0 := by
    rw [Finset.sum_eq_single s]
    · simp only [addSet, Pi.add_apply, Pi.single_eq_same]
      split_ifs <;> ring
    · intro b _ hb
      simp only [addSet, Pi.add_apply, Pi.single_eq_of_ne hb]
      ring
    · simp
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at h
  unfold casG
  split_ifs at h ⊢ <;> linarith

theorem addSet_insert {n : ℕ} (μ : Fin n → ℝ) (J : Finset (Fin n)) (s : Fin n) (hs : s ∉ J) :
    addSet μ J + Pi.single s 1 = addSet μ (insert s J) := by
  funext a
  by_cases ha : a = s
  · subst ha
    simp [addSet, hs]
  · simp [addSet, ha]

theorem addSet_eq_iff {n : ℕ} (μ : Fin n → ℝ) (J I : Finset (Fin n)) (s : Fin n) :
    addSet μ J + Pi.single s 1 = addSet μ I ↔ s ∉ J ∧ I = insert s J := by
  constructor
  · intro h
    have hs : s ∉ J := by
      intro hs
      have := congrFun h s
      simp only [addSet, Pi.add_apply, Pi.single_eq_same, if_pos hs] at this
      split_ifs at this <;> linarith
    refine ⟨hs, ?_⟩
    rw [addSet_insert μ J s hs] at h
    ext a
    have := congrFun h a
    simp only [addSet, add_right_inj] at this
    by_cases h1 : a ∈ I <;> by_cases h2 : a ∈ insert s J <;> simp_all
  · rintro ⟨hs, rfl⟩
    exact addSet_insert μ J s hs

theorem casG_polar_complex {n : ℕ} (μ : Fin n → ℝ) (J : Finset (Fin n)) (s : Fin n) :
    (casG (addSet μ J) : ℂ) + (casG (μ + Pi.single s 1) : ℂ) + (2 - (casG μ : ℂ))
      - (casG (addSet μ J + Pi.single s 1) : ℂ) = if s ∈ J then 0 else 2 := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (casG_polar μ J s)
  split_ifs at h ⊢ <;> (push_cast at h; exact h)

theorem count : Count := by
  intro n m μ _ par w
  have hw : ∀ p, w p (par p) = if p.2 ∈ p.1.1 then 0 else 2 := fun p => casG_polar_complex μ p.1.1 p.2
  refine ⟨fun I => ?_, fun ν hν => ?_⟩
  · have h1 : ∀ p ∈ univ.filter (fun p => par p = addSet μ I.1), w p (addSet μ I.1) = 2 := by
      intro p hp
      have hp' := (Finset.mem_filter.1 hp).2
      rw [← hp', hw, if_neg ((addSet_eq_iff μ p.1.1 I.1 p.2).1 hp').1]
    rw [Finset.sum_congr rfl h1, Finset.sum_const]
    have hc : (univ.filter (fun p => par p = addSet μ I.1)).card = I.1.card := by
      refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
      · intro p hp
        have := (addSet_eq_iff μ p.1.1 I.1 p.2).1 (Finset.mem_filter.1 hp).2
        rw [this.2]; exact Finset.mem_insert_self _ _
      · intro p hp q hq hpq
        have h1 := (addSet_eq_iff μ p.1.1 I.1 p.2).1 (Finset.mem_filter.1 hp).2
        have h2 := (addSet_eq_iff μ q.1.1 I.1 q.2).1 (Finset.mem_filter.1 hq).2
        have hpq' : p.2 = q.2 := hpq
        refine Prod.ext (Subtype.ext ?_) hpq'
        rw [← Finset.erase_insert h1.1, ← Finset.erase_insert h2.1, ← h1.2, ← h2.2, hpq']
      · intro s hs
        refine ⟨(⟨I.1.erase s, ?_⟩, s), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        · rw [Finset.card_erase_of_mem hs, I.2]; rfl
        · exact (addSet_eq_iff μ _ I.1 s).2 ⟨Finset.notMem_erase _ _, (Finset.insert_erase hs).symm⟩
    rw [hc, I.2, nsmul_eq_mul]
    push_cast
    ring
  · refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := (Finset.mem_filter.1 hp).2
    rw [← hp', hw, if_pos]
    by_contra hs
    refine hν ⟨insert p.2 p.1.1, ?_⟩ ?_
    · rw [Finset.card_insert_of_notMem hs, p.1.2]
    · rw [← hp']; exact (addSet_insert μ _ _ hs).symm

end GlobalTheory.CompanionTheory.ZuckCount
