import Mathlib
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.WedgeSplitCasimir

theorem jW_mul_transpose (n m : ℕ) (J J' : Sub n m) (s s' : Fin n) :
    (jW n m * (jW n m)ᵀ) (J, s) (J', s') =
      if s ∉ J.1 ∧ s' ∉ J'.1 ∧ insert s J.1 = insert s' J'.1 then
        (-1) ^ (J.1.filter fun a => a < s).card * (-1) ^ (J'.1.filter fun a => a < s').card else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, jW]
  by_cases hs : s ∈ J.1
  · simp [hs]
  · have hc : (insert s J.1).card = m + 1 := by rw [Finset.card_insert_of_notMem hs, J.2]
    rw [Finset.sum_eq_single (⟨insert s J.1, hc⟩ : Sub n (m + 1))]
    · by_cases h : s' ∉ J'.1 ∧ insert s J.1 = insert s' J'.1
      · rw [if_pos ⟨hs, rfl⟩, if_pos h, if_pos ⟨hs, h⟩]
      · rw [if_neg h, mul_zero, if_neg (fun h' => h h'.2)]
    · intro I _ hI
      rw [if_neg, zero_mul]
      rintro ⟨_, h⟩
      exact hI (Subtype.ext h)
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem anticomm {n : ℕ} (J J' : Finset (Fin n)) (s s' : Fin n) :
    (if s ∈ J' ∧ s' ∉ J'.erase s ∧ J = insert s' (J'.erase s) then
        (-1 : ℂ) ^ ((J'.erase s).filter fun c => c < s').card * (-1) ^ ((J'.erase s).filter fun c => c < s).card
      else 0) =
    (if J = J' ∧ s = s' then 1 else 0) -
      if s ∉ J ∧ s' ∉ J' ∧ insert s J = insert s' J' then
        (-1) ^ (J.filter fun a => a < s).card * (-1) ^ (J'.filter fun a => a < s').card else 0 := by
  have sq : ∀ a : ℕ, (-1 : ℂ) ^ a * (-1) ^ a = 1 := fun a => by
    rw [← mul_pow]; simp
  by_cases hss : s = s'
  · subst hss
    by_cases hs : s ∈ J'
    · rw [Finset.insert_erase hs, sq]
      simp [hs]
    · by_cases hJ : J = J'
      · subst hJ
        simp [hs, sq]
      · rw [if_neg (fun h => hs h.1), if_neg (fun h => hJ h.1), if_neg, sub_zero]
        rintro ⟨h1, h2, h3⟩
        apply hJ
        rw [← Finset.erase_insert h1, h3, Finset.erase_insert h2]
  · rw [if_neg (fun h : J = J' ∧ s = s' => hss h.2), zero_sub]
    by_cases h : s ∈ J' ∧ s' ∉ J'.erase s ∧ J = insert s' (J'.erase s)
    · rw [if_pos h]
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨K, hK, rfl⟩ : ∃ K : Finset (Fin n), s ∉ K ∧ J' = insert s K :=
        ⟨J'.erase s, Finset.notMem_erase _ _, (Finset.insert_erase h1).symm⟩
      rw [Finset.erase_insert hK] at h2 h3 ⊢
      subst h3
      rw [if_pos ⟨by simp [hss, hK], by simp [Ne.symm hss, h2], Finset.insert_comm _ _ _⟩]
      rw [Finset.filter_insert, Finset.filter_insert]
      rcases lt_or_gt_of_ne hss with hlt | hlt
      · rw [if_neg (not_lt.2 hlt.le), if_pos hlt,
          Finset.card_insert_of_notMem (fun h => hK (Finset.mem_filter.1 h).1)]
        ring
      · rw [if_pos hlt, if_neg (not_lt.2 hlt.le),
          Finset.card_insert_of_notMem (fun h => h2 (Finset.mem_filter.1 h).1)]
        ring
    · rw [if_neg h, if_neg, neg_zero]
      rintro ⟨h1, h2, h3⟩
      apply h
      have hs : s ∈ J' := by
        have : s ∈ insert s' J' := h3 ▸ Finset.mem_insert_self s J
        exact (Finset.mem_insert.1 this).resolve_left hss
      refine ⟨hs, fun h => h2 (Finset.mem_of_mem_erase h), ?_⟩
      rw [← Finset.erase_insert h1, h3, Finset.erase_insert_of_ne (Ne.symm hss)]

theorem wedgeQ : StdD → (∀ (k r m : ℕ) (a b : Fin (2 * r + k + 1)) (J J' : Sub (2 * r + k + 1) m), (wedge k r m).dC (Matrix.single a b 1) J J' = if b ∈ J'.1 ∧ a ∉ J'.1.erase b ∧ J.1 = insert a (J'.1.erase b) then (-1) ^ ((J'.1.erase b).filter fun c => c < a).card * (-1) ^ ((J'.1.erase b).filter fun c => c < b).card else 0) → WedgeQ := by
  intro hS hW k r m
  ext ⟨J, s⟩ ⟨J', s'⟩
  have h1 : qMat (wedge k r m) (vr k r false) (J, s) (J', s') =
      (wedge k r m).dC (Matrix.single s' s 1) J J' := by
    simp only [qMat, Matrix.sum_apply, Matrix.kroneckerMap_apply, (hS k r _).1]
    rw [Finset.sum_eq_single s', Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [ha]
    · simp
  rw [h1, hW, Matrix.sub_apply, jW_mul_transpose, anticomm, Matrix.one_apply]
  congr 1
  simp only [Prod.mk.injEq, Subtype.ext_iff]

end GlobalTheory.CompanionTheory.WedgeSplitCasimir
