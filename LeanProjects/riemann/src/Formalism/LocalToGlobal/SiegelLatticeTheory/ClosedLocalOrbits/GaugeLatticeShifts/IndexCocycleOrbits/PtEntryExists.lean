import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.OrbStabZ

noncomputable section

namespace Formalism.L2.SG.Pf.IndexCocycleOrbits.CU

open Formalism.MainNotions.S Matrix

theorem ptEntry_symm {K : Type*} [Zero K] :
    ∀ (bs : List (K × ℕ)) (i j : ℕ), ptEntry bs i j = ptEntry bs j i
  | [], _, _ => rfl
  | (t, s) :: bs, i, j => by
    simp only [ptEntry]
    rw [ptEntry_symm bs (i - s) (j - s)]
    split_ifs <;> first | rfl | (exfalso; omega)

theorem ptEntry_lt {K : Type*} [Zero K] :
    ∀ (bs : List (K × ℕ)) (i j : ℕ), ptEntry bs i j ≠ 0 → j < (bs.map Prod.snd).sum
  | [], _, _, h => (h rfl).elim
  | (t, s) :: bs, i, j, h => by
    simp only [ptEntry] at h
    simp only [List.map_cons, List.sum_cons]
    split_ifs at h <;> first | exact (h rfl).elim | omega | (have := ptEntry_lt bs _ _ h; omega)

theorem ptEntry_uniq {K : Type*} [Zero K] :
    ∀ (bs : List (K × ℕ)) (i j j' : ℕ), ptEntry bs i j ≠ 0 → ptEntry bs i j' ≠ 0 → j = j'
  | [], _, _, _, h, _ => (h rfl).elim
  | (t, s) :: bs, i, j, j', h, h' => by
    simp only [ptEntry] at h h'
    split_ifs at h h' <;> first | exact (h rfl).elim | exact (h' rfl).elim | omega |
      (have := ptEntry_uniq bs _ _ _ h h'; omega)

theorem ptEntry_exists {K : Type*} [Zero K] :
    ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0) → ∀ i, i < (bs.map Prod.snd).sum → ∃ j, ptEntry bs i j ≠ 0
  | [], _, i, hi => by simp at hi
  | (t, s) :: bs, hb, i, hi => by
    simp only [List.map_cons, List.sum_cons] at hi
    by_cases h1 : i < s
    · refine ⟨s - 1 - i, ?_⟩
      have ht : t ≠ 0 := hb (t, s) (by simp)
      simp only [ptEntry]
      rw [if_pos (by omega), if_pos (by omega)]
      exact ht
    · obtain ⟨j, hj⟩ := ptEntry_exists bs (fun b hb' => hb b (by simp [hb'])) (i - s) (by omega)
      refine ⟨j + s, ?_⟩
      simp only [ptEntry]
      rw [if_neg (by omega), if_pos (by omega)]
      simpa using hj

structure Mono {N : ℕ} {K : Type*} [Zero K] (P : Matrix (Fin N) (Fin N) K) : Prop where
  ex : ∀ i, ∃ j, P i j ≠ 0
  row : ∀ i j j', P i j ≠ 0 → P i j' ≠ 0 → j = j'
  col : ∀ i i' j, P i j ≠ 0 → P i' j ≠ 0 → i = i'

theorem mono_ptMat {K : Type*} [Zero K] {N : ℕ} (p : Point K N) : Mono (ptMat p) where
  ex i := by
    obtain ⟨j, hj⟩ := ptEntry_exists p.1 (fun b hb => (p.2.1 b hb).1) i.val (by rw [p.2.2]; exact i.2)
    have hjN : j < N := by have := ptEntry_lt p.1 _ _ hj; rwa [p.2.2] at this
    exact ⟨⟨j, hjN⟩, hj⟩
  row i j j' h h' := Fin.ext (ptEntry_uniq p.1 i.val _ _ h h')
  col i i' j h h' := by
    apply Fin.ext
    apply ptEntry_uniq p.1 j.val
    · rw [ptEntry_symm]; exact h
    · rw [ptEntry_symm]; exact h'

theorem mono_eq {K : Type*} [Field K] {N : ℕ} {P Q M V : Matrix (Fin N) (Fin N) K}
    (hP : Mono P) (hQ : Mono Q) (hM : IsLoUni M) (hV : IsUpUni V) (h : M * P = Q * V) : P = Q := by
  classical
  choose σ hσ using hP.ex
  choose τ hτ using hQ.ex
  have hPz : ∀ i j, j ≠ σ i → P i j = 0 := fun i j hj => by
    by_contra hne; exact hj (hP.row i j (σ i) hne (hσ i))
  have hQz : ∀ i j, j ≠ τ i → Q i j = 0 := fun i j hj => by
    by_contra hne; exact hj (hQ.row i j (τ i) hne (hτ i))
  have key : ∀ i, P i (σ i) = Q i (τ i) * V (τ i) (σ i) := by
    intro i
    have e := congrFun (congrFun h i) (σ i)
    simp only [Matrix.mul_apply] at e
    rw [Finset.sum_eq_single i, Finset.sum_eq_single (τ i)] at e
    · rw [(hM i i).2 rfl, one_mul] at e; exact e
    · intro k _ hk; rw [hQz i k hk, zero_mul]
    · intro hn; exact absurd (Finset.mem_univ _) hn
    · intro k _ hk
      have : P k (σ i) = 0 := by
        by_contra hne; exact hk (hP.col k i (σ i) hne (hσ i))
      rw [this, mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  have hle : ∀ i, τ i ≤ σ i := by
    intro i
    by_contra hlt
    push Not at hlt
    have := key i
    rw [(hV (τ i) (σ i)).1 hlt, mul_zero] at this
    exact hσ i this
  have hσi : Function.Injective σ := fun a b hab => hP.col a b (σ a) (hσ a) (by rw [hab]; exact hσ b)
  have hτi : Function.Injective τ := fun a b hab => hQ.col a b (τ a) (hτ a) (by rw [hab]; exact hτ b)
  have h1 := Equiv.sum_comp (Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτi)) (fun j : Fin N => (j : ℕ))
  have h2 := Equiv.sum_comp (Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσi)) (fun j : Fin N => (j : ℕ))
  simp only [Equiv.ofBijective_apply] at h1 h2
  have hsum : ∑ i, ((τ i : Fin N) : ℕ) = ∑ i, ((σ i : Fin N) : ℕ) := by rw [h1, h2]
  have heq : ∀ i, τ i = σ i := by
    intro i
    have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => Fin.le_iff_val_le_val.mp (hle i))).1 hsum i
      (Finset.mem_univ _)
    exact Fin.ext this
  ext i j
  by_cases hj : j = σ i
  · subst hj
    rw [key i, heq i, (hV (σ i) (σ i)).2 rfl, mul_one]
  · rw [hPz i j hj, hQz i j (by rw [heq i]; exact hj)]

end Formalism.L2.SG.Pf.IndexCocycleOrbits.CU
