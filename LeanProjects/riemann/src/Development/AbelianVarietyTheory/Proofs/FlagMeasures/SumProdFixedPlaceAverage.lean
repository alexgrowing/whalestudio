import Mathlib

open Finset

namespace GlobalTheory

theorem sum_prod_fixed_place_average {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type}
    [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] {V : Type}
    [AddCommGroup V] [Module ℂ V] (a : ∀ i, G i → ℂ) (f : (∀ i, G i) → V)
    (hf : ∀ i (γ : ∀ i, G i), γ i = 1 → ∑ β : G i, a i β • f (Function.update γ i β) = f γ) :
    ∑ γ : (∀ i, G i), (∏ i, a i (γ i)) • f γ = f 1 := by
  classical
  let c : Finset ι → (∀ i, G i) → ℂ := fun S γ =>
    ∏ i, (if i ∈ S then a i (γ i) else if γ i = 1 then 1 else 0)
  have key : ∀ S : Finset ι, ∑ γ, c S γ • f γ = f 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.sum_eq_single (1 : ∀ i, G i)]
      · simp [c]
      · intro γ _ hγ
        obtain ⟨i, hi⟩ : ∃ i, γ i ≠ 1 := by
          by_contra hcon
          push_neg at hcon
          exact hγ (funext hcon)
        have : c ∅ γ = 0 := Finset.prod_eq_zero (mem_univ i) (by simp [hi])
        rw [this, zero_smul]
      · intro h; exact absurd (mem_univ _) h
    | insert j S hj ih =>
      rw [← ih]
      let h : ∀ i, G i → ℂ := fun i x => if i ∈ S then a i x else if x = 1 then 1 else 0
      have cU : ∀ (γ : ∀ i, G i) (β : G j),
          c S (Function.update γ j β) = h j β * ∏ i ∈ univ.erase j, h i (γ i) := by
        intro γ β
        show ∏ i, h i (Function.update γ j β i) = _
        rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro i hi
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have cI : ∀ γ : ∀ i, G i, c (insert j S) γ = a j (γ j) * ∏ i ∈ univ.erase j, h i (γ i) := by
        intro γ
        show ∏ i, _ = _
        rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro i hi
          have : i ≠ j := Finset.ne_of_mem_erase hi
          simp [h, this]
      have step1 : ∑ γ, c S γ • f γ
          = ∑ γ, ∑ β : G j, (c S γ * a j β) • f (Function.update γ j β) := by
        apply Finset.sum_congr rfl
        intro γ _
        by_cases hγ : γ j = 1
        · rw [← hf j γ hγ, Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro β _
          rw [mul_smul]
        · have : c S γ = 0 := Finset.prod_eq_zero (mem_univ j) (by simp [hj, hγ])
          simp [this]
      let e : (∀ i, G i) × G j ≃ (∀ i, G i) × G j :=
        { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
          invFun := fun p => (Function.update p.1 j p.2, p.1 j)
          left_inv := by intro p; simp
          right_inv := by intro p; simp }
      rw [step1, ← Fintype.sum_prod_type']
      rw [← Fintype.sum_equiv e
        (fun p => (c S (Function.update p.1 j p.2) * a j (p.1 j)) • f p.1) _ (by
          intro p
          simp [e])]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro γ _
      dsimp only
      rw [← Finset.sum_smul, ← Finset.sum_mul]
      simp_rw [cU]
      rw [← Finset.sum_mul, cI]
      have : ∑ β : G j, h j β = 1 := by simp [h, hj]
      rw [this, one_mul, mul_comm]
  have := key univ
  simpa [c] using this

end GlobalTheory
