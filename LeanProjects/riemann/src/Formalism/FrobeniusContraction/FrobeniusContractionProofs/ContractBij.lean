import Formalism.FrobeniusContraction.Statement

namespace Formalism.WachCohomologyFacts.PContractBij

variable {R P : Type} [CommRing R] [AddCommGroup P] [Module R P] (I : Ideal R)

theorem pow_smul_top_anti {m n : ℕ} (h : m ≤ n) :
    (I ^ n • ⊤ : Submodule R P) ≤ (I ^ m • ⊤ : Submodule R P) :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

variable {I}

theorem iterate_mem (f : P →+ P)
    (hf : ∀ k : ℕ, ∀ x ∈ (I ^ k • ⊤ : Submodule R P), f x ∈ (I ^ (k + 1) • ⊤ : Submodule R P))
    (y : P) : ∀ r : ℕ, f^[r] y ∈ (I ^ r • ⊤ : Submodule R P)
  | 0 => by simp
  | r + 1 => by
    rw [Function.iterate_succ_apply']
    exact hf r _ (iterate_mem f hf y r)

theorem fixed_mem (f : P →+ P)
    (hf : ∀ k : ℕ, ∀ x ∈ (I ^ k • ⊤ : Submodule R P), f x ∈ (I ^ (k + 1) • ⊤ : Submodule R P))
    (d : P) (hd : f d = d) : ∀ k : ℕ, d ∈ (I ^ k • ⊤ : Submodule R P)
  | 0 => by simp
  | k + 1 => by
    rw [← hd]
    exact hf k _ (fixed_mem f hf d hd k)

theorem telescope (f : P →+ P) (y : P) (n : ℕ) :
    f (-∑ r ∈ Finset.range n, f^[r] y) - (-∑ r ∈ Finset.range n, f^[r] y) = y - f^[n] y := by
  have key := Finset.sum_range_sub (fun r => f^[r] y) n
  rw [Finset.sum_sub_distrib] at key
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] at key
  rw [map_neg, map_sum, neg_sub_neg]
  exact (neg_sub _ _).symm.trans (by rw [key, neg_sub])

end Formalism.WachCohomologyFacts.PContractBij

open Formalism.WachCohomologyFacts.PContractBij in
theorem subIdBijectiveOfContracting_holds : Formalism.WachCohomologyFacts.ContractBij := by
  intro R P _ _ _ I _ f hf
  have haus : ∀ z : P, (∀ n : ℕ, z ∈ (I ^ n • ⊤ : Submodule R P)) → z = 0 := by
    intro z hz
    exact IsHausdorff.haus (I := I) inferInstance z
      (fun n => SModEq.sub_mem.mpr (by rw [sub_zero]; exact hz n))
  constructor
  · intro a b hab
    simp only at hab
    have hfix : f (a - b) = a - b := by
      rw [map_sub]
      exact sub_eq_sub_iff_sub_eq_sub.mp hab
    exact sub_eq_zero.mp (haus _ (Formalism.WachCohomologyFacts.PContractBij.fixed_mem f hf _ hfix))
  · intro y
    let xs : ℕ → P := fun n => -∑ r ∈ Finset.range n, f^[r] y
    have hc : ∀ {m n : ℕ}, m ≤ n → xs m ≡ xs n [SMOD (I ^ m • ⊤ : Submodule R P)] := by
      intro m n hmn
      apply SModEq.sub_mem.mpr
      have hsplit : xs m - xs n = ∑ r ∈ Finset.Ico m n, f^[r] y := by
        simp only [xs]
        rw [neg_sub_neg, ← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
      rw [hsplit]
      refine Submodule.sum_mem _ (fun r hr => ?_)
      exact Formalism.WachCohomologyFacts.PContractBij.pow_smul_top_anti I (Finset.mem_Ico.mp hr).1 (Formalism.WachCohomologyFacts.PContractBij.iterate_mem f hf y r)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (inferInstance : IsPrecomplete I P) hc
    refine ⟨L, ?_⟩
    simp only
    rw [← sub_eq_zero]
    apply haus
    intro n
    have he : L - xs n ∈ (I ^ n • ⊤ : Submodule R P) := by
      rw [← neg_sub]
      exact neg_mem (SModEq.sub_mem.mp (hL n))
    have h1 : f (xs n) - xs n = y - f^[n] y := Formalism.WachCohomologyFacts.PContractBij.telescope f y n
    have h2 : f (xs n) = y - f^[n] y + xs n := by rw [← h1, sub_add_cancel]
    have hz : f L - L - y = f (L - xs n) - (L - xs n) - f^[n] y := by
      rw [map_sub, h2]
      abel
    rw [hz]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ he) (Formalism.WachCohomologyFacts.PContractBij.iterate_mem f hf y n)
    exact Formalism.WachCohomologyFacts.PContractBij.pow_smul_top_anti I (Nat.le_succ n) (hf n _ he)
