import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantDominance

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem sum_fin_filter_lt_eq_range {N : ℕ} (G : ℕ → ℕ) (k : ℕ) :
    ∑ a : Fin N with a.val < k, G a.val = ∑ i ∈ Finset.range (min N k), G i := by
  rw [Finset.sum_filter]
  refine (Fin.sum_univ_eq_sum_range (fun i => if i < k then G i else 0) N).trans ?_
  show ∑ i ∈ Finset.range N, (if i < k then G i else 0) = _
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem rowNu_partial_sum {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r) (k : ℕ) :
    (∑ a : Fin r with a.val < k, rowNu (r := r) ν a) = ∑ t : Fin n with t.val < k, ν t := by
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ, G = fun i => if h : i < n then ν ⟨i, h⟩ else 0 := ⟨_, rfl⟩
  have h1 : (∑ a : Fin r with a.val < k, rowNu (r := r) ν a) =
      ∑ a : Fin r with a.val < k, G a.val :=
    Finset.sum_congr rfl fun a _ => by subst hG; rfl
  have h2 : (∑ t : Fin n with t.val < k, ν t) = ∑ t : Fin n with t.val < k, G t.val :=
    Finset.sum_congr rfl fun t _ => by subst hG; simp [t.isLt]
  rw [h1, h2, sum_fin_filter_lt_eq_range, sum_fin_filter_lt_eq_range]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hi'
    simp only [Finset.mem_range] at hi hi'
    have hin : ¬ i < n := by omega
    rw [hG]
    simp [hin]

theorem dualWeylModuleDominanceOfSpan : DualWeylDominanceOf := by
  intro hspan r n ν hnr hν f hf
  rw [hspan r n ν hν] at hf
  have htot : ∑ a : Fin r, rowNu (r := r) ν a = ∑ t : Fin n, ν t := by
    have h := rowNu_partial_sum ν hnr r
    first
      | rwa [Finset.filter_true_of_mem (fun (a : Fin r) _ => a.isLt),
          Finset.filter_true_of_mem (fun (t : Fin n) _ => lt_of_lt_of_le t.isLt hnr)] at h
      | (have e1 : (Finset.univ.filter fun a : Fin r => a.val < r) = Finset.univ := by
            ext a; simp [a.isLt]
         have e2 : (Finset.univ.filter fun t : Fin n => t.val < r) = Finset.univ := by
            ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; omega
         rw [e1, e2] at h
         exact h)
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hg
    intro m hm
    obtain ⟨hpre, htot'⟩ := bideterminantDominance ℤ r n K sz hsz I m hm
    refine ⟨fun k => ?_, ?_⟩
    · rw [rowNu_partial_sum _ hnr k, ← hshape]
      exact hpre k
    · rw [htot, ← hshape]
      exact htot'
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    first
      | exact hx m (MvPolynomial.support_smul hm)
      | (apply hx m
         rw [MvPolynomial.mem_support_iff] at hm ⊢
         intro h0
         apply hm
         simp [h0])

end Formalism.GradedWeylDivisibility
