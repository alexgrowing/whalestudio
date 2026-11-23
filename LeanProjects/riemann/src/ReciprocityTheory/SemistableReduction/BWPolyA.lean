import Mathlib

namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem bwp_poly_eq_of_eval_eq_off (P Q : ℂ[X]) (E : Set ℂ) (hE : E.Finite)
    (h : ∀ t ∉ E, P.eval t = Q.eval t) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (fun t ht => h t ht) hE.infinite_compl

theorem bwp_finite_eval_eq_zero {P : ℂ[X]} (hP : P ≠ 0) : {t : ℂ | P.eval t = 0}.Finite := Polynomial.finite_setOf_isRoot hP

theorem bwp_exists_nodes (E : Set ℂ) (hE : E.Finite) (k : ℕ) :
    ∃ S : Finset ℂ, S.card = k + 1 ∧ ∀ c ∈ S, c ∉ E := by
  obtain ⟨S, hS, hcard⟩ := hE.infinite_compl.exists_subset_card_eq (k + 1)
  exact ⟨S, hcard, fun c hc => hS hc⟩

theorem bwp_eval_eq_lagrange (S : Finset ℂ) (Q : ℂ[X]) (k : ℕ) (hS : S.card = k + 1)
    (hQ : Q.natDegree ≤ k) (x : ℂ) :
    Q.eval x = ∑ c ∈ S, (Lagrange.basis S id c).eval x * Q.eval c := by
  have hinj : Set.InjOn id (S : Set ℂ) := Function.injective_id.injOn
  have hdeg : Q.degree < S.card := by
    rw [hS]
    calc Q.degree ≤ (k : WithBot ℕ) := Polynomial.degree_le_of_natDegree_le hQ
      _ < ((k + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self k
  conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp [mul_comm]

theorem bwp_eval_aeval_X {σ : Type*} (L : ℂ[X]) (i : σ) (y : σ → ℂ) :
    MvPolynomial.eval y (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ ℂ) L) = L.eval (y i) := by
  induction L using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

theorem bwp_sepPoly_fin (k : ℕ) : ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ),
    (∀ y m, ∃ Q : ℂ[X], Q.natDegree ≤ k ∧ ∀ t, G (Function.update y m t) = Q.eval t) →
    ∃ F : MvPolynomial (Fin n) ℂ, ∀ y, G y = MvPolynomial.eval y F
  | 0, G, _ => ⟨MvPolynomial.C (G 0), fun y => by
      rw [MvPolynomial.eval_C, Subsingleton.elim y 0]⟩
  | n + 1, G, hG => by
    obtain ⟨S, hS, -⟩ := bwp_exists_nodes ∅ Set.finite_empty k
    have hsub : ∀ c : ℂ, ∃ F : MvPolynomial (Fin n) ℂ,
        ∀ y', G (Fin.cons c y') = MvPolynomial.eval y' F := by
      intro c
      refine bwp_sepPoly_fin k n (fun y' => G (Fin.cons c y')) ?_
      intro y' m
      obtain ⟨Q, hQ, hQt⟩ := hG (Fin.cons c y') m.succ
      exact ⟨Q, hQ, fun t => by simp only [Fin.cons_update]; exact hQt t⟩
    choose Fc hFc using hsub
    refine ⟨∑ c ∈ S, Polynomial.aeval (MvPolynomial.X 0) (Lagrange.basis S id c) *
      MvPolynomial.rename Fin.succ (Fc c), fun y => ?_⟩
    obtain ⟨Q, hQ, hQt⟩ := hG y 0
    have hy : ∀ t, Function.update y 0 t = Fin.cons t (Fin.tail y) := by
      intro t
      conv_lhs => rw [← Fin.cons_self_tail y]
      exact Fin.update_cons_zero _ _ _
    have h1 : G y = Q.eval (y 0) := by
      rw [← hQt]; simp
    rw [h1, bwp_eval_eq_lagrange S Q k hS hQ, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, bwp_eval_aeval_X, MvPolynomial.eval_rename, ← hQt c, hy c, hFc c]
    rfl

theorem bwp_sepPoly {σ : Type*} [Fintype σ] [DecidableEq σ] (k : ℕ) (G : (σ → ℂ) → ℂ)
    (hG : ∀ y m, ∃ Q : ℂ[X], Q.natDegree ≤ k ∧ ∀ t, G (Function.update y m t) = Q.eval t) :
    ∃ F : MvPolynomial σ ℂ, ∀ y, G y = MvPolynomial.eval y F := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  obtain ⟨F, hF⟩ := bwp_sepPoly_fin k (Fintype.card σ) (fun z => G (z ∘ e)) (fun z m => by
    obtain ⟨Q, hQd, hQ⟩ := hG (z ∘ e) (e.symm m)
    refine ⟨Q, hQd, fun t => ?_⟩
    show G ((Function.update z m t) ∘ e) = _
    rw [Function.update_comp_equiv, hQ])
  refine ⟨MvPolynomial.rename e.symm F, fun y => ?_⟩
  rw [MvPolynomial.eval_rename, ← hF]
  congr 1
  ext s
  simp

end ReciprocityTheory.MultiplicativeHeights
