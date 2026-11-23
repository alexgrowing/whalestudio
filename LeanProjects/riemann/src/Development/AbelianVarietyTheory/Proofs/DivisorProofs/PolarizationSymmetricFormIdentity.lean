import Mathlib
open MvPolynomial

namespace GlobalTheory

theorem linear_coeff_compare {V J : Type} [AddCommGroup V] [Module ℝ V] (e : ℕ)
    (Ψ : MvPolynomial J ℝ →ₗ[ℝ] ℝ) (x ℓ : MvPolynomial J ℝ)
    (num : MultilinearMap ℝ (fun _ : Fin (e + 1) => V) ℝ)
    (hsym : ∀ (v : Fin (e + 1) → V) (ρ : Equiv.Perm (Fin (e + 1))), num (v ∘ ρ) = num v)
    (ν : ℝ) (w a : V)
    (h : ∀ t : ℤ, Ψ ((MvPolynomial.C (t : ℝ) * x + ℓ) ^ (e + 1)) = ν * num (fun _ => w + (t : ℝ) • a)) :
    Ψ (x * ℓ ^ e) = ν * num (Fin.cons a fun _ => w) := by
  classical
  let P : Polynomial ℝ := ∑ k ∈ Finset.range (e + 1 + 1),
    Polynomial.C (((e + 1).choose k : ℝ) * Ψ (x ^ k * ℓ ^ (e + 1 - k))) * Polynomial.X ^ k
  let Q : Polynomial ℝ := ∑ s : Finset (Fin (e + 1)),
    Polynomial.C (ν * num (s.piecewise (fun _ => a) (fun _ => w))) * Polynomial.X ^ s.card
  have hP : ∀ t : ℝ, P.eval t = Ψ ((MvPolynomial.C t * x + ℓ) ^ (e + 1)) := by
    intro t
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [add_pow, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (MvPolynomial.C t * x) ^ k * ℓ ^ (e + 1 - k) * (((e + 1).choose k : ℕ) : MvPolynomial J ℝ)
        = (t ^ k * ((e + 1).choose k : ℝ)) • (x ^ k * ℓ ^ (e + 1 - k)) := by
      rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul, MvPolynomial.C_pow, mul_pow]
      rw [show (((e + 1).choose k : ℕ) : MvPolynomial J ℝ) = MvPolynomial.C (((e + 1).choose k : ℕ) : ℝ) from
        (map_natCast _ _).symm]
      ring
    rw [this, map_smul, smul_eq_mul]
    ring
  have hQ : ∀ t : ℝ, Q.eval t = ν * num (fun _ => w + t • a) := by
    intro t
    simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [show (fun _ : Fin (e + 1) => w + t • a) = (fun _ => t • a) + (fun _ => w) from by
      funext i; simp [add_comm], num.map_add_univ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have : s.piecewise (fun _ => t • a) (fun _ => w)
        = s.piecewise (fun i => t • (s.piecewise (fun _ => a) (fun _ => w)) i)
            (s.piecewise (fun _ => a) (fun _ => w)) := by
      funext i; by_cases hi : i ∈ s <;> simp [hi]
    rw [this, num.map_piecewise_smul, Finset.prod_const, smul_eq_mul]
    ring
  have hPQ : P = Q := by
    refine Polynomial.eq_of_infinite_eval_eq P Q
      (Set.infinite_of_injective_forall_mem (f := fun t : ℤ => (t : ℝ)) Int.cast_injective ?_)
    intro t
    simp only [Set.mem_ofPred_eq]
    rw [hP, hQ, h t]
  have hc : ∀ k : Fin (e + 1), k ≠ 0 → (Fin.cons a (fun _ => w) : Fin (e + 1) → V) k = w := by
    intro k hk
    obtain ⟨k', rfl⟩ := Fin.exists_succ_eq.mpr hk
    simp
  have hsingle : ∀ i : Fin (e + 1),
      num (({i} : Finset (Fin (e + 1))).piecewise (fun _ => a) (fun _ => w))
        = num (Fin.cons a fun _ => w) := by
    intro i
    rw [← hsym (Fin.cons a fun _ => w) (Equiv.swap 0 i)]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Finset.piecewise_eq_of_notMem _ _ _ (by simpa using hj)]
      simp only [Function.comp_apply]
      rw [hc]
      rw [Equiv.swap_apply_def]
      split_ifs with h0 <;> [exact fun h' => hj (h0.trans h'.symm); assumption]
  have h1 := congrArg (fun p => p.coeff 1) hPQ
  simp only [P, Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at h1
  rw [Finset.sum_ite_eq] at h1
  rw [← Finset.sum_filter, ← Finset.powerset_univ] at h1
  simp only [@eq_comm ℕ 1 (Finset.card _)] at h1
  rw [← Finset.powersetCard_eq_filter, Finset.powersetCard_one, Finset.sum_map] at h1
  simp only [Function.Embedding.coeFn_mk, hsingle, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h1
  simp only [Finset.mem_range, Nat.choose_one_right, pow_one, Nat.add_sub_cancel, if_pos (by omega : 1 < e + 1 + 1)] at h1
  have hne : ((e : ℝ) + 1) ≠ 0 := by positivity
  push_cast at h1
  apply mul_left_cancel₀ hne
  linarith [h1]

end GlobalTheory
