import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.CharpolyNewton

open Polynomial Finset

variable {k : Type} [Field k]

theorem newton_fn {σ : Type} [Fintype σ] (f : σ → k) (j : ℕ) :
    (j : k) * (univ.val.map f).esymm j = (-1) ^ (j + 1) *
      ∑ a ∈ antidiagonal j with a.1 < j,
        (-1) ^ a.1 * (univ.val.map f).esymm a.1 * ∑ i, f i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum σ k j)
  simpa only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X] using h

theorem newton_multiset (s : Multiset k) (j : ℕ) :
    (j : k) * s.esymm j = (-1) ^ (j + 1) *
      ∑ a ∈ antidiagonal j with a.1 < j, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  have hs : s = (univ : Finset (Fin s.toList.length)).val.map (fun i => s.toList.get i) := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have h := newton_fn (fun i : Fin s.toList.length => s.toList.get i) j
  rw [← hs] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have e : ∀ n : ℕ, (s.map (· ^ n)).sum = ∑ i : Fin s.toList.length, s.toList.get i ^ n := by
    intro n
    conv_lhs => rw [hs]
    rw [Multiset.map_map]
    rfl
  exact (e a.2).symm

theorem esymm_eq_of_psum_eq [CharZero k] (s t : Multiset k)
    (h : ∀ j, (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) : ∀ j, s.esymm j = t.esymm j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · have hj0 : (j : k) ≠ 0 := by exact_mod_cast hj.ne'
      apply mul_left_cancel₀ hj0
      rw [newton_multiset, newton_multiset]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [ih a.1 (Finset.mem_filter.mp ha).2, h a.2]

theorem prod_eq_of_psum_eq [CharZero k] (s t : Multiset k) (hc : Multiset.card s = Multiset.card t)
    (h : ∀ j, (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) :
    (s.map (fun a => X - C a)).prod = (t.map (fun a => X - C a)).prod := by
  ext j
  by_cases hj : j ≤ Multiset.card s
  · rw [Multiset.prod_X_sub_C_coeff s hj, Multiset.prod_X_sub_C_coeff t (hc ▸ hj), hc,
      esymm_eq_of_psum_eq s t h]
  · push_neg at hj
    rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega

theorem charpoly_eq_prod_of_trace_pow : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (a : ℕ) (M : Matrix (Fin a) (Fin a) k) (B : Multiset k), Multiset.card B = a → (∀ n : ℕ, 1 ≤ n → (M ^ n).trace = (B.map (· ^ n)).sum) → M.charpoly = (B.map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro k _ _ _ a M B hB h
  have hR : Multiset.card M.charpoly.roots = a := GlobalTheory.CharpolyPow.card_roots_charpoly M
  have hsplit : M.charpoly = (M.charpoly.roots.map fun b => X - C b).prod := by
    have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq M.charpoly_monic
      (by rw [hR, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
    exact this.symm
  rw [hsplit]
  refine prod_eq_of_psum_eq _ _ (by rw [hR, hB]) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hR, hB]
  · rw [← h n hn, Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow]

end GlobalTheory.CharpolyNewton
