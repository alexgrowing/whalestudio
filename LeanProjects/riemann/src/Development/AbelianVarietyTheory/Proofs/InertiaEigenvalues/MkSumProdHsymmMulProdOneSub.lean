import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet

noncomputable section

open Finset PowerSeries

namespace GlobalTheory.JSW

theorem sum_finsuppAntidiag_univ_fin {M : Type*} [AddCommMonoid M] {m : ℕ} (d : ℕ)
    (F : (Fin m → ℕ) → M) :
    ∑ l ∈ finsuppAntidiag (univ : Finset (Fin m)) d, F l =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d, F k := by
  refine Finset.sum_equiv Finsupp.equivFunOnFinite ?_ ?_
  · intro l
    simp [mem_finsuppAntidiag, Finset.Nat.mem_antidiagonalTuple]
  · intro l _
    rfl

theorem coeff_prod_mk_fin {m : ℕ} (f : Fin m → ℕ → ℂ) (d : ℕ) :
    coeff d (∏ j, PowerSeries.mk (f j)) =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, f j (k j) := by
  rw [coeff_prod, sum_finsuppAntidiag_univ_fin d (fun k => ∏ j, coeff (k j) (PowerSeries.mk (f j)))]
  simp only [coeff_mk]

theorem prod_map_X_eq_monomial_toFinsupp {n : ℕ} (s : Multiset (Fin n)) :
    (s.map (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ)).prod =
      MvPolynomial.monomial (Multiset.toFinsupp s) 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add, map_add,
      Multiset.toFinsupp_singleton, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

theorem sum_toFinsupp_fin {n : ℕ} (s : Multiset (Fin n)) :
    ∑ i, Multiset.toFinsupp s i = Multiset.card s := by
  simp [Multiset.toFinsupp_apply, Multiset.sum_count_eq_card]

theorem hsymm_fin_eq_sum_monomial {n : ℕ} (k : ℕ) :
    MvPolynomial.hsymm (Fin n) ℤ k =
      ∑ l ∈ finsuppAntidiag (univ : Finset (Fin n)) k, MvPolynomial.monomial l 1 := by
  rw [MvPolynomial.hsymm]
  refine Finset.sum_bij (fun s _ => Multiset.toFinsupp s.1) ?_ ?_ ?_ ?_
  · intro s _
    rw [mem_finsuppAntidiag]
    refine ⟨?_, subset_univ _⟩
    rw [sum_toFinsupp_fin, s.2]
  · intro a _ b _ h
    exact Sym.coe_injective (Multiset.toFinsupp.injective h)
  · intro l hl
    rw [mem_finsuppAntidiag] at hl
    refine ⟨⟨Finsupp.toMultiset l, ?_⟩, mem_univ _, ?_⟩
    · rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact hl.1
    · simp
  · intro s _
    exact prod_map_X_eq_monomial_toFinsupp s.1

theorem eval₂_hsymm_fin {n : ℕ} (α : Fin n → ℂ) (k : ℕ) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ k) =
      ∑ l ∈ Finset.Nat.antidiagonalTuple n k, ∏ i, α i ^ l i := by
  rw [hsymm_fin_eq_sum_monomial, MvPolynomial.eval₂_sum,
    ← sum_finsuppAntidiag_univ_fin k (fun l => ∏ i, α i ^ l i)]
  refine sum_congr rfl fun l _ => ?_
  rw [MvPolynomial.eval₂_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem one_sub_C_mul_X_mul_mk_pow (a : ℂ) :
    (1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.mk (fun k => a ^ k) = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul]
  cases k with
  | zero => simp
  | succ k => simp [pow_succ, mul_comm]

theorem mk_hsymm_mul_prod_one_sub {n : ℕ} (α : Fin n → ℂ) (u : ℂ) :
    PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * u ^ k) *
      ∏ i, (1 - PowerSeries.C (α i * u) * PowerSeries.X) = 1 := by
  have h : PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * u ^ k) =
      ∏ i, PowerSeries.mk (fun k => (α i * u) ^ k) := by
    ext k
    rw [coeff_prod_mk_fin, coeff_mk, eval₂_hsymm_fin, sum_mul]
    refine sum_congr rfl fun l hl => ?_
    rw [Finset.Nat.mem_antidiagonalTuple] at hl
    simp_rw [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, hl]
  rw [h, ← prod_mul_distrib]
  exact prod_eq_one fun i _ => by rw [mul_comm]; exact one_sub_C_mul_X_mul_mk_pow _

theorem mk_sum_prod_hsymm_mul_prod_one_sub : ∀ {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ),
    PowerSeries.mk (fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j)) *
      ∏ p : Fin n × Fin m, (1 - PowerSeries.C (α p.1 * β p.2 * T) * PowerSeries.X) = 1 := by
  intro m n α β T
  have h1 : PowerSeries.mk (fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j)) =
      ∏ j, PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * (β j * T) ^ k) := by
    ext d
    rw [coeff_mk, coeff_prod_mk_fin, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [Finset.Nat.mem_antidiagonalTuple] at hk
    simp_rw [mul_pow, ← mul_assoc, prod_mul_distrib, prod_pow_eq_pow_sum, hk]
    ring
  have h2 : ∏ p : Fin n × Fin m, (1 - PowerSeries.C (α p.1 * β p.2 * T) * PowerSeries.X) =
      ∏ j, ∏ i, (1 - PowerSeries.C (α i * (β j * T)) * PowerSeries.X) := by
    rw [Fintype.prod_prod_type, Finset.prod_comm]
    simp_rw [mul_assoc]
  rw [h1, h2, ← prod_mul_distrib]
  exact prod_eq_one fun j _ => mk_hsymm_mul_prod_one_sub α (β j * T)

end GlobalTheory.JSW
