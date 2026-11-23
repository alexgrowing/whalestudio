import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape

namespace GlobalTheory.TotalDegreeBounds

open MvPolynomial

theorem totalDegree_aeval_le {σ τ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (f : σ → MvPolynomial τ A) (hf : ∀ i, (f i).totalDegree ≤ 1) (P : MvPolynomial σ R) :
    (MvPolynomial.aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun d hd => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap R (MvPolynomial τ A) (coeff d P)).totalDegree = 0 := by
    rw [MvPolynomial.algebraMap_apply, MvPolynomial.totalDegree_C]
  rw [h0, zero_add]
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  unfold Finsupp.sum
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (d i) (hf i)

theorem totalDegree_sum_X_mul_C_le {ι τ A : Type*} [Fintype ι] [CommSemiring A]
    (g : ι → τ) (a : ι → A) :
    (∑ l : ι, (X (g l) * C (a l) : MvPolynomial τ A)).totalDegree ≤ 1 := by
  classical
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, add_zero]
  refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
  simp

theorem main : (let d1 : (n : ℕ) → Fin n × Fin n ⊕ Fin n × Fin n → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (GlobalTheory.PsCo.Pc1.Poly n) := @(fun (n : ℕ) (x : Fin n × Fin n ⊕ Fin n × Fin n) ↦ match x with | Sum.inl x => ∑ l : Fin n, MvPolynomial.X (Sum.inr (l, Prod.fst x)) * (MvPolynomial.C : MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ)) (MvPolynomial.X (Sum.inl (l, Prod.snd x))) | Sum.inr x => ∑ l : Fin n, MvPolynomial.X (Sum.inl (l, Prod.fst x)) * (MvPolynomial.C : MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ)) (MvPolynomial.X (Sum.inr (l, Prod.snd x)))); let d2 : (n : ℕ) → GlobalTheory.PsCo.Pc1.Poly n →ₐ[ℂ] MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (GlobalTheory.PsCo.Pc1.Poly n) := @(fun (n : ℕ) ↦ MvPolynomial.aeval (d1 n)); ∀ {n : ℕ} (P : GlobalTheory.PsCo.Pc1.Poly n), MvPolynomial.totalDegree ((d2 n : GlobalTheory.PsCo.Pc1.Poly n → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (GlobalTheory.PsCo.Pc1.Poly n)) P) ≤ MvPolynomial.totalDegree P) := by
  intro d1 d2 n P
  refine totalDegree_aeval_le (d1 n) ?_ P
  rintro (x | x)
  · exact totalDegree_sum_X_mul_C_le _ _
  · exact totalDegree_sum_X_mul_C_le _ _

end GlobalTheory.TotalDegreeBounds
