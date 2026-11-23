import Mathlib

noncomputable section

open MvPolynomial

namespace GlobalTheory.PolyEntryMul

theorem totalDegree_bind₁_le_of_le_one {σ τ : Type*} (f : σ → MvPolynomial τ ℂ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (Q : MvPolynomial σ ℂ) :
    (bind₁ f Q).totalDegree ≤ Q.totalDegree := by
  classical
  conv_lhs => rw [Q.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  refine (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ (hf i))).trans ?_
  simp [Finsupp.sum]

def subst {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n × Fin n) ⊕ (Fin n × Fin n) → MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ
  | Sum.inl z => ∑ k : Fin n, ∑ l : Fin n, C (a z.1 k * b l z.2) * X (Sum.inl (k, l))
  | Sum.inr z => ∑ k : Fin n, ∑ l : Fin n, C (star (a z.1 k * b l z.2)) * X (Sum.inr (k, l))

theorem totalDegree_subst {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) (i) :
    (subst a b i).totalDegree ≤ 1 := by
  rcases i with z | z <;>
  · refine totalDegree_finsetSum_le fun k _ => totalDegree_finsetSum_le fun l _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]

theorem main : ∀ (n : ℕ) (a b : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ), ∃ Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, Q.totalDegree ≤ P.totalDegree ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (a * g * b) z.1 z.2) (fun z : Fin n × Fin n => star ((a * g * b) z.1 z.2))) P = MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (g) z.1 z.2) (fun z : Fin n × Fin n => star ((g) z.1 z.2))) Q := by
  intro n a b P
  refine ⟨bind₁ (subst a b) P, totalDegree_bind₁_le_of_le_one _ (totalDegree_subst a b) P, fun g => ?_⟩
  conv_rhs => rw [eval, eval₂Hom_bind₁]
  rw [eval]
  refine congrArg (fun x => eval₂Hom (RingHom.id ℂ) x P) (funext fun i => ?_)
  rcases i with z | z
  · simp only [Sum.elim_inl, subst, map_sum, map_mul, coe_eval₂Hom, eval₂_C, eval₂_X,
      RingHom.id_apply, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  · simp only [Sum.elim_inr, subst, map_sum, map_mul, coe_eval₂Hom, eval₂_C, eval₂_X,
      RingHom.id_apply, Matrix.mul_apply, Finset.sum_mul, star_sum, star_mul']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    ring

end GlobalTheory.PolyEntryMul
