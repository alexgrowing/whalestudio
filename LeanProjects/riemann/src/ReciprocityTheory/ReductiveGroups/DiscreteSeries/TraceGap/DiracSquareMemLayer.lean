import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight

noncomputable section

open MvPolynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

def entVar (g : Matrix (Fin n) (Fin n) ℂ) : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ :=
  Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))

abbrev EntIdx (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

theorem totalDegree_bind_le_of_linear {ι : Type*} (f : ι → MvPolynomial ι ℂ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (Q : MvPolynomial ι ℂ) : (bind₁ f Q).totalDegree ≤ Q.totalDegree := by
  classical
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hm)
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (m i) (hf i)

def trF (g : Matrix (Fin n) (Fin n) ℂ) : EntIdx n → MvPolynomial (EntIdx n) ℂ :=
  Sum.elim (fun x => ∑ l, C (g x.1 l) * X (Sum.inl (l, x.2)))
    (fun x => ∑ l, C (star (g x.1 l)) * X (Sum.inr (l, x.2)))

theorem trF_totalDegree (g : Matrix (Fin n) (Fin n) ℂ) (i : EntIdx n) : (trF g i).totalDegree ≤ 1 := by
  classical
  rcases i with x | x <;>
  · simp only [trF, Sum.elim_inl, Sum.elim_inr]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]

theorem eval_trF (g h : Matrix (Fin n) (Fin n) ℂ) (i : EntIdx n) :
    eval (entVar h) (trF g i) = entVar (g * h) i := by
  rcases i with x | x
  · simp [trF, entVar, Matrix.mul_apply]
  · simp [trF, entVar, Matrix.mul_apply, star_sum]

theorem eval_mul_eq_bind₁ (g h : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (EntIdx n) ℂ) :
    eval (entVar (g * h)) P = eval (entVar h) (bind₁ (trF g) P) := by
  have := eval₂Hom_bind₁ (RingHom.id ℂ) (entVar h) (trF g) P
  simp only [coe_eval₂Hom] at this
  rw [show eval (entVar h) (bind₁ (trF g) P) = eval₂ (RingHom.id ℂ) (entVar h) (bind₁ (trF g) P) from rfl, this]
  show eval₂ (RingHom.id ℂ) _ P = eval₂ (RingHom.id ℂ) _ P
  congr 1
  funext i
  exact (eval_trF g h i).symm

def wtM (m : EntIdx n →₀ ℕ) : Fin n → ℝ := fun a =>
  ∑ j, (((m (Sum.inr (a, j)) : ℕ) : ℝ) - ((m (Sum.inl (a, j)) : ℕ) : ℝ))

def dTor (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

theorem eval_monomial_tor (θ : Fin n → ℝ) (h : Matrix (Fin n) (Fin n) ℂ) (m : EntIdx n →₀ ℕ) :
    eval (entVar (star (dTor θ) * h)) (monomial m 1) =
      Complex.exp (((∑ a, wtM m a * θ a : ℝ) : ℂ) * Complex.I) * eval (entVar h) (monomial m 1) := by
  classical
  set s : EntIdx n → ℝ := Sum.elim (fun x => -θ x.1) (fun x => θ x.1) with hs
  have hst : ∀ t : ℝ, star (Complex.exp ((t : ℂ) * Complex.I)) = Complex.exp (((-t : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [← starRingEnd_apply, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
  have hent : ∀ i, entVar (star (dTor θ) * h) i = Complex.exp ((s i : ℂ) * Complex.I) * entVar h i := by
    intro i
    rcases i with x | x
    · simp only [entVar, Sum.elim_inl, hs, dTor, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul, Pi.star_apply]
      rw [hst]
    · simp only [entVar, Sum.elim_inr, hs, dTor, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul, Pi.star_apply, star_mul', star_star]
  simp only [eval_monomial, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [hent, mul_pow, Finset.prod_mul_distrib]
  congr 1
  simp only [← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  congr 1
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [wtM, hs, Sum.elim_inl, Sum.elim_inr]
  push_cast
  rw [← Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end ReciprocityTheory.ChartRestriction.DS.TRGap
