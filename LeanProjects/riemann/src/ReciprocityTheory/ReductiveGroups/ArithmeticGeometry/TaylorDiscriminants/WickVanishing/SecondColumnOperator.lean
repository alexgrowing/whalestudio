import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SecondColumnDegree

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator

open SecondColumnDegree

variable {k : Type} [CommRing k] [Algebra ℚ k]

section General

variable {σ : Type} [Fintype σ]

def trunc (N : ℕ) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  ∑ j ∈ range (N + 1), homogeneousComponent j

theorem trunc_apply (N : ℕ) (x : MvPolynomial σ k) :
    trunc N x = ∑ j ∈ range (N + 1), homogeneousComponent j x := by
  rw [trunc, LinearMap.sum_apply]

theorem trunc_deg (N : ℕ) (x : MvPolynomial σ k) : (trunc N x).totalDegree ≤ N := by
  rw [trunc_apply]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j hj => ?_)
  by_cases h0 : homogeneousComponent j x = 0
  · rw [h0, totalDegree_zero]
    exact Nat.zero_le _
  · rw [(homogeneousComponent_isHomogeneous j x).totalDegree h0]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)

theorem trunc_id (N : ℕ) (x : MvPolynomial σ k) (hx : x.totalDegree ≤ N) : trunc N x = x := by
  rw [trunc_apply]
  conv_rhs => rw [← sum_homogeneousComponent x]
  symm
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hx)) ?_
  intro j hj hj'
  apply homogeneousComponent_eq_zero
  simp only [Finset.mem_range] at hj hj'
  omega

theorem so_coef_add (c1 c2 : σ → σ → k) (P : MvPolynomial σ k) :
    secondOrder k (fun p q => c1 p q + c2 p q) P = secondOrder k c1 P + secondOrder k c2 P := by
  unfold secondOrder
  simp only [map_add, add_mul, Finset.sum_add_distrib]

theorem so_iter_smul (c : σ → σ → k) (r : k) :
    ∀ (i : ℕ) (y : MvPolynomial σ k), (secondOrder k c)^[i] (r • y) = r • (secondOrder k c)^[i] y
  | 0, _ => rfl
  | i + 1, y => by
    rw [Function.iterate_succ_apply, so_smul, so_iter_smul c r i, ← Function.iterate_succ_apply]

def soL (c : σ → σ → k) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k where
  toFun := secondOrder k c
  map_add' := so_add c
  map_smul' := so_smul c

def opA (c : σ → σ → k) (t : k) (N : ℕ) : Module.End ℚ (MvPolynomial σ k) :=
  ((t • (soL c ∘ₗ trunc N)) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k).restrictScalars ℚ

theorem opA_apply (c : σ → σ → k) (t : k) (N : ℕ) (x : MvPolynomial σ k) :
    opA c t N x = t • secondOrder k c (trunc N x) := rfl

private theorem totalDegree_pderiv_le' (i : σ) (y : MvPolynomial σ k) :
    (pderiv i y).totalDegree ≤ y.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum y]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [pderiv_monomial]
  refine le_trans ?_ (le_totalDegree hs)
  refine Finset.sup_le fun u hu => ?_
  have hu' := MvPolynomial.support_monomial_subset hu
  rw [Finset.mem_singleton] at hu'
  subst hu'
  have hts : s - Finsupp.single i 1 ≤ s := tsub_le_self
  calc (s - Finsupp.single i 1).sum (fun _ e => e)
      ≤ (s - Finsupp.single i 1).sum (fun _ e => e) +
          (s - (s - Finsupp.single i 1)).sum (fun _ e => e) := Nat.le_add_right _ _
    _ = ((s - Finsupp.single i 1) + (s - (s - Finsupp.single i 1))).sum (fun _ e => e) :=
        (Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)).symm
    _ = s.sum (fun _ e => e) := by rw [add_tsub_cancel_of_le hts]

theorem deg_so_trunc (c : σ → σ → k) (N : ℕ) (x : MvPolynomial σ k) :
    (secondOrder k c (trunc N x)).totalDegree ≤ N := by
  unfold secondOrder
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun l' _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact ((totalDegree_pderiv_le' _ _).trans (totalDegree_pderiv_le' _ _)).trans (trunc_deg N x)

private theorem totalDegree_iterate_secondOrder_le (c : σ → σ → k) (M : ℕ) :
    ∀ (i : ℕ) (x : MvPolynomial σ k), x.totalDegree ≤ M →
      ((secondOrder k c)^[i] x).totalDegree ≤ M := by
  intro i
  induction i with
  | zero => intro x hx; exact hx
  | succ i ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    have h := deg_so_trunc c M ((secondOrder k c)^[i] x)
    rwa [trunc_id M _ (ih x hx)] at h

theorem opA_pow_apply (c : σ → σ → k) (t : k) (N : ℕ) :
    ∀ (i : ℕ) (x : MvPolynomial σ k), x.totalDegree ≤ N →
      ((opA c t N) ^ i) x = t ^ i • (secondOrder k c)^[i] x
  | 0, x, _ => by simp
  | i + 1, x, hx => by
    rw [pow_succ', Module.End.mul_apply, opA_pow_apply c t N i x hx, opA_apply, trunc_id]
    · rw [so_smul, smul_smul, ← pow_succ', ← Function.iterate_succ_apply' (f := secondOrder k c)]
    · exact (totalDegree_smul_le _ _).trans ((so_iter_deg_le c i x).trans hx)

theorem opA_pow_eq_zero (c : σ → σ → k) (t : k) (N : ℕ) : (opA c t N) ^ (N + 1) = 0 := by
  refine LinearMap.ext fun x => ?_
  have hy : (opA c t N x).totalDegree ≤ N := by
    rw [opA_apply]
    exact (totalDegree_smul_le _ _).trans (deg_so_trunc c N x)
  rw [pow_succ, Module.End.mul_apply, opA_pow_apply c t N N _ hy, opA_apply, so_iter_smul,
    ← Function.iterate_succ_apply,
    so_iter_eq_zero c (N + 1) (trunc N x) (Nat.lt_succ_of_le (trunc_deg N x)),
    smul_zero, smul_zero, LinearMap.zero_apply]

theorem opA_nilp (c : σ → σ → k) (t : k) (N : ℕ) : IsNilpotent (opA c t N) := ⟨N + 1, opA_pow_eq_zero c t N⟩

theorem opA_comm (c1 c2 : σ → σ → k) (t : k) (N : ℕ) : Commute (opA c1 t N) (opA c2 t N) := by
  show opA c1 t N * opA c2 t N = opA c2 t N * opA c1 t N
  refine LinearMap.ext fun x => ?_
  have d1 : (opA c1 t N x).totalDegree ≤ N := by
    rw [opA_apply]
    exact (totalDegree_smul_le _ _).trans (deg_so_trunc c1 N x)
  have d2 : (opA c2 t N x).totalDegree ≤ N := by
    rw [opA_apply]
    exact (totalDegree_smul_le _ _).trans (deg_so_trunc c2 N x)
  rw [Module.End.mul_apply, Module.End.mul_apply, opA_apply c1 t N (opA c2 t N x), trunc_id N _ d2,
    opA_apply c2 t N (opA c1 t N x), trunc_id N _ d1, opA_apply, opA_apply, so_smul, so_smul,
    so_comm]

theorem opA_add (c1 c2 : σ → σ → k) (t : k) (N : ℕ) :
    opA (fun p q => c1 p q + c2 p q) t N = opA c1 t N + opA c2 t N := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, opA_apply, so_coef_add, smul_add]

theorem exp_opA_apply (c : σ → σ → k) (t : k) (N : ℕ) (x : MvPolynomial σ k) (hx : x.totalDegree ≤ N) :
    IsNilpotent.exp (opA c t N) x = ∑ i ∈ range (N + 1),
      (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * t ^ i) • (secondOrder k c)^[i] x := by
  rw [IsNilpotent.exp_eq_sum (opA_pow_eq_zero c t N), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, opA_pow_apply c t N i x hx, mul_smul, algebraMap_smul]

end General

section Columns

variable {ι : Type} [Fintype ι] {n : ℕ}

def prodQ (Q : Fin n → MvPolynomial ι k) : MvPolynomial (ι × Fin n) k := ∏ b, colE b (Q b)

def E1 (c : ι → ι → k) (t : k) (N : ℕ) (y : MvPolynomial ι k) : MvPolynomial ι k :=
  ∑ i ∈ range (N + 1), (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * t ^ i) • (secondOrder k c)^[i] y

theorem totalDegree_second_exp_le (c : ι → ι → k) (t : k) (N : ℕ) (y : MvPolynomial ι k) :
    (E1 c t N y).totalDegree ≤ y.totalDegree := by
  unfold E1
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
  exact (totalDegree_smul_le _ _).trans (totalDegree_iterate_secondOrder_le c _ i y le_rfl)

theorem prodQ_deg (Q : Fin n → MvPolynomial ι k) : (prodQ Q).totalDegree ≤ ∑ b, (Q b).totalDegree := by
  unfold prodQ
  refine (totalDegree_finset_prod _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  unfold colE
  exact totalDegree_rename_le _ _

theorem prodQ_update (Q : Fin n → MvPolynomial ι k) (b0 : Fin n) (y : MvPolynomial ι k) :
    prodQ (Function.update Q b0 y) = colE b0 y * ∏ b ∈ univ.erase b0, colE b (Q b) := by
  unfold prodQ
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b0)]
  congr 1
  · simp [Function.update_apply]
  · exact Finset.prod_congr rfl fun b hb => by simp [Function.update_apply, Finset.ne_of_mem_erase hb]

theorem prodQ_eq (Q : Fin n → MvPolynomial ι k) (b0 : Fin n) :
    prodQ Q = colE b0 (Q b0) * ∏ b ∈ univ.erase b0, colE b (Q b) := by
  unfold prodQ
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ b0)).symm

theorem exp_col (c : ι → ι → k) (t : k) (N : ℕ) (Q : Fin n → MvPolynomial ι k) (b0 : Fin n)
    (hdeg : (prodQ Q).totalDegree ≤ N) :
    IsNilpotent.exp (opA (cB c b0) t N) (prodQ Q) = prodQ (Function.update Q b0 (E1 c t N (Q b0))) := by
  rw [exp_opA_apply _ t N _ hdeg, prodQ_update, prodQ_eq Q b0]
  have hR : ∀ l : ι, pderiv (l, b0) (∏ b ∈ univ.erase b0, colE b (Q b)) = 0 :=
    fun l => pderiv_prod_colE b0 _ (Finset.notMem_erase b0 _) Q l
  unfold E1
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [so_colB_iter c b0 _ hR i, map_smul, smul_mul_assoc]

def cS (c : ι → ι → k) (S : Finset (Fin n)) : ι × Fin n → ι × Fin n → k :=
  fun p q => ∑ b ∈ S, cB c b p q

theorem exp_cols (c : ι → ι → k) (t : k) (N : ℕ) (D : Fin n → ℕ) (hD : ∑ b, D b ≤ N) :
    ∀ (S : Finset (Fin n)) (Q : Fin n → MvPolynomial ι k), (∀ b, (Q b).totalDegree ≤ D b) →
      IsNilpotent.exp (opA (cS c S) t N) (prodQ Q) =
        prodQ (fun b => if b ∈ S then E1 c t N (Q b) else Q b) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro Q _
    have h0 : opA (cS c (∅ : Finset (Fin n))) t N = 0 := by
      refine LinearMap.ext fun x => ?_
      rw [opA_apply, so_def]
      simp [cS]
    rw [h0, IsNilpotent.exp_zero]
    simp
  | insert a S ha ih =>
    intro Q hQ
    have hcs : cS c (insert a S) = fun p q => cB c a p q + cS c S p q := by
      funext p q
      simp only [cS, Finset.sum_insert ha]
    have hdeg : (prodQ fun b => if b ∈ S then E1 c t N (Q b) else Q b).totalDegree ≤ N := by
      refine (prodQ_deg _).trans (le_trans (Finset.sum_le_sum fun b _ => ?_) hD)
      split_ifs
      · exact (totalDegree_second_exp_le c t N (Q b)).trans (hQ b)
      · exact hQ b
    rw [hcs, opA_add, IsNilpotent.exp_add_of_commute (opA_comm _ _ t N) (opA_nilp _ t N)
      (opA_nilp _ t N), Module.End.mul_apply, ih Q hQ, exp_col c t N _ a hdeg]
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      simp [ha]
    · simp [hb, Finset.mem_insert]

theorem cS_univ (c : ι → ι → k) :
    cS c (univ : Finset (Fin n)) = fun p q => if p.2 = q.2 then c p.1 q.1 else 0 := by
  unfold cS cB
  funext p q
  by_cases h : p.2 = q.2
  · rw [if_pos h]
    simp only [← h, and_self, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ => if_neg ?_
    rintro ⟨h1, h2⟩
    exact h (h1.trans h2.symm)

end Columns

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
