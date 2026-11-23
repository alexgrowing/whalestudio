import Formalism.IncomingBounds.StatementThmP

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds.Cay

open MvPolynomial Matrix

section Der
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (D : Derivation R A A)

theorem der_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → A) :
    D (∏ j ∈ s, g j) = ∑ i ∈ s, D (g i) * ∏ j ∈ s.erase i, g j := by
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha,
    smul_eq_mul, smul_eq_mul, Finset.mul_sum]
  have key : ∀ i ∈ s, D (g i) * ∏ j ∈ (insert a s).erase i, g j =
      g a * (D (g i) * ∏ j ∈ s.erase i, g j) := by
    intro i hi
    have hne : a ≠ i := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hne,
      Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring
  rw [Finset.sum_congr rfl key]
  ring

theorem der_det {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n A) :
    D N.det = ∑ i, ∑ p, adjugate N i p * D (N p i) := by
  have hcol : ∀ i, ∑ p, adjugate N i p * D (N p i) = (N.updateCol i fun p => D (N p i)).det := by
    intro i
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hcol i]
  simp only [det_apply']
  rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Derivation.leibniz, Derivation.map_intCast, smul_zero, add_zero, smul_eq_mul,
    der_prod, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun x hx => ?_
    simp [Finset.ne_of_mem_erase hx]

theorem map_mul_der {n : Type*} [Fintype n] (X Y : Matrix n n A) :
    (X * Y).map D = X.map D * Y + X * Y.map D := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, Derivation.leibniz,
    smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem der_adj {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n A) (a b : n) :
    N.det * D (adjugate N a b) =
      D N.det * adjugate N a b - ∑ p, ∑ q, adjugate N a p * D (N p q) * adjugate N q b := by
  have h1 : (adjugate N).map D * N + adjugate N * N.map D = D N.det • (1 : Matrix n n A) := by
    rw [← map_mul_der, adjugate_mul]
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have h2 : N.det • (adjugate N).map D + adjugate N * (N.map D * adjugate N) =
      D N.det • adjugate N := by
    have h3 := congrArg (fun M => M * adjugate N) h1
    simp only [Matrix.add_mul, Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.one_mul] at h3
    exact h3
  have h4 := congrFun (congrFun h2 a) b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at h4
  have h5 : (adjugate N * (N.map D * adjugate N)) a b =
      ∑ p, ∑ q, adjugate N a p * D (N p q) * adjugate N q b := by
    simp only [Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum, mul_assoc]
  rw [h5] at h4
  rw [eq_sub_iff_add_eq]
  exact h4

end Der

theorem bord {R : Type*} [CommRing R] (k : ℕ) (B : Matrix (Fin (k+2)) (Fin (k+2)) R) (j : Fin (k+2)) :
    ∑ q : Fin (k+1), ∑ p : Fin (k+1),
        adjugate (B.submatrix j.succAbove Fin.succ) q p * B (j.succAbove p) 0 * B j q.succ
      = B j 0 * (B.submatrix j.succAbove Fin.succ).det - (-1) ^ (j : ℕ) * B.det := by
  have hcol : ∀ q : Fin (k+1), ∑ p : Fin (k+1),
      adjugate (B.submatrix j.succAbove Fin.succ) q p * B (j.succAbove p) 0 =
      (-1 : R) ^ (q : ℕ) * (B.submatrix j.succAbove q.succ.succAbove).det := by
    intro q
    have h1 : ∑ p : Fin (k+1), adjugate (B.submatrix j.succAbove Fin.succ) q p * B (j.succAbove p) 0 =
        cramer (B.submatrix j.succAbove Fin.succ) (fun p => B (j.succAbove p) 0) q := by
      rw [cramer_eq_adjugate_mulVec]; rfl
    have h2 : (B.submatrix j.succAbove Fin.succ).updateCol q (fun p => B (j.succAbove p) 0) =
        (B.submatrix j.succAbove q.succ.succAbove).submatrix id q.cycleRange := by
      ext x y
      simp only [Matrix.updateCol_apply, Matrix.submatrix_apply, id_eq, Fin.succAbove_cycleRange,
        Equiv.swap_apply_def]
      by_cases hy : y = q
      · subst hy; simp
      · have hs : y.succ ≠ q.succ := fun h => hy (Fin.succ_injective _ h)
        simp [hy, hs, Fin.succ_ne_zero]
    rw [h1, cramer_apply, h2, det_permute', Fin.sign_cycleRange]
    simp
  have hL : ∑ q : Fin (k+1), ∑ p : Fin (k+1),
      adjugate (B.submatrix j.succAbove Fin.succ) q p * B (j.succAbove p) 0 * B j q.succ =
      ∑ q : Fin (k+1), (-1 : R) ^ (q : ℕ) * (B.submatrix j.succAbove q.succ.succAbove).det *
        B j q.succ := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.sum_mul, hcol q]
  rw [hL, det_succ_row B j, Fin.sum_univ_succ (n := k+1), Fin.succAbove_zero]
  simp only [Fin.val_zero, Fin.val_succ, add_zero, mul_add, Finset.mul_sum]
  have e1 : (-1 : R) ^ (j : ℕ) * (-1) ^ (j : ℕ) = 1 := by rw [← mul_pow]; simp
  have hsum : ∑ q : Fin (k+1), (-1 : R) ^ (j : ℕ) * ((-1) ^ ((j : ℕ) + ((q : ℕ) + 1)) * B j q.succ *
      (B.submatrix j.succAbove q.succ.succAbove).det) =
      -∑ q : Fin (k+1), (-1 : R) ^ (q : ℕ) * (B.submatrix j.succAbove q.succ.succAbove).det *
        B j q.succ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    linear_combination
      (-(-1 : R) ^ (q : ℕ) * B j q.succ * (B.submatrix j.succAbove q.succ.succAbove).det) * e1
  rw [hsum]
  linear_combination (B j 0 * (B.submatrix j.succAbove Fin.succ).det) * e1

end Formalism.IncomingBounds.Cay

namespace Formalism.IncomingBounds.Cay

open MvPolynomial Matrix Formalism.IncomingBounds

variable {K : Type} [Field K] [CharZero K]

section SupSum
variable {σ M : Type} [AddCommMonoid M] (f : (σ →₀ ℕ) → K → M)

theorem supp_sum_superset (h0 : ∀ a, f a 0 = 0) (p : MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (hS : p.support ⊆ S) : ∑ a ∈ p.support, f a (coeff a p) = ∑ a ∈ S, f a (coeff a p) := by
  refine Finset.sum_subset hS fun a _ ha => ?_
  rw [MvPolynomial.notMem_support_iff.mp ha, h0]

theorem supp_sum_add (h0 : ∀ a, f a 0 = 0) (hadd : ∀ a x y, f a (x + y) = f a x + f a y)
    (p q : MvPolynomial σ K) :
    ∑ a ∈ (p + q).support, f a (coeff a (p + q)) =
      ∑ a ∈ p.support, f a (coeff a p) + ∑ a ∈ q.support, f a (coeff a q) := by
  classical
  have hpq : (p + q).support ⊆ p.support ∪ q.support := fun a ha => by
    rw [Finset.mem_union]
    by_contra hn
    rw [not_or] at hn
    rw [MvPolynomial.mem_support_iff, coeff_add, MvPolynomial.notMem_support_iff.mp hn.1,
      MvPolynomial.notMem_support_iff.mp hn.2, add_zero] at ha
    exact ha rfl
  rw [supp_sum_superset f h0 (p + q) (p.support ∪ q.support) hpq,
    supp_sum_superset f h0 p (p.support ∪ q.support) (fun _ h => Finset.mem_union_left _ h),
    supp_sum_superset f h0 q (p.support ∪ q.support) (fun _ h => Finset.mem_union_right _ h),
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [coeff_add, hadd]

theorem supp_sum_monomial (h0 : ∀ a, f a 0 = 0) (s : σ →₀ ℕ) (c : K) :
    ∑ a ∈ (monomial s c).support, f a (coeff a (monomial s c)) = f s c := by
  classical
  rw [supp_sum_superset f h0 _ {s} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    coeff_monomial, if_pos rfl]

end SupSum

def dm {σ : Type} (m : σ →₀ ℕ) (Q : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ a ∈ Q.support,
    if m ≤ a then monomial (a - m) (coeff a Q * ((mfact a : K) / (mfact (a - m) : K))) else 0

theorem diffOp_eq {σ : Type} (P Q : MvPolynomial σ K) :
    diffOp P Q = ∑ m ∈ P.support, coeff m P • dm m Q := by
  unfold Formalism.IncomingBounds.diffOp dm
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [smul_monomial, smul_eq_mul, mul_assoc]
  · rw [smul_zero]

theorem dm_add {σ : Type} (m : σ →₀ ℕ) (Q Q' : MvPolynomial σ K) :
    dm m (Q + Q') = dm m Q + dm m Q' := by
  unfold dm
  exact supp_sum_add (fun a x => if m ≤ a then
      monomial (a - m) (x * ((Formalism.IncomingBounds.mfact a : K) / (Formalism.IncomingBounds.mfact (a - m) : K))) else 0)
    (fun a => by simp) (fun a x y => by by_cases h : m ≤ a <;> simp [h, add_mul]) Q Q'

theorem dm_monomial {σ : Type} (m a : σ →₀ ℕ) (c : K) :
    dm m (monomial a c) =
      if m ≤ a then monomial (a - m) (c * ((mfact a : K) / (mfact (a - m) : K))) else 0 := by
  unfold dm
  exact supp_sum_monomial (fun b x => if m ≤ b then
      monomial (b - m) (x * ((Formalism.IncomingBounds.mfact b : K) / (Formalism.IncomingBounds.mfact (b - m) : K))) else 0)
    (fun b => by simp) a c

theorem diffOp_add {σ : Type} (P P' Q : MvPolynomial σ K) :
    diffOp (P + P') Q = diffOp P Q + diffOp P' Q := by
  rw [diffOp_eq, diffOp_eq, diffOp_eq]
  exact supp_sum_add (fun m x => x • dm m Q) (fun _ => zero_smul _ _)
    (fun _ x y => add_smul x y _) P P'

theorem diffOp_monomial {σ : Type} (m : σ →₀ ℕ) (c : K) (Q : MvPolynomial σ K) :
    diffOp (monomial m c) Q = c • dm m Q := by
  rw [diffOp_eq]
  exact supp_sum_monomial (fun m' x => x • dm m' Q) (fun _ => zero_smul _ _) m c

theorem diffOp_zero {σ : Type} (Q : MvPolynomial σ K) : diffOp (0 : MvPolynomial σ K) Q = 0 := by
  rw [diffOp_eq, MvPolynomial.support_zero, Finset.sum_empty]

theorem mfact_ne {σ : Type} (b : σ →₀ ℕ) : (mfact b : K) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  unfold Formalism.IncomingBounds.mfact Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _

theorem mfact_step {σ : Type} (b : σ →₀ ℕ) (x : σ) (hx : 0 < b x) :
    mfact b = b x * mfact (b - Finsupp.single x 1) := by
  classical
  have hxs : x ∈ b.support := Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hx)
  have hsub : (b - Finsupp.single x 1).support ⊆ b.support := by
    intro y hy
    rw [Finsupp.mem_support_iff] at hy ⊢
    intro hb
    apply hy
    rw [Finsupp.tsub_apply, hb, Nat.zero_sub]
  have key : ∀ e : σ →₀ ℕ, e.support ⊆ b.support →
      Formalism.IncomingBounds.mfact e = ∏ y ∈ b.support, (e y).factorial :=
    fun e he => Finsupp.prod_of_support_subset e he (fun _ k => k.factorial)
      (fun _ _ => Nat.factorial_zero)
  rw [key b (Finset.Subset.refl _), key _ hsub, ← Finset.mul_prod_erase _ _ hxs,
    ← Finset.mul_prod_erase _ _ hxs, ← mul_assoc]
  congr 1
  · rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    exact (Nat.mul_factorial_pred (Nat.pos_iff_ne_zero.mp hx)).symm
  · refine Finset.prod_congr rfl fun y hy => ?_
    rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hy), Nat.sub_zero]

theorem dm_zero {σ : Type} (Q : MvPolynomial σ K) : dm 0 Q = Q := by
  unfold dm
  conv_rhs => rw [MvPolynomial.as_sum Q]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [if_pos zero_le, tsub_zero, div_self (mfact_ne a), mul_one]

theorem dm_succ {σ : Type} (x : σ) (m : σ →₀ ℕ) (Q : MvPolynomial σ K) :
    dm (Finsupp.single x 1 + m) Q = pderiv x (dm m Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [dm_monomial, dm_monomial]
    by_cases hma : m ≤ a
    · rw [if_pos hma, pderiv_monomial]
      by_cases hbx : (a - m) x = 0
      · have hn : ¬ (Finsupp.single x 1 + m ≤ a) := by
          intro h
          have h' := (Finsupp.le_def.mp h) x
          rw [Finsupp.tsub_apply] at hbx
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at h'
          omega
        rw [if_neg hn, hbx, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]
      · have hle : Finsupp.single x 1 + m ≤ a := by
          rw [Finsupp.le_def]
          intro i
          have hmi := (Finsupp.le_def.mp hma) i
          rw [Finsupp.tsub_apply] at hbx
          by_cases hxi : x = i
          · subst hxi
            simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
            omega
          · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne (Ne.symm hxi)]
            omega
        have hsub : a - (Finsupp.single x 1 + m) = a - m - Finsupp.single x 1 := by
          rw [add_comm (Finsupp.single x 1) m, tsub_add_eq_tsub_tsub]
        rw [if_pos hle, hsub]
        congr 1
        have hfp := mfact_step (a - m) x (Nat.pos_of_ne_zero hbx)
        have h1 : (Formalism.IncomingBounds.mfact (a - m - Finsupp.single x 1) : K) ≠ 0 := mfact_ne _
        have h2 : (((a - m) x : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hbx
        rw [hfp, Nat.cast_mul]
        first
          | (field_simp; ring)
          | field_simp
    · have hn : ¬ (Finsupp.single x 1 + m ≤ a) := fun h => hma (le_trans le_add_self h)
      rw [if_neg hma, if_neg hn, map_zero]
  | add p q hp hq => rw [dm_add, dm_add, hp, hq, map_add]

theorem diffOp_X_mul {σ : Type} (x : σ) (P Q : MvPolynomial σ K) :
    diffOp (X x * P) Q = pderiv x (diffOp P Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have hX : (X x : MvPolynomial σ K) * monomial u a = monomial (Finsupp.single x 1 + u) a := by
      rw [X, monomial_mul, one_mul]
    rw [hX, diffOp_monomial, diffOp_monomial, dm_succ, Derivation.map_smul]
  | add p q hp hq => rw [mul_add, diffOp_add, diffOp_add, hp, hq, map_add]

theorem diffOp_C_mul {σ : Type} (c : K) (P Q : MvPolynomial σ K) :
    diffOp (MvPolynomial.C c * P) Q = c • diffOp P Q := by
  rw [C_mul']
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [smul_monomial, smul_eq_mul, diffOp_monomial, diffOp_monomial, mul_smul]
  | add p q hp hq => rw [smul_add, diffOp_add, diffOp_add, hp, hq, smul_add]

theorem diffOp_one {σ : Type} (Q : MvPolynomial σ K) : diffOp (1 : MvPolynomial σ K) Q = Q := by
  rw [← C_1, C_apply, diffOp_monomial, one_smul, dm_zero]

theorem diffOp_sum {σ ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ K) (Q : MvPolynomial σ K) :
    diffOp (∑ b ∈ s, f b) Q = ∑ b ∈ s, diffOp (f b) Q := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, Finset.sum_empty, diffOp_zero]) ?_
  intro b s hb ih
  rw [Finset.sum_insert hb, Finset.sum_insert hb, diffOp_add, ih]

end Formalism.IncomingBounds.Cay

namespace Formalism.IncomingBounds.Cay

open MvPolynomial Matrix Formalism.IncomingBounds

variable {K : Type} [Field K] [CharZero K]

def Mg (K : Type) [Field K] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (PVar n) K) :=
  Matrix.of fun i j => X (Sum.inl (i, j))

theorem dMg {n : ℕ} (i j p q : Fin n) :
    pderiv (Sum.inl (i, j)) (Mg K n p q) = if p = i ∧ q = j then 1 else 0 := by
  classical
  rw [show Mg K n p q = X (Sum.inl (p, q)) from rfl, pderiv_X, Pi.single_apply]
  by_cases h : p = i ∧ q = j
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : (Sum.inl (p, q) : Formalism.IncomingBounds.PVar n) ≠ Sum.inl (i, j) := by
      intro e
      apply h
      simpa using e
    rw [if_neg h, if_neg h']

theorem ddet {n : ℕ} (i j : Fin n) :
    pderiv (Sum.inl (i, j)) (Mg K n).det = adjugate (Mg K n) j i := by
  rw [der_det]
  simp only [dMg]
  rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => ?_
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem dadj {n : ℕ} (i j a b : Fin n) :
    (Mg K n).det * pderiv (Sum.inl (i, j)) (adjugate (Mg K n) a b) =
      adjugate (Mg K n) j i * adjugate (Mg K n) a b - adjugate (Mg K n) a i * adjugate (Mg K n) j b := by
  rw [der_adj, ddet]
  congr 1
  simp only [dMg]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro c _ hc
    simp [hc]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro p' _ hp
    refine Finset.sum_eq_zero fun c _ => ?_
    simp [hp]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem omega_step {n k : ℕ} (r c : Fin (k+2) → Fin n) (Q : MvPolynomial (PVar n) K) :
    diffOp ((Mg K n).submatrix r c).det Q =
      ∑ j : Fin (k+2), ((-1 : K) ^ (j : ℕ)) •
        pderiv (Sum.inl (r 0, c j)) (diffOp ((Mg K n).submatrix (r ∘ Fin.succ) (c ∘ j.succAbove)).det Q) := by
  rw [det_succ_row_zero, diffOp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e2 : ((-1 : MvPolynomial (Formalism.IncomingBounds.PVar n) K) ^ (j : ℕ)) = MvPolynomial.C ((-1 : K) ^ (j : ℕ)) := by
    simp
  rw [Matrix.submatrix_submatrix, e2, Matrix.submatrix_apply, mul_assoc, diffOp_C_mul,
    show Mg K n (r 0) (c j) = X (Sum.inl (r 0, c j)) from rfl, diffOp_X_mul]

theorem step_der {R' A' : Type*} [CommRing R'] [CommRing A'] [Algebra R' A'] (D : Derivation R' A' A')
    (d α Dm F W CP : A') (k s : ℕ) (hCP : D CP = 0) (hd : D d = α)
    (IH : d ^ k * F = CP * (d ^ s * Dm)) (E3 : d * D Dm = α * ((k : A') + 1) * Dm - W) :
    d ^ (k+1) * D F = CP * d ^ s * (((s : A') + 1) * α * Dm - W) := by
  have hpow : ∀ m : ℕ, d * D (d ^ m) = (m : A') * d ^ m * α := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hd]
      push_cast
      linear_combination d * ih
  have h1 := congrArg D IH
  rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz, hCP, smul_zero, add_zero] at h1
  simp only [smul_eq_mul] at h1
  linear_combination d * h1 - F * hpow k + CP * Dm * hpow s - (k : A') * α * IH + CP * d ^ s * E3

theorem gen (n s : ℕ) : ∀ (k : ℕ) (r c : Fin (k+1) → Fin n),
    (Mg K n).det ^ k * diffOp ((Mg K n).submatrix r c).det ((Mg K n).det ^ (s+1)) =
      MvPolynomial.C (∏ a ∈ Finset.range (k+1), ((s : K) + 1 + a)) *
        ((Mg K n).det ^ s * ((adjugate (Mg K n)).submatrix c r).det)
  | 0, r, c => by
    rw [pow_zero, one_mul, det_fin_one, det_fin_one]
    have hx : ((Mg K n).submatrix r c) 0 0 = X (Sum.inl (r 0, c 0)) := rfl
    rw [hx, ← mul_one (X _), diffOp_X_mul, diffOp_one, Derivation.leibniz_pow, ddet]
    simp only [submatrix_apply, Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.cast_zero, add_zero, map_add, map_natCast,
      map_one, nsmul_eq_mul, smul_eq_mul, Nat.add_sub_cancel]
    push_cast
    ring
  | k+1, r, c => by
    rw [omega_step, Finset.mul_sum]
    have hsum : ∀ j : Fin (k+2),
        (Mg K n).det ^ (k+1) * (((-1 : K) ^ (j : ℕ)) • pderiv (Sum.inl (r 0, c j))
          (diffOp ((Mg K n).submatrix (r ∘ Fin.succ) (c ∘ j.succAbove)).det ((Mg K n).det ^ (s+1)))) =
        MvPolynomial.C (∏ a ∈ Finset.range (k+1), ((s : K) + 1 + a)) * (Mg K n).det ^ s *
          ((s : MvPolynomial (PVar n) K) *
            ((-1) ^ (j : ℕ) * ((adjugate (Mg K n)).submatrix c r) j 0 *
              (((adjugate (Mg K n)).submatrix c r).submatrix j.succAbove Fin.succ).det) +
            ((adjugate (Mg K n)).submatrix c r).det) := by
      intro j
      set B := (adjugate (Mg K n)).submatrix c r with hB
      set N := B.submatrix j.succAbove Fin.succ with hN
      have IH : (Mg K n).det ^ k *
          diffOp ((Mg K n).submatrix (r ∘ Fin.succ) (c ∘ j.succAbove)).det ((Mg K n).det ^ (s+1)) =
          MvPolynomial.C (∏ a ∈ Finset.range (k+1), ((s : K) + 1 + a)) * ((Mg K n).det ^ s * N.det) :=
        gen n s k (r ∘ Fin.succ) (c ∘ j.succAbove)
      have hterm : ∀ i p : Fin (k+1), (Mg K n).det *
          (adjugate N i p * pderiv (Sum.inl (r 0, c j)) (N p i)) =
          B j 0 * (adjugate N i p * N p i) - adjugate N i p * B (j.succAbove p) 0 * B j i.succ := by
        intro i p
        have := dadj (K := K) (r 0) (c j) (c (j.succAbove p)) (r i.succ)
        have e1 : N p i = adjugate (Mg K n) (c (j.succAbove p)) (r i.succ) := rfl
        have e2 : B j 0 = adjugate (Mg K n) (c j) (r 0) := rfl
        have e3 : B (j.succAbove p) 0 = adjugate (Mg K n) (c (j.succAbove p)) (r 0) := rfl
        have e4 : B j i.succ = adjugate (Mg K n) (c j) (r i.succ) := rfl
        rw [e1, e2, e3, e4]
        linear_combination (adjugate N i p) * this
      have htr : ∑ i : Fin (k+1), ∑ p : Fin (k+1), adjugate N i p * N p i = ((k : MvPolynomial (PVar n) K) + 1) * N.det := by
        have h := adjugate_mul N
        have : ∀ i, ∑ p : Fin (k+1), adjugate N i p * N p i = N.det := by
          intro i
          have := congrFun (congrFun h i) i
          rw [mul_apply] at this
          rw [this]; simp
        simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
      have E3 : (Mg K n).det * pderiv (Sum.inl (r 0, c j)) N.det =
          B j 0 * ((k : MvPolynomial (PVar n) K) + 1) * N.det -
            ∑ q : Fin (k+1), ∑ p : Fin (k+1), adjugate N q p * B (j.succAbove p) 0 * B j q.succ := by
        rw [der_det, Finset.mul_sum]
        simp_rw [Finset.mul_sum, hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, htr]
        ring
      have St := step_der (pderiv (Sum.inl (r 0, c j))) ((Mg K n).det) (B j 0) N.det _ _
        (MvPolynomial.C (∏ a ∈ Finset.range (k+1), ((s : K) + 1 + a))) k s (pderiv_C)
        (ddet (r 0) (c j)) IH E3
      have Bd := bord k B j
      rw [← hN] at Bd
      have hsq : ((-1 : MvPolynomial (PVar n) K) ^ (j : ℕ)) * (-1) ^ (j : ℕ) = 1 := by
        rw [← mul_pow]; simp
      rw [smul_eq_C_mul]
      simp only [map_pow, map_neg, map_one]
      linear_combination ((-1 : MvPolynomial (PVar n) K) ^ (j : ℕ)) * St
        - ((-1 : MvPolynomial (PVar n) K) ^ (j : ℕ)) *
            MvPolynomial.C (∏ a ∈ Finset.range (k+1), ((s : K) + 1 + a)) * (Mg K n).det ^ s * Bd
        + MvPolynomial.C (∏ a ∈ Finset.range (k+1), ((s : K) + 1 + a)) * (Mg K n).det ^ s * B.det * hsq
    rw [Finset.sum_congr rfl fun j _ => hsum j, ← Finset.mul_sum, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← det_succ_column_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.prod_range_succ _ (k+1), map_mul]
    simp only [map_add, map_natCast, map_one]
    push_cast
    ring

theorem det_ne (n : ℕ) : (Mg K n).det ≠ 0 := by
  let φ : Formalism.IncomingBounds.PVar n → K := Sum.elim (fun p => if p.1 = p.2 then 1 else 0) (fun _ => 0)
  have h3 : (MvPolynomial.eval φ).mapMatrix (Mg K n) = 1 := by
    ext i j
    simp [φ, Mg, Matrix.one_apply, RingHom.mapMatrix_apply]
  have key : MvPolynomial.eval φ (Mg K n).det = 1 := by
    rw [RingHom.map_det, h3, det_one]
  intro h
  rw [h, map_zero] at key
  exact zero_ne_one key

end Formalism.IncomingBounds.Cay

namespace Formalism.IncomingBounds

open MvPolynomial Matrix

theorem cayleyIdentity : CayleyId := by
  intro F _ _ n0 s
  have hdl : detL F n0 = (Formalism.IncomingBounds.Cay.Mg F n0).det := rfl
  rw [hdl]
  cases n0 with
  | zero =>
    rw [Matrix.det_isEmpty, one_pow, one_pow, Formalism.IncomingBounds.Cay.diffOp_one, Finset.range_zero,
      Finset.prod_empty, one_smul]
  | succ k =>
    have h := Formalism.IncomingBounds.Cay.gen (K := F) (k+1) s k id id
    have hsub : (Formalism.IncomingBounds.Cay.Mg F (k+1)).submatrix id id =
        Formalism.IncomingBounds.Cay.Mg F (k+1) := Matrix.submatrix_id_id _
    have hadj : ((adjugate (Formalism.IncomingBounds.Cay.Mg F (k+1))).submatrix id id).det =
        (Formalism.IncomingBounds.Cay.Mg F (k+1)).det ^ k := by
      rw [Matrix.submatrix_id_id, det_adjugate, Fintype.card_fin, Nat.add_sub_cancel]
    rw [hsub, hadj] at h
    have hne : (Formalism.IncomingBounds.Cay.Mg F (k+1)).det ^ k ≠ 0 :=
      pow_ne_zero _ (Formalism.IncomingBounds.Cay.det_ne (K := F) (k+1))
    apply mul_left_cancel₀ hne
    rw [h, smul_eq_C_mul]
    ring

end Formalism.IncomingBounds
