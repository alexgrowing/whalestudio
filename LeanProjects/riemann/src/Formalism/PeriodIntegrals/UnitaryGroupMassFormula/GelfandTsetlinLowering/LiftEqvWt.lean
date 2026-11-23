import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDefs

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

namespace EqvWt

theorem coeff_aeval_scale {σ : Type} (e : σ → ℂ) (f : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    coeff m (aeval (fun v => C (e v) * X v) f) = (m.prod fun v k => e v ^ k) * coeff m f := by
  classical
  refine MvPolynomial.induction_on' f (fun u a => ?_) (fun p q hp hq => ?_)
  · have key : aeval (fun v => C (e v) * X v) (monomial u a) =
        monomial u (a * u.prod fun v k => e v ^ k) := by
      rw [aeval_monomial, monomial_eq]
      simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow,
        MvPolynomial.algebraMap_eq]
      ring
    rw [key, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  · rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem rowAct_diagonal {r c : ℕ} (d : Fin r → ℂ) :
    rowAct ℂ (n := c) (Matrix.diagonal d) = aeval (fun v : Fin r × Fin c => C (d v.1) * X v) := by
  unfold Formalism.GradedWeylDivisibility.rowAct
  congr 1
  funext v
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
  · simp

theorem prod_rowDeg {r c : ℕ} (x : Fin r → ℂ) (m : Fin r × Fin c →₀ ℕ) :
    (m.prod fun v k => x v.1 ^ k) = ∏ a, x a ^ rowDeg m a := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  unfold rowDeg
  show ∏ y : Fin c, x a ^ m (a, y) = x a ^ ∑ s, m (a, s)
  rw [Finset.prod_pow_eq_pow_sum]

theorem coeff_sqAct_diag {r : ℕ} (lam : DomWeight r) (t : Fin r → ℂˣ) (f : MvPolynomial (Fin r × Fin r) ℂ)
    (m : Fin r × Fin r →₀ ℕ) :
    coeff m (sqAct ℂ r lam (diagGL ℂ r t) f) =
      (∏ a, (t a : ℂ)) ^ lam.detShift * ((∏ a, (t a : ℂ) ^ rowDeg m a) * coeff m f) := by
  have hdet : detPow ℂ r (diagGL ℂ r t) lam.detShift = (∏ a, (t a : ℂ)) ^ lam.detShift := by
    unfold detPow
    rw [Units.val_zpow_eq_zpow_val]
    congr 1
    show Matrix.det (Matrix.diagonal fun a => (t a : ℂ)) = _
    exact Matrix.det_diagonal
  have htr : ((diagGL ℂ r t : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).transpose =
      Matrix.diagonal fun a => (t a : ℂ) :=
    Matrix.diagonal_transpose _
  unfold sqAct
  rw [coeff_smul, smul_eq_mul, hdet, htr, rowAct_diagonal, coeff_aeval_scale,
    prod_rowDeg (fun a => (t a : ℂ)) m]

theorem weight_rowW_apply {r c : ℕ} (m : Fin r × Fin c →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r c) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  unfold rowDeg
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp [rowW]
  · intro b _ hb
    refine Finset.sum_eq_zero fun s _ => ?_
    simp [rowW, Pi.single_apply, Ne.symm hb]
  · simp

theorem weight_colW_apply {r c : ℕ} (m : Fin r × Fin c →₀ ℕ) (j : Fin c) :
    Finsupp.weight (colW r c) m j = ∑ a, m (a, j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single j]
  · simp [colW]
  · intro b _ hb
    simp [colW, Pi.single_apply, Ne.symm hb]
  · simp

theorem weight_lastW {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) :
    Finsupp.weight (lastW (n + 1)) m = rowDeg m (Fin.last n) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
  unfold rowDeg
  rw [Finset.sum_eq_single (Fin.last n)]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp [lastW]
  · intro b _ hb
    refine Finset.sum_eq_zero fun s _ => ?_
    have hb' : ¬ (b.1 = n) := fun h => hb (Fin.ext (by simp [h]))
    simp [lastW, hb']
  · simp

theorem sum_rowDeg_of_mem {r : ℕ} (lam : DomWeight r) (f : MvPolynomial (Fin r × Fin r) ℂ)
    (hf : f ∈ nablaSq ℂ r lam) (m : Fin r × Fin r →₀ ℕ) (hm : coeff m f ≠ 0) :
    ∑ a, rowDeg m a = ∑ j, lam.natW j := by
  have hf' : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ r r lam.natW := hf
  have hw : Finsupp.weight (colW r r) m = lam.natW :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hf').1 hm
  calc ∑ a, rowDeg m a = ∑ a, ∑ j, m (a, j) := rfl
    _ = ∑ j, ∑ a, m (a, j) := Finset.sum_comm
    _ = ∑ j, Finsupp.weight (colW r r) m j := by simp only [weight_colW_apply]
    _ = ∑ j, lam.natW j := by rw [hw]

theorem sum_natW {r : ℕ} (lam : DomWeight r) :
    ((∑ j, lam.natW j : ℕ) : ℤ) = wsum lam - r * lam.detShift := by
  push_cast
  have h : ∀ j : Fin r, ((lam.natW j : ℕ) : ℤ) = lam.w j - lam.detShift := by
    intro j
    have hj := j.isLt
    have hle : lam.detShift ≤ lam.w j := by
      unfold DomWeight.detShift
      rw [dif_pos (by omega : 0 < r)]
      exact lam.anti (Fin.le_iff_val_le_val.mpr (by show j.1 ≤ r - 1; omega))
    unfold DomWeight.natW
    omega
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_sub_distrib]
  simp [wsum]

theorem two_zpow_inj {k l : ℤ} (e : (2 : ℂ) ^ k = (2 : ℂ) ^ l) : k = l := by
  have h : (((2 : ℝ) ^ k : ℝ) : ℂ) = (((2 : ℝ) ^ l : ℝ) : ℂ) := by
    push_cast
    exact e
  exact zpow_right_injective₀ (by norm_num) (by norm_num) (Complex.ofReal_injective h)

theorem embGL_diagGL {n : ℕ} (t : Fin n → ℂˣ) :
    embGL ℂ n (n + 1) rfl (diagGL ℂ n t) =
      diagGL ℂ (n + 1) (fun a => if ha : a.1 < n then t ⟨a.1, ha⟩ else 1) := by
  apply Units.ext
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [embGL, blkHom, diagGL, Matrix.diagonal_apply, Matrix.reindexAlgEquiv_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply, Fin.ext_iff] <;> omega

theorem coeff_eq_of_eqv {n : ℕ} (lam : DomWeight (n + 1)) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hφ : IsEqv rfl mu lam φ) (t : Fin n → ℂˣ) (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu)
    (κ : ℂ) (hκ : sqAct ℂ n mu (diagGL ℂ n t) s = κ • s) (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ)
    (hm : coeff m (φ s) ≠ 0) :
    (∏ i, (t i : ℂ)) ^ lam.detShift * ∏ i, (t i : ℂ) ^ rowDeg m (Fin.castSucc i) = κ := by
  have h1 := hφ.2 (diagGL ℂ n t) s hs
  rw [hκ, map_smul, embGL_diagGL] at h1
  have h2 := congrArg (coeff m) h1
  rw [coeff_smul, coeff_sqAct_diag, smul_eq_mul, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc] at h2
  simp only [Fin.coe_castSucc, Fin.is_lt, dite_true, dif_pos, Fin.eta, Fin.val_last, lt_self_iff_false,
    dite_false, Units.val_one, one_pow, mul_one] at h2
  exact mul_right_cancel₀ hm (by linear_combination (-1 : ℂ) * h2)

theorem equivariant_last_degree_coeff {n : ℕ} (lam : DomWeight (n + 1)) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hφ : IsEqv rfl mu lam φ) (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu)
    (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (hm : coeff m (φ s) ≠ 0) :
    ((rowDeg m (Fin.last n) : ℕ) : ℤ) = wsum lam - wsum mu - lam.detShift := by
  set t : Fin n → ℂˣ := fun _ => Units.mk0 (2 : ℂ) two_ne_zero with ht
  have htv : ∀ i, (t i : ℂ) = 2 := fun _ => rfl
  have hκ : sqAct ℂ n mu (diagGL ℂ n t) s =
      ((∏ i : Fin n, (t i : ℂ)) ^ mu.detShift * (2 : ℂ) ^ (∑ j, mu.natW j)) • s := by
    ext m'
    rw [coeff_sqAct_diag, coeff_smul, smul_eq_mul]
    by_cases h0 : coeff m' s = 0
    · simp [h0]
    · have hs' := sum_rowDeg_of_mem mu s hs m' h0
      simp only [htv, Finset.prod_pow_eq_pow_sum, hs']
      ring
  have h1 := coeff_eq_of_eqv lam mu φ hφ t s hs _ hκ m hm
  simp only [htv, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum] at h1
  have hz : ∀ (a : ℕ) (d : ℤ), ((2 : ℂ) ^ a) ^ d = (2 : ℂ) ^ ((a : ℤ) * d) := by
    intro a d
    rw [← zpow_natCast, ← zpow_mul]
  have hn : ∀ a : ℕ, (2 : ℂ) ^ a = (2 : ℂ) ^ (a : ℤ) := fun a => (zpow_natCast 2 a).symm
  rw [hz, hz, hn (∑ i : Fin n, rowDeg m (Fin.castSucc i)), hn (∑ j, mu.natW j),
    ← zpow_add₀ (two_ne_zero : (2 : ℂ) ≠ 0), ← zpow_add₀ (two_ne_zero : (2 : ℂ) ≠ 0)] at h1
  have E := two_zpow_inj h1
  have hmem : φ s ∈ nablaSq ℂ (n + 1) lam := hφ.1 s hs
  have T := sum_rowDeg_of_mem lam (φ s) hmem m hm
  rw [Fin.sum_univ_castSucc] at T
  have SL := sum_natW lam
  have SM := sum_natW mu
  have T' : ((∑ i : Fin n, rowDeg m (Fin.castSucc i) : ℕ) : ℤ) + (rowDeg m (Fin.last n) : ℤ) =
      ((∑ j, lam.natW j : ℕ) : ℤ) := by exact_mod_cast T
  push_cast at E SL SM T' ⊢
  linear_combination (-1 : ℤ) * E + T' + SL - SM

end EqvWt

open EqvWt in
theorem equivariant_last_degree : EqvLast := by
  intro n N h lam mu _ φ hφ s hs
  subst h
  intro m hm
  rw [weight_lastW]
  have := equivariant_last_degree_coeff lam mu φ hφ s hs m hm
  show rowDeg m (Fin.last n) = (wsum lam - wsum mu - lam.detShift).toNat
  omega

open EqvWt in
theorem equivariant_partial_weight : EqvRowWt := by
  intro n N h lam mu hI φ hφ ω s hs hω
  subst h
  intro m hm
  funext a
  rw [weight_rowW_apply]
  induction a using Fin.lastCases with
  | last =>
    have := equivariant_last_degree_coeff lam mu φ hφ s hs m hm
    unfold liftWt
    rw [dif_neg (by simp)]
    show rowDeg m (Fin.last n) = (wsum lam - wsum mu - lam.detShift).toNat
    omega
  | cast i =>
    have hi := i.isLt
    let t : Fin n → ℂˣ := fun j => if j = i then Units.mk0 (2 : ℂ) two_ne_zero else 1
    have hp : ∀ f : Fin n → ℕ, ∏ j, (t j : ℂ) ^ f j = 2 ^ f i := by
      intro f
      rw [Finset.prod_eq_single i]
      · simp [t]
      · intro j _ hj
        simp [t, hj]
      · simp
    have hp0 : ∏ j, (t j : ℂ) = 2 := by simpa using hp (fun _ => 1)
    have hκ : sqAct ℂ n mu (diagGL ℂ n t) s =
        ((∏ j, (t j : ℂ)) ^ mu.detShift * ∏ j, (t j : ℂ) ^ ω j) • s := by
      ext m'
      rw [coeff_sqAct_diag, coeff_smul, smul_eq_mul]
      by_cases h0 : coeff m' s = 0
      · simp [h0]
      · have hw := hω h0
        have hr : ∀ j, rowDeg m' j = ω j := fun j => by rw [← weight_rowW_apply, hw]
        simp only [hr]
        ring
    have h1 := coeff_eq_of_eqv lam mu φ hφ t s hs _ hκ m hm
    rw [hp0, hp (fun j => rowDeg m (Fin.castSucc j)), hp ω] at h1
    rw [← zpow_natCast, ← zpow_natCast (2 : ℂ) (ω i), ← zpow_add₀ (two_ne_zero : (2 : ℂ) ≠ 0),
      ← zpow_add₀ (two_ne_zero : (2 : ℂ) ≠ 0)] at h1
    have E := two_zpow_inj h1
    have hle : lam.detShift ≤ mu.detShift := by
      have h2 := (hI ⟨n - 1, by omega⟩).2
      unfold DomWeight.detShift
      rw [dif_pos (by omega : 0 < n + 1), dif_pos (by omega : 0 < n)]
      exact (le_of_eq (congrArg lam.w (Fin.ext (by show n + 1 - 1 = n - 1 + 1; omega)))).trans h2
    unfold liftWt
    rw [dif_pos (by simp)]
    simp only [Fin.coe_castSucc, Fin.eta]
    omega

end PI.WGL
