import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique

noncomputable section

open Matrix Finset
open scoped Kronecker

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma prho_submatrix_mul {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (A B : Matrix ι ι ℂ) (hA : ∀ i k, P i → ¬ P k → A i k = 0) :
    ((A * B).submatrix Subtype.val Subtype.val : Matrix {i // P i} {i // P i} ℂ) =
      (A.submatrix Subtype.val Subtype.val : Matrix {i // P i} {i // P i} ℂ) *
        (B.submatrix Subtype.val Subtype.val : Matrix {i // P i} {i // P i} ℂ) := by
  ext p r
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Finset.sum_filter_of_ne (p := P) (fun k _ hk => by_contra fun h => hk (by rw [hA _ _ p.2 h, zero_mul]))]
  exact Finset.sum_subtype _ (fun k => by simp) _

lemma prho_sub_kron {ι κ : Type*} (A B : Matrix ι ι ℂ) (C : Matrix κ κ ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext p q; simp [Matrix.kroneckerMap_apply, sub_mul]

lemma prho_kron_sub {ι κ : Type*} (A : Matrix ι ι ℂ) (B C : Matrix κ κ ℂ) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext p q; simp [Matrix.kroneckerMap_apply, mul_sub]

def adFull (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  g ⊗ₖ g.map (starRingEnd ℂ)

def adDFull (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  X ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) - (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ Xᵀ

lemma adFull_mul (g h : Matrix (Fin n) (Fin n) ℂ) : adFull (g * h) = adFull g * adFull h := by
  unfold adFull
  rw [Matrix.map_mul, mul_kronecker_mul]

lemma adFull_one : adFull (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold adFull
  rw [Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _), one_kronecker_one]

lemma adFull_star (g : Matrix (Fin n) (Fin n) ℂ) : star (adFull g) = adFull (star g) := by
  ext p q
  simp only [adFull, Matrix.star_apply, Matrix.kroneckerMap_apply, Matrix.map_apply, star_mul',
    RCLike.star_def, RCLike.conj_conj]

lemma adDFull_bracket (X Y : Matrix (Fin n) (Fin n) ℂ) :
    adDFull X * adDFull Y - adDFull Y * adDFull X = adDFull (X * Y - Y * X) := by
  simp only [adDFull, sub_mul, mul_sub, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.transpose_sub, Matrix.transpose_mul, prho_sub_kron, prho_kron_sub]
  abel

variable {ε : Fin n → Bool} {β : Bool}

lemma adFull_zero_out {g : Matrix (Fin n) (Fin n) ℂ} (hg : g * Jm ε = Jm ε * g) (p k : Fin n × Fin n)
    (hp : ε p.1 = β ∧ ε p.2 = !β) (hk : ¬ (ε k.1 = β ∧ ε k.2 = !β)) : adFull g p k = 0 := by
  simp only [adFull, Matrix.kroneckerMap_apply, Matrix.map_apply]
  by_cases h1 : ε k.1 = β
  · have h2 : ε p.2 ≠ ε k.2 := fun h => hk ⟨h1, by rw [← h]; exact hp.2⟩
    rw [uq_offdiag_zero hg h2, map_zero, mul_zero]
  · have h2 : ε p.1 ≠ ε k.1 := fun h => h1 (by rw [← h]; exact hp.1)
    rw [uq_offdiag_zero hg h2, zero_mul]

lemma adDFull_zero_out {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X) (p k : Fin n × Fin n)
    (hp : ε p.1 = β ∧ ε p.2 = !β) (hk : ¬ (ε k.1 = β ∧ ε k.2 = !β)) : adDFull X p k = 0 := by
  simp only [adDFull, Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  by_cases h1 : ε k.1 = β
  · have h2 : ε p.2 ≠ ε k.2 := fun h => hk ⟨h1, by rw [← h]; exact hp.2⟩
    have h3 : p.2 ≠ k.2 := fun h => h2 (by rw [h])
    rw [Matrix.one_apply_ne h3, uq_offdiag_zero hX (Ne.symm h2), mul_zero, mul_zero, sub_zero]
  · have h2 : ε p.1 ≠ ε k.1 := fun h => h1 (by rw [← h]; exact hp.1)
    have h3 : p.1 ≠ k.1 := fun h => h2 (by rw [h])
    rw [Matrix.one_apply_ne h3, uq_offdiag_zero hX h2, zero_mul, zero_mul, sub_zero]

variable (ε β)

def pRhoM (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (pIdx ε β) (pIdx ε β) ℂ :=
  (adFull g).submatrix Subtype.val Subtype.val

lemma pRhoM_mul {g : Matrix (Fin n) (Fin n) ℂ} (hg : g * Jm ε = Jm ε * g) (h : Matrix (Fin n) (Fin n) ℂ) :
    pRhoM ε β (g * h) = pRhoM ε β g * pRhoM ε β h := by
  unfold pRhoM
  rw [adFull_mul]
  exact prho_submatrix_mul (fun p : Fin n × Fin n => ε p.1 = β ∧ ε p.2 = !β) _ _
    (fun i k hi hk => adFull_zero_out hg i k hi hk)

lemma pRhoM_one : pRhoM ε β (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold pRhoM
  rw [adFull_one]
  exact Matrix.submatrix_one _ Subtype.val_injective

lemma pRhoM_star (g : Matrix (Fin n) (Fin n) ℂ) : star (pRhoM ε β g) = pRhoM ε β (star g) := by
  unfold pRhoM
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, ← Matrix.star_eq_conjTranspose,
    adFull_star]

lemma pRhoM_mem (k : KG ε) : pRhoM ε β (toMK k) ∈ unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ) := by
  have hk : toMK k ∈ Kset ε := k.2
  have hs : star (toMK k) ∈ Kset ε := Kset_star ε hk
  rw [Unitary.mem_iff, pRhoM_star, ← pRhoM_mul ε β hs.2, ← pRhoM_mul ε β hk.2,
    Unitary.star_mul_self_of_mem hk.1, Unitary.mul_star_self_of_mem hk.1, pRhoM_one]
  exact ⟨rfl, rfl⟩

def pRho : KG ε →* unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ) where
  toFun k := ⟨pRhoM ε β (toMK k), pRhoM_mem ε β k⟩
  map_one' := Subtype.ext (pRhoM_one ε β)
  map_mul' k l := Subtype.ext (pRhoM_mul ε β (k.2 : toMK k ∈ Kset ε).2 (toMK l))

lemma pRho_apply (k : KG ε) (p q : pIdx ε β) :
    ((pRho ε β k : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) p q =
      toMK k p.1.1 q.1.1 * star (toMK k p.1.2 q.1.2) := rfl

def pDRho : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (pIdx ε β) (pIdx ε β) ℂ where
  toFun X := (adDFull X).submatrix Subtype.val Subtype.val
  map_add' X Y := by
    ext p q
    simp only [adDFull, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply]
    ring
  map_smul' c X := by
    ext p q
    simp only [adDFull, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma pDRho_apply (X : Matrix (Fin n) (Fin n) ℂ) (p q : pIdx ε β) :
    pDRho ε β X p q = X p.1.1 q.1.1 * (1 : Matrix (Fin n) (Fin n) ℂ) p.1.2 q.1.2 -
      (1 : Matrix (Fin n) (Fin n) ℂ) p.1.1 q.1.1 * X q.1.2 p.1.2 := rfl

theorem pDRho_single (a b : Fin n) : pDRho ε β (Matrix.single a b 1) = pAdM ε β a b := by
  ext p q
  rw [pDRho_apply]
  simp only [pAdM, Matrix.single_apply, Matrix.one_apply]
  by_cases h1 : p.1.1 = a <;> by_cases h2 : q.1.1 = b <;> by_cases h3 : p.1.2 = q.1.2 <;>
    by_cases h4 : q.1.2 = a <;> by_cases h5 : p.1.2 = b <;> by_cases h6 : p.1.1 = q.1.1 <;>
    simp_all [eq_comm]

theorem pDRho_bracket {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X)
    (hY : Y * Jm ε = Jm ε * Y) :
    pDRho ε β X * pDRho ε β Y - pDRho ε β Y * pDRho ε β X = pDRho ε β (X * Y - Y * X) := by
  have e : ∀ Z : Matrix (Fin n) (Fin n) ℂ, pDRho ε β Z = (adDFull Z).submatrix Subtype.val Subtype.val :=
    fun _ => rfl
  have hs : ∀ A B : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ,
      ((A - B).submatrix Subtype.val Subtype.val : Matrix (pIdx ε β) (pIdx ε β) ℂ) =
        (A.submatrix Subtype.val Subtype.val : Matrix (pIdx ε β) (pIdx ε β) ℂ) -
          (B.submatrix Subtype.val Subtype.val : Matrix (pIdx ε β) (pIdx ε β) ℂ) := fun _ _ => rfl
  rw [e, e, e, ← prho_submatrix_mul (fun p : Fin n × Fin n => ε p.1 = β ∧ ε p.2 = !β) _ _
      (fun i k hi hk => adDFull_zero_out hX i k hi hk),
    ← prho_submatrix_mul (fun p : Fin n × Fin n => ε p.1 = β ∧ ε p.2 = !β) _ _
      (fun i k hi hk => adDFull_zero_out hY i k hi hk), ← hs, adDFull_bracket]

lemma prho_single_bracket (a b c d : Fin n) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1 h2; simp [Matrix.single_mul_single_same]
  · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]
  · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]
  · simp [Matrix.single_mul_single_of_ne, h1, h2]

theorem pAdM_kRel : Formalism.REAL.KRel ε (pAdM ε β) := by
  intro a b c d hab hcd
  have e : ∀ a b, pAdM ε β a b = pDRho ε β (Matrix.single a b 1) := fun a b => (pDRho_single ε β a b).symm
  simp only [e]
  rw [pDRho_bracket ε β (single_mul_Jm hab 1) (single_mul_Jm hcd 1), prho_single_bracket]
  split_ifs <;> simp

theorem pRho_continuous :
    Continuous (fun k : KG ε =>
      ((pRho ε β k : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ)) := by
  have hm : Continuous (fun k : KG ε => toMK k) := (continuous_toM ε).comp continuous_subtype_val
  refine continuous_matrix fun p q => ?_
  simp only [pRho_apply]
  exact (hm.matrix_elem _ _).mul ((hm.matrix_elem _ _).star)

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma prho_entry_hasDerivAt (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have h := (L.hasFDerivAt).comp_hasDerivAt _ (hasDerivAt_exp_smul_const X ((0 : ℝ) : ℂ))
  have h2 := hasDerivAt_real_of_complex' (z := 0) h
  have e : L (NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X) = X i j := by simp [L]
  exact h2.congr_deriv e

end Deriv

theorem pRho_hasDerivAt (X : Matrix (Fin n) (Fin n) ℂ) (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (i j : pIdx ε β) :
    HasDerivAt (fun t : ℝ =>
      ((pRho ε β (γ t) : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) i j)
      (pDRho ε β X i j) 0 := by
  have hf : (fun t : ℝ =>
      ((pRho ε β (γ t) : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) i j) =
      fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i.1.1 j.1.1 *
        star (NormedSpace.exp ((t : ℂ) • X) i.1.2 j.1.2) := by
    funext t
    rw [pRho_apply, hγ t]
  rw [hf]
  have h := (prho_entry_hasDerivAt X i.1.1 j.1.1).mul (prho_entry_hasDerivAt X i.1.2 j.1.2).star
  have hs : star (X i.1.2 j.1.2) = -X j.1.2 i.1.2 := by
    have := congrFun (congrFun (onep_skew hX) j.1.2) i.1.2
    simpa only [Matrix.conjTranspose_apply, Matrix.neg_apply] using this
  have e : X i.1.1 j.1.1 * star (NormedSpace.exp (((0 : ℝ) : ℂ) • X) i.1.2 j.1.2) +
      NormedSpace.exp (((0 : ℝ) : ℂ) • X) i.1.1 j.1.1 * star (X i.1.2 j.1.2) = pDRho ε β X i j := by
    rw [pDRho_apply, hs]
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  exact h.congr_deriv e

end ReciprocityTheory.ChartRestriction.DS.HW
