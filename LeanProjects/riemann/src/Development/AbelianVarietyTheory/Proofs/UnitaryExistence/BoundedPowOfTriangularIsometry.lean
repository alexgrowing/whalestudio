import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

namespace GlobalTheory.TriangularIsometryBoundedPowers

open Matrix

lemma det_block_ne {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor B i ≠ 0) (j : Fin n) :
    (B.submatrix (Subtype.val : {c : Fin n // c < j} → Fin n)
      (Subtype.val : {c : Fin n // c < j} → Fin n)).det ≠ 0 := by
  have h := hB (Fin.castSucc j)
  unfold ReciprocityTheory.ChartRestriction.G.FD.lminor at h
  let e : Fin ((Fin.castSucc j : Fin (n + 1)) : ℕ) ≃ {c : Fin n // c < j} :=
    { toFun := fun k => ⟨Fin.castLE (Nat.le_of_lt_succ (Fin.castSucc j).isLt) k, by
        rw [Fin.lt_def]
        exact k.isLt⟩
      invFun := fun c => ⟨c.1.val, c.2⟩
      left_inv := fun k => Fin.ext rfl
      right_inv := fun c => Subtype.ext (Fin.ext rfl) }
  have e2 : (B.submatrix (Subtype.val : {c : Fin n // c < j} → Fin n)
      (Subtype.val : {c : Fin n // c < j} → Fin n)).submatrix e e =
      B.submatrix (Fin.castLE (Nat.le_of_lt_succ (Fin.castSucc j).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (Fin.castSucc j).isLt)) := rfl
  rw [← Matrix.det_submatrix_equiv_self e, e2]
  exact h

lemma exists_col {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor B i ≠ 0) (j : Fin n) :
    ∃ y : Fin n → ℂ, y j = 1 ∧ (∀ c, j < c → y c = 0) ∧
      ∀ a, a < j → ∑ c, B a c * y c = 0 := by
  classical
  set S := B.submatrix (Subtype.val : {c : Fin n // c < j} → Fin n)
      (Subtype.val : {c : Fin n // c < j} → Fin n) with hS
  have hdet : IsUnit S.det := isUnit_iff_ne_zero.mpr (det_block_ne B hB j)
  obtain ⟨w, hw⟩ : ∃ w : {c : Fin n // c < j} → ℂ, S *ᵥ w = fun p => -B p.1 j :=
    ⟨S⁻¹ *ᵥ fun p => -B p.1 j, by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]⟩
  refine ⟨fun c => if h : c < j then w ⟨c, h⟩ else if c = j then 1 else 0, by simp, ?_, ?_⟩
  · intro c hc
    simp [not_lt.mpr hc.le, hc.ne']
  · intro a ha
    rw [← Fintype.sum_subtype_add_sum_subtype (fun c => c < j)]
    have h1 : ∑ c : {c : Fin n // c < j}, B a c.1 *
        (if h : c.1 < j then w ⟨c.1, h⟩ else if c.1 = j then 1 else 0) = -B a j := by
      have := congrFun hw ⟨a, ha⟩
      simp only [Matrix.mulVec, dotProduct, hS, Matrix.submatrix_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [dif_pos c.2]
    have h2 : ∑ c : {c : Fin n // ¬ c < j}, B a c.1 *
        (if h : c.1 < j then w ⟨c.1, h⟩ else if c.1 = j then 1 else 0) = B a j := by
      rw [Finset.sum_eq_single (⟨j, lt_irrefl j⟩ : {c : Fin n // ¬ c < j})]
      · simp
      · intro c _ hc
        have : c.1 ≠ j := fun h => hc (Subtype.ext h)
        rw [dif_neg c.2, if_neg this, mul_zero]
      · simp
    rw [h1, h2]
    ring

lemma exists_diag {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hH : B.IsHermitian)
    (hB : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor B i ≠ 0) :
    ∃ (F : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ), F.BlockTriangular id ∧ F.det = 1 ∧
      (∀ i, μ i ≠ 0) ∧ Fᴴ * B * F = diagonal μ := by
  choose y hy1 hy0 hyB using exists_col B hB
  let F : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c j => y j c
  have hFt : F.BlockTriangular id := fun c j h => hy0 j c h
  have hFd : F.det = 1 := by
    rw [Matrix.det_of_upperTriangular hFt]
    exact Finset.prod_eq_one fun i _ => hy1 i
  have hup : ∀ i j, i < j → (Fᴴ * B * F) i j = 0 := by
    intro i j hij
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    rcases lt_or_ge i a with h | h
    · have : F a i = 0 := hy0 i a h
      rw [Matrix.conjTranspose_apply, this, star_zero, zero_mul]
    · have : (B * F) a j = 0 := by
        rw [Matrix.mul_apply]
        exact hyB j a (lt_of_le_of_lt h hij)
      rw [this, mul_zero]
  have hherm : (Fᴴ * B * F)ᴴ = Fᴴ * B * F := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hH.eq, Matrix.mul_assoc]
  have hD : Fᴴ * B * F = diagonal fun i => (Fᴴ * B * F) i i := by
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · rw [hup i j h, Matrix.diagonal_apply_ne _ h.ne]
    · subst h; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h.ne', ← hherm, Matrix.conjTranspose_apply, hup j i h,
        star_zero]
  have hBd : B.det ≠ 0 := hB (Fin.last n)
  refine ⟨F, _, hFt, hFd, ?_, hD⟩
  have : (diagonal fun i => (Fᴴ * B * F) i i).det ≠ 0 := by
    rw [← hD, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hFd]
    simpa using hBd
  rw [Matrix.det_diagonal] at this
  exact fun i => Finset.prod_ne_zero_iff.mp this i (Finset.mem_univ i)

lemma diag_of_isometry {n : ℕ} (d : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ)
    (hd : d.BlockTriangular id) (hμ : ∀ i, μ i ≠ 0)
    (h : dᴴ * diagonal μ * d = diagonal μ) :
    ∃ l : Fin n → ℂ, d = diagonal l ∧ ∀ i, ‖l i‖ = 1 := by
  have hμd : (diagonal μ).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hμ i
  have hdet : (dᴴ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, h0, zero_mul, zero_mul] at this
    exact hμd this.symm
  have hu : IsUnit (dᴴ).det := isUnit_iff_ne_zero.mpr hdet
  have hlow : (dᴴ).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have : d j i = 0 := hd (show i < j from hij)
    rw [Matrix.conjTranspose_apply, this, star_zero]
  haveI := Matrix.invertibleOfIsUnitDet _ hu
  have hlow' := Matrix.blockTriangular_inv_of_blockTriangular hlow
  have h2 : diagonal μ * d = (dᴴ)⁻¹ * diagonal μ := by
    conv_rhs => rw [← h]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have hdiag : d = diagonal fun i => d i i := by
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · have h3 := congrFun (congrFun h2 i) j
      have h4 : (dᴴ)⁻¹ i j = 0 := hlow' (show OrderDual.toDual j < OrderDual.toDual i from hij)
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, h4, zero_mul] at h3
      rw [Matrix.diagonal_apply_ne _ hij.ne]
      exact (mul_eq_zero.mp h3).resolve_left (hμ i)
    · subst hij; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij.ne']
      exact hd hij
  refine ⟨_, hdiag, fun i => ?_⟩
  rw [hdiag, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal] at h
  have h5 := congrFun (congrFun h i) i
  simp only [Matrix.diagonal_apply_eq, Pi.star_apply] at h5
  have h6 := congrArg norm h5
  rw [norm_mul, norm_mul, norm_star] at h6
  have h7 : ‖μ i‖ ≠ 0 := norm_ne_zero_iff.mpr (hμ i)
  have h8 : ‖d i i‖ * ‖d i i‖ = 1 := by
    apply mul_right_cancel₀ h7
    linarith
  have h9 := norm_nonneg (d i i)
  nlinarith

lemma bounded_pow {n : ℕ} (g P : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ) (hP : P.det ≠ 0)
    (hl : ∀ i, ‖l i‖ = 1) (h : g * P = P * diagonal l) :
    ∃ R : ℝ, ∀ (k : ℕ) (i j : Fin n), ‖(g ^ k) i j‖ ≤ R := by
  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.2 hP)
  have hPinv' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.2 hP)
  have hg : g = P * diagonal l * P⁻¹ := by
    calc g = g * P * P⁻¹ := by rw [Matrix.mul_assoc, hPinv, Matrix.mul_one]
      _ = P * diagonal l * P⁻¹ := by rw [h]
  have hk : ∀ k : ℕ, g ^ k = P * diagonal (l ^ k) * P⁻¹ := by
    intro k
    induction k with
    | zero => simp [hPinv]
    | succ k ih =>
      have hd : diagonal (l ^ k * l) = diagonal (l ^ k) * diagonal l := (Matrix.diagonal_mul_diagonal _ _).symm
      rw [pow_succ, ih, hg, pow_succ, hd]
      calc P * diagonal (l ^ k) * P⁻¹ * (P * diagonal l * P⁻¹)
          = P * diagonal (l ^ k) * (P⁻¹ * P) * diagonal l * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = P * (diagonal (l ^ k) * diagonal l) * P⁻¹ := by rw [hPinv', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  refine ⟨∑ i, ∑ j, ∑ a, ‖P i a‖ * ‖P⁻¹ a j‖, fun k i j => ?_⟩
  rw [hk, Matrix.mul_apply]
  have hterm : ∀ a, ‖(P * diagonal (l ^ k)) i a * P⁻¹ a j‖ = ‖P i a‖ * ‖P⁻¹ a j‖ := fun a => by
    rw [Matrix.mul_diagonal, norm_mul, norm_mul, Pi.pow_apply, norm_pow, hl, one_pow, mul_one]
  calc ‖∑ a, (P * diagonal (l ^ k)) i a * P⁻¹ a j‖ ≤ ∑ a, ‖(P * diagonal (l ^ k)) i a * P⁻¹ a j‖ := norm_sum_le _ _
    _ = ∑ a, ‖P i a‖ * ‖P⁻¹ a j‖ := Finset.sum_congr rfl fun a _ => hterm a
    _ ≤ ∑ j', ∑ a, ‖P i a‖ * ‖P⁻¹ a j'‖ :=
        Finset.single_le_sum (f := fun j' => ∑ a, ‖P i a‖ * ‖P⁻¹ a j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ∑ a, ‖P i' a‖ * ‖P⁻¹ a j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ∑ a, ‖P i' a‖ * ‖P⁻¹ a j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem bounded_pow_of_triangular_isometry {n : ℕ} (g x b A : Matrix (Fin n) (Fin n) ℂ)
    (hx : Matrix.det x ≠ (0 : ℂ)) (hb : Matrix.BlockTriangular b id) (hA : Matrix.IsHermitian A)
    (hm : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor A i ≠ (0 : ℂ)) (hg : g * x = x * b)
    (hiso : Matrix.transpose b * A * Matrix.map b (⇑(starRingEnd ℂ) : ℂ → ℂ) = A) :
    ∃ R : ℝ, ∀ (k : ℕ) (i j : Fin n), ‖(g ^ k) i j‖ ≤ R := by
  have hm' : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor Aᵀ i ≠ 0 := by
    intro i
    have := hm i
    unfold ReciprocityTheory.ChartRestriction.G.FD.lminor at this ⊢
    rwa [← Matrix.transpose_submatrix, Matrix.det_transpose]
  have hiso' : bᴴ * Aᵀ * b = Aᵀ := by
    have := congrArg Matrix.transpose hiso
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.mul_assoc] at this
    exact this
  obtain ⟨F, μ, hFt, hFd, hμ, hD⟩ := exists_diag Aᵀ hA.transpose hm'
  have hu : IsUnit F.det := by rw [hFd]; exact isUnit_one
  haveI := Matrix.invertibleOfIsUnitDet _ hu
  have hFd' : F * (F⁻¹ * b * F) = b * F := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  obtain ⟨l, hl, hl1⟩ := diag_of_isometry (F⁻¹ * b * F) μ
    (((Matrix.blockTriangular_inv_of_blockTriangular hFt).mul hb).mul hFt) hμ (by
      calc (F⁻¹ * b * F)ᴴ * diagonal μ * (F⁻¹ * b * F)
          = (F * (F⁻¹ * b * F))ᴴ * Aᵀ * (F * (F⁻¹ * b * F)) := by
            rw [← hD, Matrix.conjTranspose_mul F]
            simp only [Matrix.mul_assoc]
        _ = Fᴴ * (bᴴ * Aᵀ * b) * F := by
            rw [hFd', Matrix.conjTranspose_mul]
            simp only [Matrix.mul_assoc]
        _ = diagonal μ := by rw [hiso', hD])
  refine bounded_pow g (x * F) l ?_ hl1 ?_
  · rw [Matrix.det_mul, hFd, mul_one]; exact hx
  · rw [← hl, Matrix.mul_assoc x, hFd', ← Matrix.mul_assoc, hg, Matrix.mul_assoc]

end GlobalTheory.TriangularIsometryBoundedPowers
