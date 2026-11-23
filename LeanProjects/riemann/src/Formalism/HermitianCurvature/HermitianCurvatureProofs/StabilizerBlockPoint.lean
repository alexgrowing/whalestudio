import Formalism.HermitianCurvature.StatementG

open Matrix
open Formalism.FourierDecayAlt.G

namespace Formalism.FourierDecayAlt.P.G4

theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  simp [blk, h]

theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]

theorem blk_lc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]

theorem blk_ll {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    blk A b a e (Fin.last n) (Fin.last n) = e := by
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h2]

theorem blk_mul {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b a b' a' : Fin n → ℂ) (e e' : ℂ) :
    blk A b a e * blk A' b' a' e' =
      blk (A * A' + Matrix.vecMulVec b a') (A *ᵥ b' + e' • b) (a ᵥ* A' + e • a') (a ⬝ᵥ b' + e * e') := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  congr 2
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply, dotProduct]

theorem mat_ext {n : ℕ} {M N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h1 : ∀ i j : Fin n, M i.castSucc j.castSucc = N i.castSucc j.castSucc)
    (h2 : ∀ i : Fin n, M i.castSucc (Fin.last n) = N i.castSucc (Fin.last n))
    (h3 : ∀ j : Fin n, M (Fin.last n) j.castSucc = N (Fin.last n) j.castSucc)
    (h4 : M (Fin.last n) (Fin.last n) = N (Fin.last n) (Fin.last n)) : M = N := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact h4
    | cast j => exact h3 j
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact h2 i
    | cast j => exact h1 i j

theorem blk_eta {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    M = blk (Matrix.of fun i j => M i.castSucc j.castSucc) (fun i => M i.castSucc (Fin.last n))
      (fun j => M (Fin.last n) j.castSucc) (M (Fin.last n) (Fin.last n)) :=
  mat_ext (fun i j => by rw [blk_cc]; rfl) (fun i => by rw [blk_cl]) (fun j => by rw [blk_lc])
    (by rw [blk_ll])

theorem blk_inj {n : ℕ} {A A' : Matrix (Fin n) (Fin n) ℂ} {b a b' a' : Fin n → ℂ} {e e' : ℂ} :
    blk A b a e = blk A' b' a' e' ↔ A = A' ∧ b = b' ∧ a = a' ∧ e = e' := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext i j
      have := congrFun (congrFun h i.castSucc) j.castSucc
      simpa only [blk_cc] using this
    · ext i
      have := congrFun (congrFun h i.castSucc) (Fin.last n)
      simpa only [blk_cl] using this
    · ext j
      have := congrFun (congrFun h (Fin.last n)) j.castSucc
      simpa only [blk_lc] using this
    · have := congrFun (congrFun h (Fin.last n)) (Fin.last n)
      simpa only [blk_ll] using this
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

theorem blk_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    (blk A b a e)ᵀ = blk Aᵀ a b e :=
  mat_ext (fun i j => by rw [transpose_apply, blk_cc, blk_cc, transpose_apply])
    (fun i => by rw [transpose_apply, blk_lc, blk_cl])
    (fun j => by rw [transpose_apply, blk_cl, blk_lc])
    (by rw [transpose_apply, blk_ll, blk_ll])

theorem upperUni_blk_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    IsUpperUni (blk A b a e) ↔ IsUpperUni A ∧ a = 0 ∧ e = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_, ?_⟩
    · rw [← blk_cc A b a e]; exact h1 _
    · rw [← blk_cc A b a e]; exact h2 _ _ (Fin.castSucc_lt_castSucc_iff.2 hij)
    · ext j
      rw [← blk_lc A b a e]; exact h2 _ _ (Fin.castSucc_lt_last j)
    · rw [← blk_ll A b a e]; exact h1 _
  · rintro ⟨⟨h1, h2⟩, rfl, rfl⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · induction i using Fin.lastCases with
      | last => rw [blk_ll]
      | cast i => rw [blk_cc]; exact h1 i
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => rw [blk_lc]; rfl
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.le_last _))
        | cast j => rw [blk_cc]; exact h2 _ _ (Fin.castSucc_lt_castSucc_iff.1 hij)

theorem lowerUni_blk_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    IsLowerUni (blk A b a e) ↔ IsLowerUni A ∧ b = 0 ∧ e = 1 := by
  unfold IsLowerUni
  rw [blk_transpose, upperUni_blk_iff]

theorem exists_blk_upper {n : ℕ} {u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hu : IsUpperUni u) :
    ∃ (u' : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ), IsUpperUni u' ∧ u = blk u' b 0 1 := by
  have h := blk_eta u
  rw [h, upperUni_blk_iff] at hu
  obtain ⟨h1, h2, h3⟩ := hu
  refine ⟨_, fun i => u i.castSucc (Fin.last n), h1, ?_⟩
  rw [h2, h3] at h
  exact h

theorem exists_blk_lower {n : ℕ} {l : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hl : IsLowerUni l) :
    ∃ (l' : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ), IsLowerUni l' ∧ l = blk l' 0 a 1 := by
  have h := blk_eta l
  rw [h, lowerUni_blk_iff] at hl
  obtain ⟨h1, h2, h3⟩ := hl
  refine ⟨_, fun j => l (Fin.last n) j.castSucc, h1, ?_⟩
  rw [h2, h3] at h
  exact h

theorem tri_mul_diag {d : ℕ} {p q : Matrix (Fin d) (Fin d) ℂ} (hp : ∀ i j, j < i → p i j = 0)
    (hq : ∀ i j, j < i → q i j = 0) (i : Fin d) : (p * q) i i = p i i * q i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hp _ _ h, zero_mul]
  · rw [hq _ _ h, mul_zero]

theorem tri_mul {d : ℕ} {p q : Matrix (Fin d) (Fin d) ℂ} (hp : ∀ i j, j < i → p i j = 0)
    (hq : ∀ i j, j < i → q i j = 0) (i j : Fin d) (hij : j < i) : (p * q) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k i with h | h
  · rw [hp _ _ h, zero_mul]
  · rw [hq _ _ (lt_of_lt_of_le hij h), mul_zero]

theorem upperUni_one {d : ℕ} : IsUpperUni (1 : Matrix (Fin d) (Fin d) ℂ) :=
  ⟨fun i => Matrix.one_apply_eq i, fun _ _ h => Matrix.one_apply_ne h.ne'⟩

theorem upperUni_mul {d : ℕ} {p q : Matrix (Fin d) (Fin d) ℂ} (hp : IsUpperUni p) (hq : IsUpperUni q) :
    IsUpperUni (p * q) :=
  ⟨fun i => by rw [tri_mul_diag hp.2 hq.2, hp.1, hq.1, mul_one], tri_mul hp.2 hq.2⟩

theorem upperUni_det {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) : u.det = 1 := by
  have h : u.BlockTriangular id := fun i j hij => hu.2 i j hij
  rw [Matrix.det_of_isUpperTriangular h]
  simp [hu.1]

theorem lowerUni_det {d : ℕ} {l : Matrix (Fin d) (Fin d) ℂ} (hl : IsLowerUni l) : l.det = 1 := by
  rw [← Matrix.det_transpose]; exact upperUni_det hl

theorem upper_mul_inv {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) : u * u⁻¹ = 1 :=
  Matrix.mul_nonsing_inv u (by rw [upperUni_det hu]; exact isUnit_one)

theorem upper_inv_mul {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) : u⁻¹ * u = 1 :=
  Matrix.nonsing_inv_mul u (by rw [upperUni_det hu]; exact isUnit_one)

theorem lower_mul_inv {d : ℕ} {l : Matrix (Fin d) (Fin d) ℂ} (hl : IsLowerUni l) : l * l⁻¹ = 1 :=
  Matrix.mul_nonsing_inv l (by rw [lowerUni_det hl]; exact isUnit_one)

theorem lower_inv_mul {d : ℕ} {l : Matrix (Fin d) (Fin d) ℂ} (hl : IsLowerUni l) : l⁻¹ * l = 1 :=
  Matrix.nonsing_inv_mul l (by rw [lowerUni_det hl]; exact isUnit_one)

theorem upperUni_inv {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) : IsUpperUni u⁻¹ := by
  have h : u.BlockTriangular id := fun i j hij => hu.2 i j hij
  have : Invertible u := Matrix.invertibleOfIsUnitDet u (by rw [upperUni_det hu]; exact isUnit_one)
  have h' : (u⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular h
  have h2 : ∀ i j, j < i → u⁻¹ i j = 0 := fun i j hij => h' hij
  refine ⟨fun i => ?_, h2⟩
  have := tri_mul_diag hu.2 h2 i
  rw [upper_mul_inv hu, Matrix.one_apply_eq, hu.1, one_mul] at this
  exact this.symm

theorem lowerUni_inv {d : ℕ} {l : Matrix (Fin d) (Fin d) ℂ} (hl : IsLowerUni l) : IsLowerUni l⁻¹ := by
  unfold IsLowerUni
  rw [Matrix.transpose_nonsing_inv]
  exact upperUni_inv hl

theorem upperUni_upper {d : ℕ} (v : UT d → ℂ) : IsUpperUni (upper v) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp [upper, strictUpper]
  · simp [upper, strictUpper, hij.ne', not_lt.2 hij.le]

theorem upper_coordU {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) : upper (coordU u) = u := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · simp [upper, strictUpper, coordU, h, h.ne]
  · subst h; simp [upper, strictUpper, hu.1]
  · simp [upper, strictUpper, h.ne', not_lt.2 h.le, hu.2 _ _ h]

theorem upper_injective {d : ℕ} {v v' : UT d → ℂ} (h : upper v = upper v') : v = v' := by
  ext ⟨⟨i, j⟩, hij⟩
  have hij' : i < j := hij
  have := congrFun (congrFun h i) j
  simpa [upper, strictUpper, hij', hij'.ne] using this

theorem w_mul_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (wMat d * M) i j = M i.rev j := by
  simp [wMat, Matrix.mul_apply]

theorem mul_w_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (M * wMat d) i j = M i j.rev := by
  have : ∀ k : Fin d, (j = k.rev) = (k = j.rev) := fun k =>
    propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  simp [wMat, Matrix.mul_apply, this]

theorem w_mul_w (d : ℕ) : wMat d * wMat d = 1 := by
  ext i j
  rw [w_mul_apply]
  simp [wMat, Matrix.one_apply, eq_comm]

theorem w_conj_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (wMat d * M * wMat d) i j = M i.rev j.rev := by
  rw [mul_w_apply, w_mul_apply]

theorem w_det_ne (d : ℕ) : (wMat d).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (w_mul_w d)
  simp [Matrix.det_mul, h] at this

theorem lowerUni_conj {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) :
    IsLowerUni (wMat d * u * wMat d) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [transpose_apply, w_conj_apply]; exact hu.1 _
  · rw [transpose_apply, w_conj_apply]; exact hu.2 _ _ (Fin.rev_lt_rev.2 hij)

theorem upperUni_conj {d : ℕ} {l : Matrix (Fin d) (Fin d) ℂ} (hl : IsLowerUni l) :
    IsUpperUni (wMat d * l * wMat d) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [w_conj_apply]; exact hl.1 _
  · rw [w_conj_apply]; exact hl.2 _ _ (Fin.rev_lt_rev.2 hij)

theorem superSum_mul {n : ℕ} {p q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hp : IsUpperUni p)
    (hq : IsUpperUni q) : superSum (p * q) = superSum p + superSum q := by
  simp only [superSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ).ne
  rw [Finset.sum_eq_add i.castSucc i.succ hne]
  · rw [hp.1, hq.1]; ring
  · intro k _ hk
    rcases lt_trichotomy k i.castSucc with h | h | h
    · rw [hp.2 _ _ h]; ring
    · exact absurd h hk.1
    · have : i.succ < k := by
        rcases lt_or_eq_of_le (Fin.castSucc_lt_iff_succ_le.1 h) with h' | h'
        · exact h'
        · exact absurd h'.symm hk.2
      rw [hq.2 _ _ this]; ring
  · simp
  · simp

theorem superSum_one {n : ℕ} : superSum (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 0 := by
  unfold superSum
  refine Finset.sum_eq_zero fun i _ => ?_
  exact Matrix.one_apply_ne (Fin.castSucc_lt_succ).ne

theorem superSum_inv {n : ℕ} {u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hu : IsUpperUni u) :
    superSum u⁻¹ + superSum u = 0 := by
  rw [← superSum_mul (upperUni_inv hu) hu, upper_inv_mul hu, superSum_one]

theorem subSum_conj {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    subSum (wMat (n + 1) * M * wMat (n + 1)) = superSum M := by
  unfold subSum superSum
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [w_conj_apply, Fin.rev_succ, Fin.rev_castSucc, Fin.revPerm_apply, Fin.rev_rev]

theorem superSum_blk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (b a : Fin (m + 1) → ℂ) (e : ℂ) :
    superSum (blk A b a e) = superSum A + b (Fin.last m) := by
  unfold superSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, blk_cc]
  · rw [Fin.succ_last, blk_cl]

theorem subSum_blk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (b a : Fin (m + 1) → ℂ) (e : ℂ) :
    subSum (blk A b a e) = subSum A + a (Fin.last m) := by
  unfold subSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, blk_cc]
  · rw [Fin.succ_last, blk_lc]

theorem stab_core {d : ℕ} {l u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) :
    l * wMat d * u = wMat d ↔ l = wMat d * u⁻¹ * wMat d := by
  constructor
  · intro h
    calc l = l * wMat d * (u * u⁻¹) * wMat d := by
            rw [upper_mul_inv hu, Matrix.mul_one, Matrix.mul_assoc, w_mul_w, Matrix.mul_one]
      _ = (l * wMat d * u) * u⁻¹ * wMat d := by simp only [Matrix.mul_assoc]
      _ = wMat d * u⁻¹ * wMat d := by rw [h]
  · rintro rfl
    calc wMat d * u⁻¹ * wMat d * wMat d * u = wMat d * (u⁻¹ * ((wMat d * wMat d) * u)) := by
            simp only [Matrix.mul_assoc]
      _ = wMat d := by rw [w_mul_w, Matrix.one_mul, upper_inv_mul hu, Matrix.mul_one]

theorem stab_right {d : ℕ} {l k k' : Matrix (Fin d) (Fin d) ℂ} (h1 : l * k = 1)
    (h2 : k * wMat d * k' = wMat d) : k' = wMat d * l * wMat d := by
  calc k' = (wMat d * wMat d) * k' := by rw [w_mul_w, Matrix.one_mul]
    _ = wMat d * (l * k) * wMat d * k' := by rw [h1, Matrix.mul_one]
    _ = wMat d * l * (k * wMat d * k') := by simp only [Matrix.mul_assoc]
    _ = wMat d * l * wMat d := by rw [h2]

theorem stab_smul {d : ℕ} {z : ℂ} (hz : z ≠ 0) (l u : Matrix (Fin d) (Fin d) ℂ) :
    l * (z • wMat d) * u = z • wMat d ↔ l * wMat d * u = wMat d := by
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact (smul_right_injective _ hz).eq_iff

theorem stab_exists {d : ℕ} {l : Matrix (Fin d) (Fin d) ℂ} (hl : IsLowerUni l) :
    l⁻¹ * wMat d * (wMat d * l * wMat d) = wMat d := by
  calc l⁻¹ * wMat d * (wMat d * l * wMat d) = l⁻¹ * ((wMat d * wMat d) * l) * wMat d := by
          simp only [Matrix.mul_assoc]
    _ = wMat d := by rw [w_mul_w, Matrix.one_mul, lower_inv_mul hl, Matrix.one_mul]

theorem block_prod {n : ℕ} (t c : ℂ) (l' u' : Matrix (Fin n) (Fin n) ℂ) (α β : Fin n → ℂ) :
    blk l' 0 α 1 * ptBlock n t c * blk u' β 0 1 =
      blk (l' * (t • wMat n) * u') ((l' * (t • wMat n)) *ᵥ β) (α ᵥ* ((t • wMat n) * u'))
        ((α ᵥ* (t • wMat n)) ⬝ᵥ β + c) := by
  unfold ptBlock
  rw [blk_mul, blk_mul, blk_inj]
  exact ⟨by simp, by simp, by simp [Matrix.vecMul_vecMul], by simp⟩

theorem blk_mul_diag_right {n : ℕ} (A K : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ) :
    blk A 0 a 1 * blk K 0 0 1 = blk (A * K) 0 (a ᵥ* K) 1 := by
  rw [blk_mul, blk_inj]
  exact ⟨by simp, by simp, by simp, by simp⟩

theorem blk_mul_diag_left {n : ℕ} (A K : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) :
    blk K 0 0 1 * blk A b 0 1 = blk (K * A) (K *ᵥ b) 0 1 := by
  rw [blk_mul, blk_inj]
  exact ⟨by simp, by simp, by simp, by simp⟩

theorem char_blk : ∀ {n : ℕ} {k : Matrix (Fin n) (Fin n) ℂ}, IsUpperUni k →
    subSum (blk (wMat n * k⁻¹ * wMat n) 0 0 1) + superSum (blk k 0 0 1) = 0
  | 0, _, _ => by simp [subSum, superSum]
  | m + 1, k, hk => by
    rw [subSum_blk, superSum_blk, subSum_conj]
    simpa using superSum_inv hk

end Formalism.FourierDecayAlt.P.G4

namespace Formalism.FourierDecayAlt.P

open G4

theorem stabilizer_long_point : Formalism.FourierDecayAlt.G.StabLong := by
  intro n z hz l u _ hu
  have h1 : l * ptLong (n + 1) z * u = ptLong (n + 1) z ↔ l = wMat (n + 1) * u⁻¹ * wMat (n + 1) := by
    unfold ptLong
    rw [stab_smul hz, stab_core hu]
  refine ⟨h1, fun h => ?_⟩
  rw [h1.1 h, subSum_conj, superSum_inv hu]

theorem section_at_long_point : Formalism.FourierDecayAlt.G.SectionLong := by
  intro n z hz l u hl hu
  have hk' := upperUni_conj hl
  refine ⟨coordU (wMat (n + 1) * l * wMat (n + 1) * u),
    ⟨l⁻¹, wMat (n + 1) * l * wMat (n + 1), lowerUni_inv hl, hk', ?_, lower_mul_inv hl, ?_⟩, ?_⟩
  · unfold ptLong
    rw [stab_smul hz]
    exact stab_exists hl
  · exact (upper_coordU (upperUni_mul hk' hu)).symm
  · rintro v ⟨k, k', _, _, h3, h4, h5⟩
    unfold ptLong at h3
    rw [stab_smul hz] at h3
    apply upper_injective
    rw [← h5, stab_right h4 h3, upper_coordU (upperUni_mul hk' hu)]

theorem stabilizer_block_point : Formalism.FourierDecayAlt.G.StabBlock := by
  intro n t c ht l u hl hu
  have h1 : l * ptBlock n t c * u = ptBlock n t c ↔
      ∃ k : Matrix (Fin n) (Fin n) ℂ, IsUpperUni k ∧ u = blk k 0 0 1 ∧
        l = blk (wMat n * k⁻¹ * wMat n) 0 0 1 := by
    constructor
    · intro h
      obtain ⟨l', α, hl', rfl⟩ := exists_blk_lower hl
      obtain ⟨u', β, hu', rfl⟩ := exists_blk_upper hu
      rw [block_prod] at h
      unfold ptBlock at h
      rw [blk_inj] at h
      obtain ⟨e1, e2, e3, _⟩ := h
      have hw : (t • wMat n).det ≠ 0 := by
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ ht) (w_det_ne n)
      have hβ : β = 0 := by
        refine Matrix.eq_zero_of_mulVec_eq_zero ?_ e2
        rw [Matrix.det_mul, lowerUni_det hl', one_mul]
        exact hw
      have hα : α = 0 := by
        refine Matrix.eq_zero_of_vecMul_eq_zero ?_ e3
        rw [Matrix.det_mul, upperUni_det hu', mul_one]
        exact hw
      refine ⟨u', hu', by rw [hβ], ?_⟩
      rw [hα, (stab_core hu').1 ((stab_smul ht _ _).1 e1)]
    · rintro ⟨k, hk, rfl, rfl⟩
      rw [block_prod]
      unfold ptBlock
      rw [blk_inj]
      exact ⟨(stab_smul ht _ _).2 ((stab_core hk).2 rfl), by simp, by simp, by simp⟩
  refine ⟨h1, fun h => ?_⟩
  obtain ⟨k, hk, rfl, rfl⟩ := h1.1 h
  exact char_blk hk

theorem section_at_block_point : Formalism.FourierDecayAlt.G.SectionBlock := by
  intro n t c ht l u hl hu
  obtain ⟨l', α, hl', rfl⟩ := exists_blk_lower hl
  obtain ⟨u', β, hu', rfl⟩ := exists_blk_upper hu
  have hk0 := upperUni_conj hl'
  refine ⟨(α ᵥ* l'⁻¹, coordU (wMat n * l' * wMat n * u'), (wMat n * l' * wMat n) *ᵥ β),
    ⟨blk l'⁻¹ 0 0 1, blk (wMat n * l' * wMat n) 0 0 1, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (lowerUni_blk_iff _ _ _ _).2 ⟨lowerUni_inv hl', rfl, rfl⟩
  · exact (upperUni_blk_iff _ _ _ _).2 ⟨hk0, rfl, rfl⟩
  · rw [block_prod]
    unfold ptBlock
    rw [blk_inj]
    exact ⟨(stab_smul ht _ _).2 (stab_exists hl'), by simp, by simp, by simp⟩
  · rw [blk_mul_diag_right, lower_mul_inv hl']
    rfl
  · rw [blk_mul_diag_left]
    dsimp only
    rw [upper_coordU (upperUni_mul hk0 hu')]
  · rintro ⟨a, v, b⟩ ⟨k, k', hk, hk', h3, h4, h5⟩
    obtain ⟨κ, hκ, rfl, rfl⟩ := ((stabilizer_block_point n t c ht k k' hk hk').1).1 h3
    dsimp only at h4 h5
    unfold lowRow at h4
    rw [blk_mul_diag_right, blk_inj] at h4
    rw [blk_mul_diag_left, blk_inj] at h5
    obtain ⟨h41, _, h43, _⟩ := h4
    obtain ⟨h51, h52, _, _⟩ := h5
    have hκ0 : κ = wMat n * l' * wMat n := stab_right h41 ((stab_core hκ).2 rfl)
    have hinv : l'⁻¹ = wMat n * κ⁻¹ * wMat n := Matrix.inv_eq_right_inv h41
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show a = α ᵥ* l'⁻¹
      rw [hinv, h43]
    · show v = coordU (wMat n * l' * wMat n * u')
      apply upper_injective
      rw [upper_coordU (upperUni_mul hk0 hu'), ← h51, hκ0]
    · show b = (wMat n * l' * wMat n) *ᵥ β
      rw [← h52, hκ0]

end Formalism.FourierDecayAlt.P
