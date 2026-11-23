import ReciprocityTheory.SemistableReduction.SemiDegCC

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField Matrix
open scoped nonZeroDivisors

theorem hermForm_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (u w : Fin r → K) : S.h (a • u) w = S.c a * S.h u w := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermForm_eq_mulVec {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (u w : Fin r → K) : S.h u w = ∑ b, (∑ a, S.c (u a) * S.G a b) * w b := by
  simp only [HermForm.h, Finset.sum_mul]
  rw [Finset.sum_comm]

def rowMat {K : Type} [Field K] {k : ℕ} (z : Fin k → Fin k → K) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i a => z i a

theorem det_rowMat {K : Type} [Field K] {k : ℕ} (z : Fin k → Fin k → K)
    (htri : ∀ j i : Fin k, i < j → z j i = 0) (hdiag : ∀ j, z j j = 1) : (rowMat z).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [rowMat, hdiag]
  · intro i j hji
    exact htri i j hji

theorem hermForm_rows {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    (z : Fin k → Fin k → K) (i : Fin k) (v : Fin k → K) :
    S.h (z i) v = (((rowMat z).map S.c * S.G) *ᵥ v) i := by
  rw [hermForm_eq_mulVec]
  simp [mulVec, dotProduct, Matrix.mul_apply, rowMat]

theorem smul_mem_of_split {K : Type} [Field K] [NumberField K] {k : ℕ}
    {X : Submodule (𝓞 K) (Fin k → K)} {C : Fin k → Submodule (𝓞 K) K} {z : Fin k → Fin k → K}
    (hin : ∀ t : Fin k → K, (∀ i, t i ∈ C i) → ∑ i, t i • z i ∈ X) (j : Fin k) {a : K}
    (ha : a ∈ C j) : a • z j ∈ X := by
  classical
  have h := hin (Pi.single j a) (fun i => by
    by_cases hij : i = j
    · subst hij; simpa using ha
    · simp [hij])
  simpa [Pi.single_apply] using h

theorem integral_of_mem_one {K : Type} [Field K] [NumberField K] {x : K}
    (hx : x ∈ (1 : Submodule (𝓞 K) K)) : IsIntegralElt x := by
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 hx
  exact ⟨a, ha⟩

theorem split_integral {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    {X : Submodule (𝓞 K) (Fin k → K)} {C : Fin k → Submodule (𝓞 K) K} {z : Fin k → Fin k → K}
    (htri : ∀ j i : Fin k, i < j → z j i = 0) (hdiag : ∀ j, z j j = 1)
    (hin : ∀ t : Fin k → K, (∀ i, t i ∈ C i) → ∑ i, t i • z i ∈ X) (hint : IsIntegralOn S X)
    (s t : Fin k → K) (hs : ∀ i, S.c (s i) ∈ C i) (ht : ∀ i, t i ∈ C i) :
    (∏ i, s i) * S.G.det * (∏ i, t i) ∈ (1 : Submodule (𝓞 K) K) := by
  let M : Matrix (Fin k) (Fin k) K :=
    Matrix.of fun i j => S.h (S.c (s i) • z i) (t j • z j)
  have hM : M = Matrix.diagonal s * (((rowMat z).map S.c * S.G) * (rowMat z)ᵀ) *
      Matrix.diagonal t := by
    ext i j
    simp only [M, Matrix.of_apply, hermForm_smul_smul, S.c_invol, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    rw [hermForm_rows]
    simp [mulVec, dotProduct, Matrix.mul_apply, rowMat]
    ring
  have hdet : M.det = (∏ i, s i) * S.G.det * (∏ i, t i) := by
    have : ((rowMat z).map S.c).det = 1 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_rowMat z htri hdiag, map_one]
    rw [hM]
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
      det_rowMat z htri hdiag, this]
    ring
  have hent : ∀ i j, ∃ m : 𝓞 K, algebraMap (𝓞 K) K m = M i j := fun i j =>
    hint _ (smul_mem_of_split hin i (hs i)) _ (smul_mem_of_split hin j (ht j))
  choose m hm using hent
  have : M = (Matrix.of m).map (algebraMap (𝓞 K) K) := by
    ext i j
    simp [hm]
  rw [← hdet, this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact Submodule.mem_one.2 ⟨_, rfl⟩

theorem split_selfDual {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    {X : Submodule (𝓞 K) (Fin k → K)} {C : Fin k → Submodule (𝓞 K) K} {z : Fin k → Fin k → K}
    (htri : ∀ j i : Fin k, i < j → z j i = 0) (hdiag : ∀ j, z j j = 1)
    (hdec : ∀ x ∈ X, ∃ t : Fin k → K, (∀ i, t i ∈ C i) ∧ x = ∑ i, t i • z i)
    (hsd : IsSelfDual S X) (hG : S.G.det ≠ 0) (u : Fin k → K)
    (hu : ∀ j, ∀ w, S.c w ∈ C j → u j * w ∈ (1 : Submodule (𝓞 K) K)) :
    ∏ j, u j ∈ Submodule.span (𝓞 K) {S.G.det} * ∏ i, C i := by
  classical
  set Q : Matrix (Fin k) (Fin k) K := (rowMat z).map S.c * S.G with hQ
  have hQdet : Q.det = S.G.det := by
    rw [hQ, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      det_rowMat z htri hdiag, map_one, one_mul]
  have hQu : IsUnit Q.det := by rw [hQdet]; exact isUnit_iff_ne_zero.2 hG
  let y : Fin k → Fin k → K := fun j => Q⁻¹ *ᵥ Pi.single j (u j)
  have hQy : ∀ j, Q *ᵥ y j = Pi.single j (u j) := fun j => by
    simp only [y, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQu, Matrix.one_mulVec]
  have hy : ∀ j, y j ∈ X := by
    intro j
    refine hsd.2 _ fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := hdec x hx
    rw [← hermForm_conj]
    have : S.h (∑ i, t i • z i) (y j) = S.c (t j) * u j := by
      rw [hermForm_sum_left]
      simp only [hermForm_smul_left, hermForm_rows, ← hQ, hQy, Pi.single_apply]
      simp
    rw [this]
    refine integral_of_mem_one (mem_one_map S.c ?_)
    rw [mul_comm]
    exact hu j _ (by rw [S.c_invol]; exact ht j)
  choose T hT hTy using fun j => hdec (y j) (hy j)
  let Tm : Matrix (Fin k) (Fin k) K := Matrix.of fun i j => T j i
  have hY1 : (Matrix.of fun a j => y j a) = (rowMat z)ᵀ * Tm := by
    ext a j
    simp only [Matrix.of_apply]
    rw [hTy j]
    simp [Tm, rowMat, Matrix.mul_apply, Finset.sum_apply, mul_comm]
  have hY2 : (Matrix.of fun a j => y j a) = Q⁻¹ * Matrix.diagonal u := by
    ext a j
    simp [y, Matrix.mul_diagonal, mul_comm]
  have hdet : (∏ j, u j) = S.G.det * Tm.det := by
    have h1 := congrArg Matrix.det hY1
    rw [hY2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_rowMat z htri hdiag,
      one_mul, Matrix.det_nonsing_inv, Matrix.det_diagonal, hQdet, Ring.inverse_eq_inv'] at h1
    rw [← h1]
    field_simp
  rw [hdet]
  exact Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _)
    (det_mem_prod_sub C Tm fun i j => hT j i)

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
