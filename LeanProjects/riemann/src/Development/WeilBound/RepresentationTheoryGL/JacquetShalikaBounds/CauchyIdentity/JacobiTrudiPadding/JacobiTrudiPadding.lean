import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT

open Finset Matrix

namespace PositivityTheory.RgJS

namespace JacobiTrudiPadding

theorem hZ_zero {m : ℕ} (α : Fin m → ℂ) : hZ 0 α = 1 := by
  simp [hZ, hN, Finset.Nat.antidiagonalTuple_zero_right]

theorem hZ_neg {m : ℕ} (α : Fin m → ℂ) {z : ℤ} (hz : z < 0) : hZ z α = 0 := by
  simp [hZ, hz]

theorem det_unitri {m d : ℕ} (α : Fin m → ℂ) : (Matrix.of fun i j : Fin d => hZ ((i : ℤ) - j) α).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [hZ_zero]
  · intro i j hij
    simp only [Matrix.of_apply]
    apply hZ_neg
    have : (i : ℕ) < j := hij
    omega

theorem jt_pad_add (m' d : ℕ) (α : Fin (m' + d) → ℂ) (l : Fin m' → ℕ) :
    jt α (padN (m' + d) l) = jt α l := by
  unfold jt
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  rw [← Matrix.fromBlocks_toBlocks (Matrix.submatrix _ finSumFinEquiv finSumFinEquiv)]
  rw [show Matrix.toBlocks₁₂ (Matrix.submatrix _ finSumFinEquiv finSumFinEquiv) = 0 from ?_]
  · rw [Matrix.det_fromBlocks_zero₁₂]
    have h11 : Matrix.toBlocks₁₁ ((of fun (i j : Fin (m' + d)) => hZ (↑(padN (m' + d) l j) - ↑↑j + ↑↑i) α).submatrix
        finSumFinEquiv finSumFinEquiv) = of fun (i j : Fin m') => hZ (↑(l j) - ↑↑j + ↑↑i) α := by
      ext i j
      simp [Matrix.toBlocks₁₁, padN]
    have h22 : Matrix.toBlocks₂₂ ((of fun (i j : Fin (m' + d)) => hZ (↑(padN (m' + d) l j) - ↑↑j + ↑↑i) α).submatrix
        finSumFinEquiv finSumFinEquiv) = of fun (i j : Fin d) => hZ ((i : ℤ) - j) α := by
      ext i j
      simp [Matrix.toBlocks₂₂, padN]
      congr 1
      ring
    rw [h11, h22, det_unitri, mul_one]
  · ext i j
    simp [Matrix.toBlocks₁₂, padN]
    apply hZ_neg
    have := i.isLt
    omega

end JacobiTrudiPadding

theorem jacobi_trudi_padding : JTPad := by
  intro m m' hm α l
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact JacobiTrudiPadding.jt_pad_add m' d α l

end PositivityTheory.RgJS
