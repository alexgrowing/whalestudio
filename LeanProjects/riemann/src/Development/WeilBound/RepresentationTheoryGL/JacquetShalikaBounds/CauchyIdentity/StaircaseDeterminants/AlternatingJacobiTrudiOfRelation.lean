import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT

noncomputable section

open Finset Matrix

namespace PositivityTheory.RgJS

namespace SkewJacobiTrudiStaircase

variable {m : ℕ}

def eM (α : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i k => (-1 : ℂ) ^ (k.rev : ℕ) * eEx α i (k.rev : ℕ)

def hM (α : Fin m → ℂ) (μ : Fin m → ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun k j => hZ ((μ j : ℤ) - (k.rev : ℕ)) α

theorem factor (hE : ERel) (α : Fin m → ℂ) (μ : Fin m → ℕ) :
    (Matrix.of fun i j => α i ^ μ j) = eM α * hM α μ := by
  ext i j
  rw [Matrix.of_apply, hE m α i (μ j), Matrix.mul_apply]
  simp only [eM, hM, Matrix.of_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun r => (-1 : ℂ) ^ r * eEx α i r * hZ ((μ j : ℤ) - (r : ℤ)) α)]
  exact (Fintype.sum_equiv Fin.revPerm _ _ (fun k => rfl)).symm

theorem hZ_neg (α : Fin m → ℂ) {z : ℤ} (hz : z < 0) : hZ z α = 0 := by
  simp [hZ, hz]

theorem hZ_zero (α : Fin m → ℂ) : hZ 0 α = 1 := by
  simp only [hZ, hN, lt_irrefl, if_false, Int.toNat_zero]
  rw [Nat.antidiagonalTuple_zero_right]
  simp

theorem det_hM_stair (α : Fin m → ℂ) : (hM α (stair m)).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro k _
    simp only [hM, Matrix.of_apply]
    have hk : ((stair m k : ℕ) : ℤ) - ((k.rev : ℕ) : ℤ) = 0 := by
      simp only [stair, Fin.val_rev]
      have := k.isLt
      omega
    rw [hk]
    exact hZ_zero α
  · intro i j hij
    simp only [hM, Matrix.of_apply]
    apply hZ_neg
    have hlt : (i : ℕ) < j := hij
    simp only [stair, Fin.val_rev]
    have := j.isLt
    omega

theorem hM_add_stair (α : Fin m → ℂ) (l : Fin m → ℕ) :
    hM α (l + stair m) = Matrix.of fun i j : Fin m => hZ ((l j : ℤ) - j + i) α := by
  ext k j
  simp only [hM, Matrix.of_apply, Pi.add_apply, stair, Fin.val_rev]
  congr 1
  have hj := j.isLt
  have hk := k.isLt
  push_cast
  omega

end SkewJacobiTrudiStaircase

open SkewJacobiTrudiStaircase in
theorem alternating_jacobi_trudi_of_relation : ERel → AltJT := by
  intro hE m α l
  unfold altN jt
  rw [factor hE α, factor hE α, det_mul, det_mul, det_hM_stair, mul_one, hM_add_stair]

end PositivityTheory.RgJS
