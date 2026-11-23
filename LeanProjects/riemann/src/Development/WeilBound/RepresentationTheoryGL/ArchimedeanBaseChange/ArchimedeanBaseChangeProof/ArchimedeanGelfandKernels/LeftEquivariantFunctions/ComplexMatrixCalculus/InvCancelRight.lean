import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.FrameZeroApply

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ} {lam : Fin n → ℤ}

local notation "𝟙W" => (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)
local notation "𝟙Λ" => (1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ)

theorem cj_smul_one (hu : IsUnit (sqQ lam)) (c : ℂ) : cjL lam (c • (1 : Matrix (Ix n lam) (Ix n lam) ℂ)) = c • 1 := by
  rw [map_smul, cj_one hu]

theorem herm_conj {x H : Mat n} (hH : H.IsHermitian) : (x * H * xᴴ).IsHermitian := by
  exact Matrix.isHermitian_mul_mul_conjTranspose x hH

theorem herm_conj' {x H : Mat n} (hH : H.IsHermitian) : (xᴴ * H * x).IsHermitian := by
  exact Matrix.isHermitian_conjTranspose_mul_mul x hH

theorem car_f (hu : IsUnit (sqQ lam)) (hB : Car) (hP : CfPair) (H H' : Mat n) (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) : lefε n lam H * lefι n lam H' + lefι n lam H' * lefε n lam H = (H * H').trace • 1 := by
  rw [lefε_apply, lefι_apply, cj_mul hu, cj_mul hu, ← map_add, ← mul_kronecker_mul, ← mul_kronecker_mul, mul_one,
    ← add_kronecker, add_comm (creL n (cf n H) * annL n (cf n H')), hB n (cf n H) (cf n H')]
  have e : cf n H' ⬝ᵥ cf n H = (H * H').trace := by
    rw [← hP n H H' hH hH', dotProduct]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  rw [e, smul_kronecker, one_kronecker_one, cj_smul_one hu]

theorem inv_cancel_left' {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ * x = 1 :=
  Matrix.nonsing_inv_mul x (isUnit_iff_ne_zero.mpr hx)

theorem inv_cancel_right' {x : Mat n} (hx : x ∈ GLs n) : x * x⁻¹ = 1 :=
  Matrix.mul_nonsing_inv x (isUnit_iff_ne_zero.mpr hx)

theorem frι_f (hu : IsUnit (sqQ lam)) (hC : GamCre) (hM : MtLaws) (x : Mat n) (hx : x ∈ GLs n) (H : Mat n)
    (hH : H.IsHermitian) : lefFr n lam x * lefι n lam H = lefι n lam (x * H * xᴴ) * lefFr n lam x := by
  rw [lefFr_apply, lefι_apply, lefι_apply, cj_mul hu, cj_mul hu, frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul,
    mul_one, one_mul]
  congr 2
  rw [(hC n _ 0 (cf n (x * H * xᴴ))).2, transpose_transpose, (hM n).2.2.1 x⁻¹ _ (herm_conj hH)]
  have h1 := inv_cancel_left' hx
  have h2 : xᴴ * x⁻¹ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have key : x⁻¹ * (x * H * xᴴ) * x⁻¹ᴴ = H := by
    calc x⁻¹ * (x * H * xᴴ) * x⁻¹ᴴ = (x⁻¹ * x) * H * (xᴴ * x⁻¹ᴴ) := by simp only [mul_assoc]
      _ = H := by rw [h1, h2, one_mul, mul_one]
  rw [key]

theorem frε_f (hu : IsUnit (sqQ lam)) (hC : GamCre) (hM : MtLaws) (x : Mat n) (hx : x ∈ GLs n) (H : Mat n)
    (hH : H.IsHermitian) : lefε n lam H * lefFr n lam x = lefFr n lam x * lefε n lam (xᴴ * H * x) := by
  rw [lefFr_apply, lefε_apply, lefε_apply, cj_mul hu, cj_mul hu, frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul,
    mul_one, one_mul]
  congr 2
  rw [(hC n _ (cf n (xᴴ * H * x)) 0).1, (hM n).2.2.2 x⁻¹ _ (herm_conj' hH)]
  have h1 := inv_cancel_right' hx
  have h2 : x⁻¹ᴴ * xᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have key : x⁻¹ᴴ * (xᴴ * H * x) * x⁻¹ = H := by
    calc x⁻¹ᴴ * (xᴴ * H * x) * x⁻¹ = (x⁻¹ᴴ * xᴴ) * H * (x * x⁻¹) := by simp only [mul_assoc]
      _ = H := by rw [h1, h2, one_mul, mul_one]
  rw [key]

end PositivityTheory.RgBcC
