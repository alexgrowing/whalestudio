import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.MemIntOEOfIsIntegral

noncomputable section

open Matrix

namespace PI.UnitaryApproxFinWork

variable {n : Type} [Fintype n] [DecidableEq n] {A : Type} [CommRing A] (ρ : A →+* A)

theorem cT_add (M N : Matrix n n A) : PI.UnitaryApproxDefs.cT ρ (M + N) = PI.UnitaryApproxDefs.cT ρ M + PI.UnitaryApproxDefs.cT ρ N := by
  ext i j
  simp [PI.UnitaryApproxDefs.cT]

theorem cT_sub (M N : Matrix n n A) : PI.UnitaryApproxDefs.cT ρ (M - N) = PI.UnitaryApproxDefs.cT ρ M - PI.UnitaryApproxDefs.cT ρ N := by
  ext i j
  simp [PI.UnitaryApproxDefs.cT]

theorem cayley_unitary (J X : Matrix n n A) (hX : PI.UnitaryApproxDefs.cT ρ X * J + J * X = 0)
    (hQ : IsUnit (1 + X).det) :
    PI.UnitaryApproxDefs.cT ρ ((1 - X) * (1 + X)⁻¹) * J * ((1 - X) * (1 + X)⁻¹) = J := by
  have hXJ : PI.UnitaryApproxDefs.cT ρ X * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
  have hcP : PI.UnitaryApproxDefs.cT ρ (1 - X) * J = J * (1 + X) := by
    rw [cT_sub ρ, PI.UnitaryApproxDefs.cT_one, sub_mul, one_mul, hXJ, sub_neg_eq_add, mul_add, mul_one]
  have hcQ : PI.UnitaryApproxDefs.cT ρ (1 + X) * J = J * (1 - X) := by
    rw [cT_add ρ, PI.UnitaryApproxDefs.cT_one, add_mul, one_mul, hXJ, mul_sub, mul_one, sub_eq_add_neg]
  have hinvQ : PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 + X) = 1 := by
    rw [← PI.UnitaryApproxDefs.cT_mul, Matrix.mul_nonsing_inv _ hQ, PI.UnitaryApproxDefs.cT_one]
  have hcomm : (1 + X) * (1 - X) = (1 - X) * (1 + X) := by noncomm_ring
  rw [PI.UnitaryApproxDefs.cT_mul]
  calc PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 - X) * J * ((1 - X) * (1 + X)⁻¹)
      = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * (PI.UnitaryApproxDefs.cT ρ (1 - X) * J) * (1 - X) * (1 + X)⁻¹ := by simp only [mul_assoc]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * J * ((1 + X) * (1 - X)) * (1 + X)⁻¹ := by rw [hcP]; simp only [mul_assoc]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * J * (1 - X) * ((1 + X) * (1 + X)⁻¹) := by rw [hcomm]; simp only [mul_assoc]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * (J * (1 - X)) := by rw [Matrix.mul_nonsing_inv _ hQ, mul_one, mul_assoc]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * (PI.UnitaryApproxDefs.cT ρ (1 + X) * J) := by rw [hcQ]
    _ = J := by rw [← mul_assoc, hinvQ, one_mul]

theorem cayley_mem_UJ (J X : Matrix n n A) (hJd : IsUnit J.det) (hX : PI.UnitaryApproxDefs.cT ρ X * J + J * X = 0)
    (hQ : IsUnit (1 + X).det) :
    ∃ γ ∈ PI.UnitaryApproxDefs.UJ ρ J, (γ : Matrix n n A) = (1 - X) * (1 + X)⁻¹ := by
  have hU := cayley_unitary ρ J X hX hQ
  have hdet := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have h2 : J.det * ((PI.UnitaryApproxDefs.cT ρ ((1 - X) * (1 + X)⁻¹)).det * ((1 - X) * (1 + X)⁻¹).det) = J.det * 1 := by
    rw [mul_one]
    calc J.det * ((PI.UnitaryApproxDefs.cT ρ ((1 - X) * (1 + X)⁻¹)).det * ((1 - X) * (1 + X)⁻¹).det)
        = (PI.UnitaryApproxDefs.cT ρ ((1 - X) * (1 + X)⁻¹)).det * J.det * ((1 - X) * (1 + X)⁻¹).det := by ring
      _ = J.det := hdet
  have h3 := hJd.mul_left_cancel h2
  have hu : IsUnit ((1 - X) * (1 + X)⁻¹).det := isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact h3⟩
  exact ⟨Matrix.nonsingInvUnit _ hu, hU, rfl⟩

theorem lie_of_unitary (J g : Matrix n n A) (hg : PI.UnitaryApproxDefs.cT ρ g * J * g = J) (hP : IsUnit (1 + g).det) :
    PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹) = 0 := by
  have hL : PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 + g) = 1 := by
    rw [← PI.UnitaryApproxDefs.cT_mul, Matrix.mul_nonsing_inv _ hP, PI.UnitaryApproxDefs.cT_one]
  have hLinv : PI.UnitaryApproxDefs.cT ρ (1 + g) * PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ = 1 := by
    rw [← PI.UnitaryApproxDefs.cT_mul, Matrix.nonsing_inv_mul _ hP, PI.UnitaryApproxDefs.cT_one]
  have hR : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
  have e1 : (1 - PI.UnitaryApproxDefs.cT ρ g) * J * (1 + g) + (1 + PI.UnitaryApproxDefs.cT ρ g) * J * (1 - g) =
      J + J - (PI.UnitaryApproxDefs.cT ρ g * J * g + PI.UnitaryApproxDefs.cT ρ g * J * g) := by noncomm_ring
  have key : PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)) * (1 + g) = 0 := by
    rw [PI.UnitaryApproxDefs.cT_mul]
    calc PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 - g) * J + J * ((1 - g) * (1 + g)⁻¹)) * (1 + g)
        = (PI.UnitaryApproxDefs.cT ρ (1 + g) * PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹) * PI.UnitaryApproxDefs.cT ρ (1 - g) * J * (1 + g) +
            PI.UnitaryApproxDefs.cT ρ (1 + g) * J * (1 - g) * ((1 + g)⁻¹ * (1 + g)) := by
          simp only [mul_add, add_mul, mul_assoc]
          abel
      _ = PI.UnitaryApproxDefs.cT ρ (1 - g) * J * (1 + g) + PI.UnitaryApproxDefs.cT ρ (1 + g) * J * (1 - g) := by
          rw [hLinv, Matrix.nonsing_inv_mul _ hP, one_mul, mul_one]
      _ = 0 := by
          rw [cT_sub ρ, cT_add ρ, PI.UnitaryApproxDefs.cT_one, e1, hg, sub_self]
  calc PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)
      = PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)) *
          ((1 + g) * (1 + g)⁻¹) := by rw [hL, hR, one_mul, mul_one]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * (PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)) *
          (1 + g)) * (1 + g)⁻¹ := by simp only [mul_assoc]
    _ = 0 := by rw [key, mul_zero, zero_mul]

end PI.UnitaryApproxFinWork

end
