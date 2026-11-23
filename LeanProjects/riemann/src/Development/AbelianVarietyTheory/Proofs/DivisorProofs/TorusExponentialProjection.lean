import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

noncomputable section

namespace GlobalTheory.TorFin.TorusExp

variable {n : ℕ}

theorem dot_swap {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (u v : Fin n → ℂ) :
    (star u ᵥ* J) ⬝ᵥ v = star ((star v ᵥ* J) ⬝ᵥ u) := by
  rw [← dotProduct_mulVec, star_dotProduct, star_mulVec, hJ]

theorem exp_smul_idem {p : Matrix (Fin n) (Fin n) ℂ} (hp : p * p = p) (a : ℂ) :
    NormedSpace.exp (a • p) = 1 + (Complex.exp a - 1) • p := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let f : ℂ × ℂ →+* Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun st => st.1 • p + st.2 • (1 - p)
      map_one' := by simp
      map_mul' := fun s t => by
        simp only [Prod.fst_mul, Prod.snd_mul, add_mul, mul_add, smul_mul_smul_comm, mul_sub, sub_mul, hp,
          mul_one, one_mul, sub_self, smul_zero, add_zero, zero_add, sub_sub_cancel, sub_zero]
      map_zero' := by simp
      map_add' := fun s t => by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel }
  have hf : Continuous f := by
    show Continuous fun st : ℂ × ℂ => st.1 • p + st.2 • (1 - p)
    fun_prop
  have h1 : f (a, 0) = a • p := by simp [f]
  have h2 := NormedSpace.map_exp f hf (a, 0)
  rw [h1] at h2
  refine Eq.trans h2.symm ?_
  have e1 : (NormedSpace.exp ((a, 0) : ℂ × ℂ)).1 = Complex.exp a := by rw [Prod.fst_exp, Complex.exp_eq_exp_ℂ]
  have e2 : (NormedSpace.exp ((a, 0) : ℂ × ℂ)).2 = 1 := by rw [Prod.snd_exp]; exact NormedSpace.exp_zero
  show (NormedSpace.exp ((a, 0) : ℂ × ℂ)).1 • p + (NormedSpace.exp ((a, 0) : ℂ × ℂ)).2 • (1 - p) = _
  rw [e1, e2, one_smul, sub_smul, one_smul]
  abel

theorem exp_torus (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (hJ : Jᴴ = J) (x y : Fin n → ℂ)
    (hx : (star x ᵥ* J) ⬝ᵥ x = 0) (hy : (star y ᵥ* J) ⬝ᵥ y = 0) (hxy : (star x ᵥ* J) ⬝ᵥ y = 1) (ζ : ℂ) :
    IsSkew J (ζ • projL J x y - star ζ • projL J y x) ∧
      NormedSpace.exp (ζ • projL J x y - star ζ • projL J y x) = torMat J x y (Complex.exp ζ) := by
  have hyx : (star y ᵥ* J) ⬝ᵥ x = 1 := by rw [dot_swap hJ, hxy, star_one]
  have pp : projL J x y * projL J x y = projL J x y := by
    simp only [projL, vecMulVec_mul_vecMulVec, hyx, one_smul]
  have qq : projL J y x * projL J y x = projL J y x := by
    simp only [projL, vecMulVec_mul_vecMulVec, hxy, one_smul]
  have pq : projL J x y * projL J y x = 0 := by
    simp only [projL, vecMulVec_mul_vecMulVec, hy, zero_smul]
    ext i j; simp [vecMulVec]
  have qp : projL J y x * projL J x y = 0 := by
    simp only [projL, vecMulVec_mul_vecMulVec, hx, zero_smul]
    ext i j; simp [vecMulVec]
  have hs : ∀ u v : Fin n → ℂ, (projL J u v)ᴴ * J = J * projL J v u := by
    intro u v
    simp only [projL, conjTranspose_vecMulVec, vecMulVec_mul, mul_vecMulVec, star_vecMul, hJ, star_star]
  refine ⟨?_, ?_⟩
  · unfold IsSkew
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_smul, star_star, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.smul_mul, hs, hs, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul]
    abel
  · rw [sub_eq_add_neg, ← neg_smul, Matrix.exp_add_of_commute, exp_smul_idem pp, exp_smul_idem qq]
    · have he : (star (Complex.exp ζ))⁻¹ = Complex.exp (-star ζ) := by
        change (starRingEnd ℂ (Complex.exp ζ))⁻¹ = Complex.exp (-(starRingEnd ℂ ζ))
        rw [← Complex.exp_conj, Complex.exp_neg]
      rw [torMat, he, add_mul, mul_add, mul_add, mul_one, one_mul, smul_mul_smul_comm, pq, smul_zero, add_zero]
      simp only [mul_one]
      abel
    · show Commute _ _
      simp only [Commute, SemiconjBy, smul_mul_smul_comm, pq, qp, smul_zero]

end GlobalTheory.TorFin.TorusExp
