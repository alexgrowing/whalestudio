import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CentralLetter

variable {n : ℕ}

theorem exp_smul_one (c : ℂ) :
    NormedSpace.exp (c • (1 : Matrix (Fin n) (Fin n) ℂ)) = Complex.exp c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, Complex.exp_eq_exp_ℂ]

theorem inG_imag (ε : Fin n → Bool) (s : ℝ) :
    inG ε (((s : ℂ) * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold inG
  simp [Matrix.conjTranspose_smul]

theorem Rd_central (ε : Fin n → Bool) (m : ℤ) (G : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hG : ∀ z : ℂ, ‖z‖ = 1 → ∀ x : Matrix (Fin n) (Fin n) ℂ, inUJ ε x → G (z • x) = z ^ m * G x)
    (s : ℝ) (x : Matrix (Fin n) (Fin n) ℂ) (hx : inUJ ε x) :
    Rd (((s : ℂ) * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) G x = (m : ℂ) * (s * Complex.I) * G x := by
  unfold Rd
  have h1 : (fun t : ℝ => G (x * NormedSpace.exp ((t : ℂ) • (((s : ℂ) * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)))))
      = fun t : ℝ => Complex.exp ((t : ℂ) * ((m : ℂ) * (s * Complex.I))) * G x := by
    funext t
    rw [smul_smul, exp_smul_one, Matrix.mul_smul, Matrix.mul_one, hG _ _ x hx, ← Complex.exp_int_mul]
    · congr 2; ring
    · rw [← mul_assoc, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  rw [h1]
  have h2 : HasDerivAt (fun t : ℂ => Complex.exp (t * ((m : ℂ) * (s * Complex.I))) * G x)
      ((m : ℂ) * (s * Complex.I) * G x) ((0 : ℝ) : ℂ) := by
    have := (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const ((m : ℂ) * (s * Complex.I))).cexp).mul_const (G x)
    simpa using this
  exact h2.comp_ofReal.deriv

theorem cpart1_add_real (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    cpart1 ε (Z + (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = cpart1 ε Z := by
  unfold cpart1
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Jm_mul_self, Complex.star_def, Complex.conj_ofReal]
  congr 1
  abel

theorem cpart2_add_real (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    cpart2 ε (Z + (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      cpart2 ε Z + ((((-r : ℝ)) : ℂ) * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold cpart2
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Jm_mul_self, Complex.star_def, Complex.conj_ofReal,
    add_add_add_comm, smul_add, ← add_smul, smul_smul]
  congr 2
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

theorem main : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (G : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε G → (∀ z : ℂ, ‖z‖ = 1 → ∀ x : Matrix (Fin n) (Fin n) ℂ, inUJ ε x → G (z • x) = z ^ m * G x) → ∀ (a b : Fin n) (x : Matrix (Fin n) (Fin n) ℂ), inUJ ε x → Eab ε a b G x = Ec ε (E0 a b) G x + (if a = b then (m : ℂ) / n else 0) * G x := by
  intro n _ ε m G hs hG a b x hx
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : ℂ) = (if a = b then (n : ℂ)⁻¹ else 0) :=
    ⟨if a = b then (n : ℝ)⁻¹ else 0, by split_ifs <;> simp⟩
  have e : (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) = E0 a b + (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hr, E0, sub_add_cancel]
  have hm : (if a = b then (m : ℂ) / n else 0) = m * r := by
    rw [hr]; split_ifs <;> simp [div_eq_mul_inv]
  unfold Eab
  rw [e, hm]
  unfold Ec
  rw [cpart1_add_real, cpart2_add_real,
    (right_derivative_linear n ε G G _ _ 0 0 x hs hs (complex_parts_mem_lie_algebra_holds n ε (E0 a b)).2.1 (inG_imag ε (-r)) hx).1,
    Rd_central ε m G hG (-r) x hx]
  push_cast
  linear_combination (-(m : ℂ) * r * G x) * Complex.I_sq

end GlobalTheory.CentralLetter

end
