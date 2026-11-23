import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.WittReflect

open Matrix

variable {E : Type} [Field E]

theorem cT_add' (s : E →+* E) {m p : Type} (M N : Matrix m p E) :
    Formalism.UG.cT s (M + N) = Formalism.UG.cT s M + Formalism.UG.cT s N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_sub' (s : E →+* E) {m p : Type} (M N : Matrix m p E) :
    Formalism.UG.cT s (M - N) = Formalism.UG.cT s M - Formalism.UG.cT s N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_smul' (s : E →+* E) (c : E) {m p : Type} (M : Matrix m p E) :
    Formalism.UG.cT s (c • M) = s c • Formalism.UG.cT s M := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_cT' (s : E →+* E) (hs : ∀ e, s (s e) = e) {m p : Type} (M : Matrix m p E) :
    Formalism.UG.cT s (Formalism.UG.cT s M) = M := by
  ext i j; simp [Formalism.UG.cT, hs]

theorem fin_one_matrix_eq_smul_one (A : Matrix (Fin 1) (Fin 1) E) : A = A 0 0 • 1 := by
  ext i j; fin_cases i; fin_cases j; simp

end GlobalTheory.WittReflect

open GlobalTheory.WittReflect in

theorem GlobalTheory.WittReflect.exists_unitary_map_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ x₀ x : Matrix (Fin n) (Fin 1) E, Formalism.UG.cT (σ : E →+* E) x₀ * J * x₀ = 0 →
        Formalism.UG.cT (σ : E →+* E) x * J * x = 0 → Formalism.UG.cT (σ : E →+* E) x₀ * J * x ≠ 0 →
          ∃ γ ∈ Formalism.UG.UJ (σ : E →+* E) J, ∃ c : E, c ≠ 0 ∧ (γ : Matrix (Fin n) (Fin n) E) * x₀ = c • x := by
  intro F E _ _ _ _ _ σ hcm n J hJ x₀ x h0 hx hne
  have hσσ : ∀ e : E, (σ : E →+* E) ((σ : E →+* E) e) = e := fun e => by
    simpa using GlobalTheory.SiegelSet.sigma_sigma hcm e
  set s : E →+* E := (σ : E →+* E) with hsdef
  have hJT : Formalism.UG.cT s J = J := by
    ext i j; simpa [Formalism.UG.cT, hsdef] using hJ.1 i j
  set A := Formalism.UG.cT s x₀ * J * x with hA
  set a := A 0 0 with ha
  have hA1 : A = a • 1 := fin_one_matrix_eq_smul_one A
  have ha0 : a ≠ 0 := by
    intro h; apply hne; rw [hA1, h, zero_smul]
  have hB : Formalism.UG.cT s x * J * x₀ = s a • 1 := by
    have : Formalism.UG.cT s A = Formalism.UG.cT s x * J * x₀ := by
      rw [hA, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hJT, cT_cT' s hσσ]; simp only [Matrix.mul_assoc]
    rw [← this, hA1, cT_smul', Formalism.UG.cT_one]
  set w := x₀ - a⁻¹ • x with hw
  have hcw : Formalism.UG.cT s w = Formalism.UG.cT s x₀ - s a⁻¹ • Formalism.UG.cT s x := by
    rw [hw, cT_sub', cT_smul']
  have hwx : Formalism.UG.cT s w * J * x₀ = -1 := by
    rw [hcw, Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, h0, hB, smul_smul,
      ← map_mul, inv_mul_cancel₀ ha0, map_one, one_smul, zero_sub]
  have hww : Formalism.UG.cT s w * J * w = (-2 : E) • 1 := by
    have e1 : Formalism.UG.cT s w * J * w = Formalism.UG.cT s w * J * x₀ - a⁻¹ • (Formalism.UG.cT s w * J * x) := by
      rw [hw, Matrix.mul_sub, Matrix.mul_smul]
    have e2 : Formalism.UG.cT s w * J * x = A := by
      rw [hcw, Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, hx, smul_zero, sub_zero]
    rw [e1, e2, hwx, hA1, smul_smul, inv_mul_cancel₀ ha0, one_smul, neg_smul, two_smul]
    abel
  set P := w * Formalism.UG.cT s w * J with hP
  have hPP : P * P = (-2 : E) • P := by
    calc P * P = w * (Formalism.UG.cT s w * J * w) * Formalism.UG.cT s w * J := by simp only [hP, Matrix.mul_assoc]
    _ = (-2 : E) • P := by rw [hww]; simp [hP, Matrix.mul_assoc]
  have hγγ : (1 + P) * (1 + P) = 1 := by
    rw [add_mul, mul_add, mul_add, hPP, one_mul, mul_one, one_mul, neg_smul, two_smul]
    abel
  have hcP : Formalism.UG.cT s P = J * w * Formalism.UG.cT s w := by
    rw [hP, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hJT, cT_cT' s hσσ]; simp only [Matrix.mul_assoc]
  have hU : Formalism.UG.cT s (1 + P) * J * (1 + P) = J := by
    have h1 : Formalism.UG.cT s (1 + P) * J = J * (1 + P) := by
      rw [cT_add', Formalism.UG.cT_one, hcP, add_mul, one_mul, mul_add, mul_one, hP]
      simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_assoc, hγγ, mul_one]
  let γ : GL (Fin n) E := ⟨1 + P, 1 + P, hγγ, hγγ⟩
  refine ⟨γ, hU, a⁻¹, inv_ne_zero ha0, ?_⟩
  show (1 + P) * x₀ = a⁻¹ • x
  have e3 : P * x₀ = w * (Formalism.UG.cT s w * J * x₀) := by simp only [hP, Matrix.mul_assoc]
  rw [Matrix.add_mul, Matrix.one_mul, e3, hwx, Matrix.mul_neg, Matrix.mul_one, hw]
  abel
