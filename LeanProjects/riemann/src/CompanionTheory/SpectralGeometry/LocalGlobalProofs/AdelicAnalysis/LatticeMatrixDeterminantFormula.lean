import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker nonZeroDivisors

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq (InfinitePlace F)]

theorem det_EM_sq {ρ : InfinitePlace F → (F →+* ℝ)} (hT : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) :
    (EM ρ (fun v => b v)).det ^ 2 = (discr F : ℝ) := by
  let B : Module.Basis (InfinitePlace F) ℚ F := b.localizationLocalization ℚ ℤ⁰ F
  have hB : ∀ i, B i = (b i : F) := fun i =>
    Module.Basis.localizationLocalization_apply ℚ ℤ⁰ F b i
  have hd : Algebra.discr ℚ B = (discr F : ℚ) := by
    rw [← NumberField.discr_eq_discr F b]
    exact (Algebra.discr_localizationLocalization ℤ ℤ⁰ F b).trans (by simp)
  have hm : (EM ρ (fun v => b v))ᵀ * EM ρ (fun v => b v) =
      (algebraMap ℚ ℝ).mapMatrix (Algebra.traceMatrix ℚ B) := by
    ext u v
    simp only [Matrix.mul_apply, Matrix.transpose_apply, EM, RingHom.mapMatrix_apply,
      Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply, hB]
    simp_rw [← map_mul]
    rw [sum_rho_eq_trace hT hρ]
    simp
  have h2 : (EM ρ (fun v => b v)).det ^ 2 =
      ((EM ρ (fun v => b v))ᵀ * EM ρ (fun v => b v)).det := by
    rw [Matrix.det_mul, Matrix.det_transpose, sq]
  rw [h2, hm, ← RingHom.map_det, ← Algebra.discr_def, hd]
  simp

theorem abs_det_gM {ρ : InfinitePlace F → (F →+* ℝ)} (hT : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ) :
    |(gM (ι := ι) ρ (fun v => b v) N).det| =
      ((N : ℝ) ^ Module.finrank ℚ F * Real.sqrt |(discr F : ℝ)|) ^ Fintype.card ι := by
  have hfr : Module.finrank ℚ F = Fintype.card (InfinitePlace F) :=
    Module.finrank_eq_card_basis (b.localizationLocalization ℚ ℤ⁰ F)
  have hE : |(EM ρ (fun v => b v)).det| = Real.sqrt |(discr F : ℝ)| := by
    rw [← det_EM_sq hT hρ b, abs_of_nonneg (sq_nonneg (EM ρ (fun v => b v)).det), Real.sqrt_sq_eq_abs]
  rw [gM, Matrix.det_smul, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul,
    Fintype.card_prod, abs_mul, abs_pow, abs_pow, hE, hfr, Nat.abs_cast]
  ring

theorem abs_det_gM_all : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ)), IsTotallyReal F →
    (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∀ (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ),
    |(gM (ι := ι) ρ (fun v => b v) N).det| =
      ((N : ℝ) ^ Module.finrank ℚ F * Real.sqrt |(discr F : ℝ)|) ^ Fintype.card ι :=
  fun _ _ _ _ _ _ _ _ hT hρ b N => abs_det_gM hT hρ b N

end GlobalTheory.CompanionTheory.SW.ThW
