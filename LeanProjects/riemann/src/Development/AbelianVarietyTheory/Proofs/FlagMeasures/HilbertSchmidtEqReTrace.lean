import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm hs Jm_mul_self Jm_conjTranspose)

namespace GlobalTheory.LeviIso

theorem trace_compress {n m : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin m) ℂ)
    (y : Matrix (Fin m) (Fin m) ℂ) (hC : Cᴴ * C = 1) (hD : D * C = C * y) :
    (Dᴴ * D * (C * Cᴴ)).trace = (yᴴ * y).trace := by
  have hcore : Cᴴ * (Dᴴ * D * C) = yᴴ * y :=
    calc Cᴴ * (Dᴴ * D * C) = (D * C)ᴴ * (D * C) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (C * y)ᴴ * (C * y) := by rw [hD]
      _ = yᴴ * (Cᴴ * C) * y := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = yᴴ * y := by rw [hC, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, hcore]

private theorem hs_eq_re_trace_conjTranspose_mul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : hs X = (trace (Xᴴ * X)).re := by
  unfold hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem hs_lev_sub_one : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ →
    ∀ (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g : Matrix (Fin n₀) (Fin n₀) ℂ),
    Formalism.REAL.hs (lev ε B B₀ x g - 1) =
      ∑ i, (Formalism.REAL.hs (x i - 1) + Formalism.REAL.hs ((x i)⁻¹ - 1)) + Formalism.REAL.hs (g - 1) := by
  intro n n₀ a j ε ε₀ B B₀ h x g
  have hJ : ∀ i, (Jm ε * B i)ᴴ * (Jm ε * B i) = 1 := fun i => by
    rw [Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (Jm ε),
      Jm_mul_self, Matrix.one_mul, h.1 i]
  have hsplit : (1 : Matrix (Fin n) (Fin n) ℂ) =
      ∑ i, B i * (B i)ᴴ + ∑ i, (Jm ε * B i) * (Jm ε * B i)ᴴ + B₀ * B₀ᴴ := by
    rw [← h.2.2.2.2.2.2]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_mul, Jm_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hsub : ∀ {m : ℕ} (C : Matrix (Fin n) (Fin m) ℂ) (y : Matrix (Fin m) (Fin m) ℂ),
      lev ε B B₀ x g * C = C * y → (lev ε B B₀ x g - 1) * C = C * (y - 1) := by
    intro m C y hy
    rw [Matrix.sub_mul, hy, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  have hconj : ∀ {m : ℕ} (Y : Matrix (Fin m) (Fin m) ℂ), hs Yᴴ = hs Y := by
    intro m Y
    rw [hs_eq_re_trace_conjTranspose_mul, hs_eq_re_trace_conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  set M := lev ε B B₀ x g - 1 with hM
  have eB : ∀ i, (Mᴴ * M * (B i * (B i)ᴴ)).trace = ((x i - 1)ᴴ * (x i - 1)).trace := fun i =>
    trace_compress M (B i) _ (h.1 i) (hsub _ _ (h.lev_mul_B x g i))
  have eJ : ∀ i, (Mᴴ * M * ((Jm ε * B i) * (Jm ε * B i)ᴴ)).trace =
      (((x i)⁻¹ᴴ - 1)ᴴ * ((x i)⁻¹ᴴ - 1)).trace := fun i =>
    trace_compress M (Jm ε * B i) _ (hJ i) (hsub _ _ (h.lev_mul_JB x g i))
  have e0 : (Mᴴ * M * (B₀ * B₀ᴴ)).trace = ((g - 1)ᴴ * (g - 1)).trace :=
    trace_compress M B₀ _ h.2.2.2.2.1 (hsub _ _ (h.lev_mul_B₀ x g))
  rw [hs_eq_re_trace_conjTranspose_mul, ← Matrix.mul_one (Mᴴ * M), hsplit]
  simp only [Matrix.mul_add, Matrix.mul_sum, Matrix.trace_add, Matrix.trace_sum, Complex.add_re,
    Complex.re_sum, eB, eJ, e0, Finset.sum_add_distrib]
  have hinv : ∀ i, (x i)⁻¹ᴴ - 1 = ((x i)⁻¹ - 1)ᴴ := fun i => by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  simp only [hinv, ← hs_eq_re_trace_conjTranspose_mul, hconj]

end GlobalTheory.LeviIso
