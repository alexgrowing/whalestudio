import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdeal
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SemiCharImg

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : D7}

def gM {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  γ.map (TaylorLogMetric.embT D τ)

theorem embT_star' (τ : D.what₂.Tau) (x : D.host.E) :
    TaylorLogMetric.embT D τ (letI := D.host.cmStar; star x) = star (TaylorLogMetric.embT D τ x) := by
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.emb_conj]
  rfl

theorem gM_conjTranspose {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (gM γ τ)ᴴ = gM (letI := D.host.cmStar; star γ) τ := by
  letI := D.host.cmStar
  ext i j
  simp only [gM, conjTranspose_apply, map_apply, star_apply]
  rw [embT_star']

theorem gM_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : gM (A * B) τ = gM A τ * gM B τ := by
  simp [gM, Matrix.map_mul]

theorem gM_one {n : ℕ} (τ : D.what₂.Tau) : gM (1 : Matrix (Fin n) (Fin n) D.host.E) τ = 1 := by
  simp [gM, Matrix.map_one]

theorem gM_unit {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (h : (letI := D.host.cmStar; star γ * γ) = 1)
    (τ : D.what₂.Tau) : (gM γ τ)ᴴ * gM γ τ = 1 := by
  rw [gM_conjTranspose, ← gM_mul, h, gM_one]

theorem gM_unit' {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (h : (letI := D.host.cmStar; γ * star γ) = 1)
    (τ : D.what₂.Tau) : gM γ τ * (gM γ τ)ᴴ = 1 := by
  rw [gM_conjTranspose, ← gM_mul, h, gM_one]

variable {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)

def phiL (h1 : (letI := D.host.cmStar; star γ * γ) = 1) (h2 : (letI := D.host.cmStar; γ * star γ) = 1)
    (h1' : (letI := D.host.cmStar; star γ' * γ') = 1) (h2' : (letI := D.host.cmStar; γ' * star γ') = 1) :
    TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N' where
  toFun z := fun τ => (gM γ' τ * Matrix.of (z τ) * (gM γ τ)ᴴ : Matrix _ _ ℂ)
  invFun z := fun τ => (Matrix.conjTranspose (γ'.map (TaylorLogMetric.embT D τ)) * (Matrix.of (z τ)) * γ.map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ)
  map_add' x y := by
    funext τ
    show gM γ' τ * (Matrix.of (x τ) + Matrix.of (y τ)) * (gM γ τ)ᴴ = _
    rw [Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c x := by
    funext τ
    show gM γ' τ * (c • Matrix.of (x τ)) * (gM γ τ)ᴴ = c • (gM γ' τ * Matrix.of (x τ) * (gM γ τ)ᴴ)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  left_inv z := by
    funext τ
    show (gM γ' τ)ᴴ * (gM γ' τ * Matrix.of (z τ) * (gM γ τ)ᴴ) * gM γ τ = Matrix.of (z τ)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, gM_unit γ h1, Matrix.mul_one, ← Matrix.mul_assoc, gM_unit γ' h1',
      Matrix.one_mul]
  right_inv z := by
    funext τ
    show gM γ' τ * ((gM γ' τ)ᴴ * Matrix.of (z τ) * gM γ τ) * (gM γ τ)ᴴ = Matrix.of (z τ)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, gM_unit' γ h2, Matrix.mul_one, ← Matrix.mul_assoc, gM_unit' γ' h2',
      Matrix.one_mul]

theorem sum_trace {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℂ) :
    ∑ i, ∑ j, X i j * (starRingEnd ℂ) (Y i j) = Matrix.trace (X * Yᴴ) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem trace_unit {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (hP : Pᴴ * P = 1)
    (hQ : Q * Qᴴ = 1) (Z W : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.trace (P * Z * Q * (P * W * Q)ᴴ) = Matrix.trace (Z * Wᴴ) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc Matrix.trace (P * Z * Q * (Qᴴ * (Wᴴ * Pᴴ))) = Matrix.trace (P * (Z * Wᴴ * Pᴴ)) := by
        rw [show P * Z * Q * (Qᴴ * (Wᴴ * Pᴴ)) = P * Z * (Q * Qᴴ) * (Wᴴ * Pᴴ) by simp only [Matrix.mul_assoc], hQ]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Matrix.trace (Z * Wᴴ * Pᴴ * P) := by rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = Matrix.trace (Z * Wᴴ) := by rw [Matrix.mul_assoc, hP, Matrix.mul_one]

theorem phiL_isom (h1 h2 h1' h2') (A : ℝ) :
    IsIsom (Ker.formV A D.what₂.Tau N N') (Ker.formV A D.what₂.Tau N N')
      ((phiL γ γ' h1 h2 h1' h2' : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') := by
  intro x y
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e := sum_trace (gM γ' τ * Matrix.of (x τ) * (gM γ τ)ᴴ) (gM γ' τ * Matrix.of (y τ) * (gM γ τ)ᴴ)
  have e2 := sum_trace (Matrix.of (x τ)) (Matrix.of (y τ))
  rw [trace_unit _ _ (gM_unit γ' h1' τ) (by rw [Matrix.conjTranspose_conjTranspose]; exact gM_unit γ h1 τ)] at e
  exact e.trans e2.symm

end Formalism.L2.PairingIndexBounds.Eq
