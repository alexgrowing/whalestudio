import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CartanTrace

theorem star_trace_herm {m n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hA : Aᴴ = A) (hB : Bᴴ = B) (x y : Matrix (Fin m) (Fin n) ℂ) :
    star (A * yᴴ * B * x).trace = (A * xᴴ * B * y).trace := by
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA, hB]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

open scoped MatrixOrder in
theorem trace_pos {m n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (x : Matrix (Fin m) (Fin n) ℂ) (hx : x ≠ 0) :
    0 < (A * xᴴ * B * x).trace := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hA.isStrictlyPositive
  obtain ⟨D, hD, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hB.isStrictlyPositive
  have e : (star C * C * xᴴ * (star D * D) * x).trace = ((D * x * Cᴴ)ᴴ * (D * x * Cᴴ)).trace := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e]
  refine lt_of_le_of_ne (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg ?_
  intro h
  have h0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h.symm
  apply hx
  have hC' : IsUnit Cᴴ := hC.star
  have hD' := (Matrix.isUnit_iff_isUnit_det _).1 hD
  have hC'' := (Matrix.isUnit_iff_isUnit_det _).1 hC'
  have : x = D⁻¹ * (D * x * Cᴴ) * Cᴴ⁻¹ := by
    rw [Matrix.mul_assoc D, Matrix.nonsing_inv_mul_cancel_left _ _ hD',
      Matrix.mul_nonsing_inv_cancel_right _ _ hC'']
  rw [this, h0]; simp

variable {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}

theorem adj_mul (h : IsCartanInv G s) : sᴴ * G = G * s := by
  have := congrArg (· * s) h.2.1
  simpa only [Matrix.mul_assoc, h.1, Matrix.mul_one] using this

theorem adj_sq (h : IsCartanInv G s) : sᴴ * sᴴ = 1 := by
  rw [← Matrix.conjTranspose_mul, h.1, Matrix.conjTranspose_one]

theorem herm (h : IsCartanInv G s) : Gᴴ = G := by
  have h1 : sᴴ * Gᴴ = sᴴ * G := by
    rw [← Matrix.conjTranspose_mul, adj_mul h]; exact h.2.2.isHermitian
  have := congrArg (sᴴ * ·) h1
  simpa only [← Matrix.mul_assoc, adj_sq h, Matrix.one_mul] using this

theorem inv_mul_adj (h : IsCartanInv G s) : G⁻¹ * sᴴ = (G * s)⁻¹ := by
  rw [← adj_mul h, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (adj_sq h)]

theorem form_cplxO {m n : ℕ} {GS sS : Matrix (Fin n) (Fin n) ℂ} {GT sT : Matrix (Fin m) (Fin m) ℂ}
    {ξ : ℂ} (hξ : ξ.re = 0) (hS : IsCartanInv GS sS) (hT : IsCartanInv GT sT)
    (x y : Matrix (Fin m) (Fin n) ℂ) :
    (ξ * (GS⁻¹ * (cplxO sS sT y)ᴴ * GT * x).trace).re =
      ξ.im * ((GS * sS)⁻¹ * yᴴ * (GT * sT) * x).trace.re := by
  have e : GS⁻¹ * (cplxO sS sT y)ᴴ * GT * x =
      (-Complex.I) • ((GS * sS)⁻¹ * yᴴ * (GT * sT) * x) := by
    rw [← inv_mul_adj hS, ← adj_mul hT]
    simp only [cplxO, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, Complex.star_def, Complex.conj_I]
  rw [e, Matrix.trace_smul]
  simp [hξ]

theorem cplxO_pos : ∀ (m n : ℕ) (GS sS : Matrix (Fin n) (Fin n) ℂ) (GT sT : Matrix (Fin m) (Fin m) ℂ) (ξ : ℂ), ξ.re = 0 → 0 < ξ.im → IsCartanInv GS sS → IsCartanInv GT sT → (∀ x : Matrix (Fin m) (Fin n) ℂ, (ξ * (GS⁻¹ * xᴴ * GT * x).trace).re = 0) ∧ (∀ x : Matrix (Fin m) (Fin n) ℂ, cplxO sS sT (cplxO sS sT x) = -x) ∧ (∀ x y : Matrix (Fin m) (Fin n) ℂ, (ξ * (GS⁻¹ * (cplxO sS sT y)ᴴ * GT * x).trace).re = (ξ * (GS⁻¹ * (cplxO sS sT x)ᴴ * GT * y).trace).re) ∧ ∀ x : Matrix (Fin m) (Fin n) ℂ, x ≠ 0 → 0 < (ξ * (GS⁻¹ * (cplxO sS sT x)ᴴ * GT * x).trace).re := by
  intro m n GS sS GT sT ξ h0 h1 hS hT
  refine ⟨fun x => ?_, fun x => ?_, fun x y => ?_, fun x hx => ?_⟩
  · have hi : GS⁻¹ᴴ = GS⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, herm hS]
    have := congrArg Complex.im (star_trace_herm hi (herm hT) x x)
    have h2 : (GS⁻¹ * xᴴ * GT * x).trace.im = 0 := by
      rw [Complex.star_def, Complex.conj_im] at this; linarith
    simp [h0, h2]
  · simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hT.1, Matrix.one_mul, Matrix.mul_assoc, hS.1]
    simp
  · rw [form_cplxO h0 hS hT, form_cplxO h0 hS hT,
      ← star_trace_herm hS.2.2.inv.isHermitian hT.2.2.isHermitian x y]
    simp
  · rw [form_cplxO h0 hS hT]
    exact mul_pos h1 (Complex.pos_iff.1 (trace_pos hS.2.2.inv hT.2.2 x hx)).1

end GlobalTheory.CartanTrace
