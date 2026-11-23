import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

def twF {n : ℕ} (c : D.what₂.Tau → ℤ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (y : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos y τ).det ^ (-(c τ)) else 1) * GL3Theta.evFr D Q (zT X D pos y)

theorem zT_zT {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, (f τ).det ≠ 0) :
    zT X D pos (zT X D pos f) = f := by
  funext τ
  unfold zT
  split_ifs with h
  · have hu : IsUnit (f τ).det := isUnit_iff_ne_zero.2 (hf τ)
    rw [show ((f τ)⁻¹).transpose.submatrix id Fin.rev = ((f τ)⁻¹).transpose.submatrix (Equiv.refl (Fin n)) (Fin.revPerm : Equiv.Perm (Fin n)) from rfl,
      Matrix.inv_submatrix_equiv, ← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hu]
    ext i j
    simp
  · rfl

theorem det_zT {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) :
    (zT X D pos f τ).det = if IsOddPos (pos.symm τ).2 then sgRev n * ((f τ).det)⁻¹ else (f τ).det := by
  unfold zT
  split_ifs with h
  · rw [show ((f τ)⁻¹).transpose.submatrix id Fin.rev = ((f τ)⁻¹).transpose.submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) from rfl,
      Matrix.det_permute', Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    simp [sgRev]
  · rfl

theorem sgRev_ne_zero (n : ℕ) : sgRev n ≠ 0 := by
  unfold sgRev
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> simp [h]

end GlobalTheory.TwV.DelA
