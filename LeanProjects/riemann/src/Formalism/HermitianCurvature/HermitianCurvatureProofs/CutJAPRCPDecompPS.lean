import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompDefs

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

section ps

variable {TT : ℝ}

lemma gg_eval (ζ : ℂ) : gg TT ζ = MvPolynomial.eval ![ζ, conj ζ, sig TT ζ]
    (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)) := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.gg
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.mul_conj]
  push_cast
  ring

lemma ps_congr {f g : ℂ → ℂ} (hf : PS TT f) (h : ∀ ζ, TT < Complex.normSq ζ → f ζ = g ζ) : PS TT g := by
  obtain ⟨m, p, hp⟩ := hf
  exact ⟨m, p, fun ζ hζ => by rw [← h ζ hζ]; exact hp ζ hζ⟩

lemma ps_const (c : ℂ) : PS TT (fun _ => c) := ⟨0, MvPolynomial.C c, fun ζ _ => by simp⟩

lemma ps_id : PS TT (fun ζ => ζ) := ⟨0, MvPolynomial.X 0, fun ζ _ => by simp⟩

lemma ps_conj : PS TT (fun ζ => conj ζ) := ⟨0, MvPolynomial.X 1, fun ζ _ => by simp⟩

lemma ps_sig : PS TT (fun ζ => sig TT ζ) := ⟨0, MvPolynomial.X 2, fun ζ _ => by simp⟩

lemma ps_add {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ + g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨n, q, hq⟩ := hg
  refine ⟨m + n, (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)) ^ n * p + (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)) ^ m * q, fun ζ hζ => ?_⟩
  rw [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_pow, ← gg_eval, ← hp ζ hζ, ← hq ζ hζ]
  ring

lemma ps_mul {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ * g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨n, q, hq⟩ := hg
  refine ⟨m + n, p * q, fun ζ hζ => ?_⟩
  rw [MvPolynomial.eval_mul, ← hp ζ hζ, ← hq ζ hζ]
  ring

lemma sig_sq {ζ : ℂ} (hζ : TT < Complex.normSq ζ) : sig TT ζ * sig TT ζ = gg TT ζ := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.gg Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.sig
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]

lemma sig_ne {ζ : ℂ} (hζ : TT < Complex.normSq ζ) : sig TT ζ ≠ 0 := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.sig
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by linarith))

lemma ps_sigInv : PS TT (fun ζ => (sig TT ζ)⁻¹) := by
  refine ⟨1, MvPolynomial.X 2, fun ζ hζ => ?_⟩
  rw [pow_one, ← sig_sq hζ, mul_assoc, mul_inv_cancel₀ (sig_ne hζ), mul_one]
  simp

end ps

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
