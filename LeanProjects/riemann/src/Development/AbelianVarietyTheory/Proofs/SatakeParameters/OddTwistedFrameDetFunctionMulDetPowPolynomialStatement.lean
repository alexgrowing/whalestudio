import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OddTwistedFrameDetFunctionMulDetPowPolynomial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SgRevNeZero
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oddTwistedFrameDetFunction_mul_det_pow_polynomial : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}, 0 < n → ∀ (ν : D.what₂.Tau → Fin n → ℕ) (c : D.what₂.Tau → ℤ), (∀ τ r, (ν τ r : ℤ) ≤ c τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∃ (K : D.what₂.Tau → ℕ) (P : MvPolynomial (GL3Theta.FrV D n) ℂ), ∀ x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (x τ).det ≠ 0) → MvPolynomial.eval (fun k : GL3Theta.FrV D n => x k.1 k.2.1 k.2.2) P = twF X D pos c Q x * ∏ τ, (x τ).det ^ K τ := by
  first | exact @GlobalTheory.TwV.DelA.twF_mul_det_poly | exact GlobalTheory.TwV.DelA.twF_mul_det_poly | (intros; apply GlobalTheory.TwV.DelA.twF_mul_det_poly <;> assumption)
