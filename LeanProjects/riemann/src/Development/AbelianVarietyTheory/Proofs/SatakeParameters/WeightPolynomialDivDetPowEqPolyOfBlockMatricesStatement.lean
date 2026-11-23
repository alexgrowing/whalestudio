import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightPolynomialDivDetPowEqPolyOfBlockMatrices
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightPolynomial_div_detPow_eq_poly_of_blockMatrices : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (c : D.what₂.Tau → ℤ), (∀ τ r, (ν τ r : ℤ) ≤ c τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∃ R : MvPolynomial (GL3Theta.FrV D n) ℂ, ∀ f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (f τ).det ≠ 0) → GL3Theta.evFr D R (zT X D pos f) = (∏ τ, if IsOddPos (pos.symm τ).2 then (f τ).det ^ (-(c τ)) else 1) * GL3Theta.evFr D Q f := by
  first | exact @GlobalTheory.TwV.DelA.twPoly_main | exact GlobalTheory.TwV.DelA.twPoly_main | (intros; apply GlobalTheory.TwV.DelA.twPoly_main <;> assumption)
