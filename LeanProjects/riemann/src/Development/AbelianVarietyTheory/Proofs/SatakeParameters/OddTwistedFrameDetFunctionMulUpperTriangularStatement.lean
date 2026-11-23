import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OddTwistedFrameDetFunctionMulUpperTriangular
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SgRevNeZero
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oddTwistedFrameDetFunction_mul_upper_triangular : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (c : D.what₂.Tau → ℤ), (∀ τ r, (ν τ r : ℤ) ≤ c τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∀ (x β : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, (x τ).det ≠ 0) → IsBor β → twF X D pos c Q (fun τ => x τ * β τ) = (∏ τ, ∏ r, β τ r r ^ (if IsOddPos (pos.symm τ).2 then (c τ - (ν τ (Fin.rev r) : ℤ)).toNat else ν τ r)) * twF X D pos c Q x := by
  first | exact @GlobalTheory.TwV.DelA.twF_mul_bor | exact GlobalTheory.TwV.DelA.twF_mul_bor | (intros; apply GlobalTheory.TwV.DelA.twF_mul_bor <;> assumption)
