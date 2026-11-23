import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SgRevNeZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OddTwistedFrameDetFunctionMulUpperTriangularStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OddTwistedFrameDetFunctionMulDetPowPolynomialStatement
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem twPoly_main : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (c : D.what₂.Tau → ℤ), (∀ τ r, (ν τ r : ℤ) ≤ c τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∃ R : MvPolynomial (GL3Theta.FrV D n) ℂ, ∀ f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (f τ).det ≠ 0) → GL3Theta.evFr D R (zT X D pos f) = (∏ τ, if IsOddPos (pos.symm τ).2 then (f τ).det ^ (-(c τ)) else 1) * GL3Theta.evFr D Q f := by
  intro p _ X D pos n ν c hc Q hQ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨Q, fun f _ => ?_⟩
    have h0 : zT X D pos f = f := funext fun τ => Subsingleton.elim _ _
    rw [h0]
    simp [Matrix.det_fin_zero]
  · obtain ⟨K, P, hP⟩ := GlobalTheory.T.oddTwistedFrameDetFunction_mul_det_pow_polynomial X D pos hn ν c hc Q hQ
    obtain ⟨R, hR⟩ := Formalism.L2.KerInert.SharpPolyP.sp_main
      (fun τ r => if IsOddPos (pos.symm τ).2 then (c τ - (ν τ (Fin.rev r) : ℤ)).toNat else ν τ r)
      (twF X D pos c Q) (fun x β hx hβ => GlobalTheory.T.oddTwistedFrameDetFunction_mul_upper_triangular X D pos ν c hc Q hQ x β hx hβ) _ K P rfl hP
    refine ⟨R, fun f hf => ?_⟩
    have hz : ∀ τ, (zT X D pos f τ).det ≠ 0 := by
      intro τ
      rw [det_zT]
      split_ifs
      · exact mul_ne_zero (sgRev_ne_zero n) (inv_ne_zero (hf τ))
      · exact hf τ
    have h1 := hR (zT X D pos f) hz
    rw [show GL3Theta.evFr D R (zT X D pos f) = MvPolynomial.eval (Formalism.L2.KerInert.SharpPolyP.pt (zT X D pos f)) R from rfl,
      ← h1, twF, zT_zT X D pos f hf]

end GlobalTheory.TwV.DelA
