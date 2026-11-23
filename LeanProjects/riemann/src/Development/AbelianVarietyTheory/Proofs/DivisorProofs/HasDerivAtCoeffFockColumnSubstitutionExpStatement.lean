import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtCoeffFockColumnSubstitutionExp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColDerApply
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_coeff_fockColumnSubstitution_exp : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (R : GlobalTheory.MinorFrame.Pol ι d a)
    (m : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
    HasDerivAt (fun h : ℝ => MvPolynomial.coeff m (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp ((h : ℂ) • S))) R))
      (MvPolynomial.coeff m (GlobalTheory.ColLie.colDer τ S R)) 0 := by
  first | exact @GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp | exact GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp | (intros; apply GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp <;> assumption)
