import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockColumnSubstitutionExpOfColumnDerivation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColDerApply
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockColumnSubstitution_exp_of_columnDerivation : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι) (c : ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Q),
    (∀ (S : Matrix (Fin a) (Fin a) ℂ) (R : GlobalTheory.MinorFrame.Pol ι d a) (m : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
      HasDerivAt (fun h : ℝ => MvPolynomial.coeff m (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp ((h : ℂ) • S))) R))
        (MvPolynomial.coeff m (GlobalTheory.ColLie.colDer τ S R)) 0) →
    (∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P, q (GlobalTheory.ColLie.colDer τ S P) = ((c : ℂ) * S.trace) • q P) →
    ∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P,
      q (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp S)) P) = ((NormedSpace.exp S).det ^ c) • q P := by
  first | exact @GlobalTheory.ColLie.colSub_exp_of_colDer | exact GlobalTheory.ColLie.colSub_exp_of_colDer | (intros; apply GlobalTheory.ColLie.colSub_exp_of_colDer <;> assumption)
