import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvolutionAdjoinNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_involution_adjoin_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E), ∃ σ : Algebra.adjoin E {(nrm d).val} →+* Algebra.adjoin E {(nrm d).val}, (∀ x, ((σ x : Algebra.adjoin E {(nrm d).val}) : Matrix (Fin n) (Fin n) E) = sg d x) ∧ ∀ x, σ (σ x) = x := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.SgRing.exists_sgRing | exact GlobalTheory.CompanionTheory.TorusCh.SgRing.exists_sgRing | (intros; apply GlobalTheory.CompanionTheory.TorusCh.SgRing.exists_sgRing <;> assumption)
