import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LambdaInvolutionNeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambda_involution_neg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (e : Matrix (Fin n) (Fin n) E), e * e = e → ∀ t : GA E n, t ∈ adCent d → t.val * rm e = rm e * t.val → t.val * rm (sg d e) = rm (sg d e) * t.val → lam (sg d e) t = - lam e t := by
  first | exact @GlobalTheory.CompanionTheory.TorusAdj.lam_sg | exact GlobalTheory.CompanionTheory.TorusAdj.lam_sg | (intros; apply GlobalTheory.CompanionTheory.TorusAdj.lam_sg <;> assumption)
