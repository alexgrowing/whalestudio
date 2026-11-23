import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpinGlRelationsAdjoint
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spin_gl_relations_adjoint : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    Formalism.REAL.GlRel (spinM c) ∧ ∀ a b, (spinM c a b)ᴴ = spinM c b a := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel | exact GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel | (intros; apply GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel <;> assumption)
